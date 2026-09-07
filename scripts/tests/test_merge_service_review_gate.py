#!/usr/bin/env python3
"""Regression tests for the owner merge service's canonical CI/review selection.

MERGE_SERVICE_UNDER_TEST and MERGE_SERVICE_BIN_DIR can select a deployed copy.
Only imports and mocked eligibility reads run; no GitHub or repository writes occur.
"""

from __future__ import annotations

import importlib
import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch


HEAD = "a" * 40
OTHER_HEAD = "b" * 40
NUMBER = 731


class MergeServiceEligibilityTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        repo = Path(__file__).resolve().parents[2]
        service_path = Path(os.environ.get(
            "MERGE_SERVICE_UNDER_TEST",
            repo / "results/telemetry/owner-tools/merge-service-space-cap5.py")).resolve()
        bin_dir = Path(os.environ.get("MERGE_SERVICE_BIN_DIR", repo / "local/bin"))
        sys.path.insert(0, str(bin_dir.resolve()))
        spec = importlib.util.spec_from_file_location("merge_service_under_test", service_path)
        cls.service = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.service)
        cls.canonical = importlib.import_module("pr_merge")
        cls.github = importlib.import_module("gh_common")

    def setUp(self):
        self.pr = {
            "number": NUMBER,
            "draft": False,
            "head": {"sha": HEAD, "ref": "issue-731-eligibility"},
            "base": {"ref": "main"},
            "created_at": "2026-09-07T00:00:00Z",
        }
        self.statuses = {
            context: {"state": "success"}
            for context in self.canonical.CI_CONTEXTS
        }
        self.statuses[self.canonical.REVIEW_CONTEXT] = {"state": "success"}
        self.reviews = [self.review()]

    @staticmethod
    def review(*, head=HEAD, marker_head=None, marker_number=NUMBER,
               verdict="APPROVED", findings="", state="COMMENTED"):
        marker_head = head if marker_head is None else marker_head
        return {
            "commit_id": head,
            "state": state,
            "body": (
                f"<!-- mipstarre-review pr={marker_number} head={marker_head} -->\n"
                f"## Findings\n{findings}\nVERDICT: {verdict}\n"
            ),
        }

    def eligible(self, *, fresh=True):
        def api(path, **_kwargs):
            if path.startswith("pulls?state=open"):
                return [self.pr]
            self.fail(f"unexpected API request: {path}")

        with patch.object(self.github, "api", side_effect=api), \
                patch.object(self.github, "latest_statuses", return_value=self.statuses), \
                patch.object(self.github, "pr_reviews", return_value=self.reviews), \
                patch.object(self.service.subprocess, "run", return_value=
                             subprocess.CompletedProcess([], 0 if fresh else 1)):
            return self.service.eligible_prs(HEAD)

    def test_clean_exact_head_approval_is_eligible(self):
        rows = self.eligible()
        self.assertEqual([row["number"] for row in rows], [NUMBER])
        self.assertEqual(rows[0]["head"], HEAD)
        self.assertTrue(rows[0]["fresh_against_remote"])

    def test_each_required_ci_context_must_exist(self):
        for context in self.canonical.CI_CONTEXTS:
            with self.subTest(context=context):
                saved = self.statuses.pop(context)
                self.assertEqual(self.eligible(), [])
                self.statuses[context] = saved

    def test_each_required_ci_context_must_be_success(self):
        for context in self.canonical.CI_CONTEXTS:
            for state in ("pending", "failure", "error"):
                with self.subTest(context=context, state=state):
                    self.statuses[context] = {"state": state}
                    self.assertEqual(self.eligible(), [])
            self.statuses[context] = {"state": "success"}

    def test_review_summary_must_exist_and_be_success(self):
        self.statuses.pop(self.canonical.REVIEW_CONTEXT)
        self.assertEqual(self.eligible(), [])
        for state in ("pending", "failure", "error"):
            with self.subTest(state=state):
                self.statuses[self.canonical.REVIEW_CONTEXT] = {"state": state}
                self.assertEqual(self.eligible(), [])

    def test_newest_matching_clean_review_replaces_inconsistent_old_review(self):
        self.reviews = [
            self.review(findings="- [ ] F1 (blocker) old unresolved finding"),
            self.review(),
        ]
        self.assertEqual(len(self.eligible()), 1)

    def test_newest_matching_adverse_review_replaces_old_approval(self):
        for verdict in ("CHANGES_REQUESTED", "COMMENTED", "APPROVED"):
            with self.subTest(verdict=verdict):
                self.reviews = [self.review(), self.review(
                    verdict=verdict, findings="- [ ] F1 (blocker) current finding")]
                self.assertEqual(self.eligible(), [])

    def test_unrelated_newer_reviews_do_not_replace_exact_marker_review(self):
        self.reviews = [
            self.review(),
            self.review(head=OTHER_HEAD, verdict="CHANGES_REQUESTED"),
            self.review(marker_number=NUMBER + 1, verdict="CHANGES_REQUESTED"),
        ]
        self.assertEqual(len(self.eligible()), 1)

    def test_wrong_commit_or_marker_never_supplies_review_evidence(self):
        variants = [
            self.review(head=OTHER_HEAD, marker_head=HEAD),
            self.review(marker_head=OTHER_HEAD),
            self.review(marker_number=NUMBER + 1),
            {"commit_id": HEAD, "state": "COMMENTED",
             "body": f"head={HEAD}\nVERDICT: APPROVED"},
        ]
        for review in variants:
            with self.subTest(review=review):
                self.reviews = [review]
                self.assertEqual(self.eligible(), [])

    def test_no_review_is_ineligible(self):
        self.reviews = []
        self.assertEqual(self.eligible(), [])

    def test_verdict_must_be_a_canonical_trailer_line(self):
        for text in ("The previous VERDICT: APPROVED is obsolete.",
                     "VERDICT: CHANGES_REQUESTED\nquoted VERDICT: APPROVED"):
            with self.subTest(text=text):
                row = self.review()
                row["body"] = row["body"].replace("VERDICT: APPROVED", text)
                self.reviews = [row]
                self.assertEqual(self.eligible(), [])

    def test_all_unchecked_task_list_styles_block(self):
        for findings in ("- [ ] F1 (blocker) finding", "* [ ] F1 (blocker) finding",
                         "  * [ ] optional checklist"):
            with self.subTest(findings=findings):
                self.reviews = [self.review(findings=findings)]
                self.assertEqual(self.eligible(), [])

    def test_inline_prose_mentioning_checkbox_syntax_is_not_a_finding(self):
        self.reviews = [self.review(findings="The parser recognizes - [ ] task items.")]
        self.assertEqual(len(self.eligible()), 1)

    def test_commented_review_without_findings_is_eligible(self):
        self.reviews = [self.review(verdict="COMMENTED")]
        self.assertEqual(len(self.eligible()), 1)

    def test_current_head_changes_requested_state_blocks_even_clean_latest_body(self):
        self.reviews = [
            self.review(state="CHANGES_REQUESTED"),
            self.review(),
        ]
        self.assertEqual(self.eligible(), [])

    def test_changes_requested_state_on_other_head_does_not_block(self):
        self.reviews = [
            self.review(head=OTHER_HEAD, state="CHANGES_REQUESTED"),
            self.review(),
        ]
        self.assertEqual(len(self.eligible()), 1)

    def test_stale_eligible_pr_is_retained_as_stale(self):
        rows = self.eligible(fresh=False)
        self.assertEqual(len(rows), 1)
        self.assertFalse(rows[0]["fresh_against_remote"])

    def test_draft_pr_is_ineligible(self):
        self.pr["draft"] = True
        self.assertEqual(self.eligible(), [])


if __name__ == "__main__":
    unittest.main()
