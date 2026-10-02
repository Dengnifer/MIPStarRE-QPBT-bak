#!/usr/bin/env python3
"""Regression tests for comparator challenge drift checking."""

from __future__ import annotations

import hashlib
import importlib.util
import re
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch


REPO_ROOT = Path(__file__).resolve().parents[2]
COMPARATOR = REPO_ROOT / "scripts" / "comparator"
SCRIPT = COMPARATOR / "check_challenge_drift.py"
PR_CI = REPO_ROOT / ".github" / "workflows" / "pr-ci.yml"
CI_SH = REPO_ROOT / "local" / "bin" / "ci.sh"
QPBT_AXIOM_AUDIT = REPO_ROOT / "MIPStarRE" / "QPBT" / "Test" / "AxiomAudit.lean"
README = COMPARATOR / "README.md"
EXTRACTOR = COMPARATOR / "extract_closure.lean"
LDT_EXPECTED = COMPARATOR / "expected" / "Challenge.lean.expected"
PALOMAR_EXPECTED = COMPARATOR / "expected" / "palomar" / "Challenge.lean.expected"
LDT_BASELINE_SHA256 = (
    "3430abaf0e82e3527a8f64719f5da2740f3a84d4169a3391be8af6650179c434"
)
PALOMAR_BASELINE_SHA256 = (
    "74f16feefedf98b442a143836d8a720e39748561ebdd32e8e8041b55b2621bc3"
)
TEMPLATE_BASELINE_SHA256 = {
    "challenge_header.lean.in":
        "5031f9a950a17981dfd41f38950c364f2f7fa575f305d966c511e6544f614fe6",
    "challenge_footer.lean.in":
        "c9d93c31cf4cebc5973fc85b9a79c497f5991dbc1f767abfffefe44246592ff8",
    "challenge_qpbt_header.lean.in":
        "c09e1e2ff263da5c547c0cad2e616d05ec83db6b8e2e8d9e2259ed2d3b060ec9",
    "challenge_qpbt_footer.lean.in":
        "c5660a0d8c8145ded79d6a9490d7dbec269d045f9de3b19b712353a2797853da",
    "challenge_palomar_header.lean.in":
        "a209d7bf1dd1af406ae4d7c8eb0d11f4a4f3cc1c3682c2843f94574905fadf17",
    "challenge_palomar_footer.lean.in":
        "aa55e89fd5fa8c35c01853874ebffccefa6e9b02b7aa0820fad019285f45abd6",
}
ARCHIVED_NATIVE_HARNESS = (
    REPO_ROOT
    / "results/telemetry/native-audits/pr549-01a0a525"
    / "PR549NativeChecks.lean.txt"
)
ARCHIVED_NATIVE_HARNESS_SHA256 = (
    "99f9a14cc19aabc368a0be88420f24953967dfef70c0cf616439b255b7b7898c"
)

# the drift checker imports its sibling `challenge_config`, which a script run
# finds on `sys.path[0]` and a file-location import does not
if str(COMPARATOR) not in sys.path:
    sys.path.insert(0, str(COMPARATOR))

import challenge_config  # noqa: E402

_spec = importlib.util.spec_from_file_location("check_challenge_drift", SCRIPT)
assert _spec is not None and _spec.loader is not None
check_challenge_drift = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(check_challenge_drift)


class ComparatorChallengeDriftTests(unittest.TestCase):
    def test_challenge_templates_are_byte_preserved_fragments(self) -> None:
        configured_parts = {
            part
            for challenge in challenge_config.load_challenges()
            for part in (challenge.header, challenge.footer)
            if part is not None
        }
        expected_parts = {
            f"scripts/comparator/{name}" for name in TEMPLATE_BASELINE_SHA256
        }
        self.assertEqual(configured_parts, expected_parts)
        for name, expected_hash in TEMPLATE_BASELINE_SHA256.items():
            with self.subTest(template=name):
                path = COMPARATOR / name
                self.assertEqual(
                    hashlib.sha256(path.read_bytes()).hexdigest(),
                    expected_hash,
                )

    def test_archived_native_harness_is_byte_preserved_text(self) -> None:
        self.assertEqual(
            hashlib.sha256(ARCHIVED_NATIVE_HARNESS.read_bytes()).hexdigest(),
            ARCHIVED_NATIVE_HARNESS_SHA256,
        )

    def test_clean_closure_rows_keeps_supported_tsv_rows(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            raw = root / "closure.tsv"
            clean = root / "closure.clean.tsv"
            raw.write_text(
                "\n".join(
                    [
                        "noise from an unexpected diagnostic",
                        "Decl\tMIPStarRE/Foo.lean\t1\t2",
                        "too\tmany\tcolumns\tfor\tthis\trow",
                        "Hole\tMIPStarRE/Hole.lean\t3\t4\tDEF_SAFE",
                        "Generated\tMIPStarRE/Bar.lean\tNORANGE\tNORANGE",
                    ]
                )
                + "\n",
                encoding="utf-8",
            )

            check_challenge_drift.clean_closure_rows(raw, clean)

            self.assertEqual(
                clean.read_text(encoding="utf-8"),
                "Decl\tMIPStarRE/Foo.lean\t1\t2\n"
                "Hole\tMIPStarRE/Hole.lean\t3\t4\tDEF_SAFE\n"
                "Generated\tMIPStarRE/Bar.lean\tNORANGE\tNORANGE\n",
            )

    def test_closure_extraction_loads_transitive_server_metadata(self) -> None:
        challenge = challenge_config.load_challenges(["ldt"])[0]
        with tempfile.TemporaryDirectory() as td:
            workdir = Path(td)

            def fake_run(cmd, *, cwd, stdout=None, env=None):
                self.assertEqual(cwd, REPO_ROOT)
                self.assertIsNotNone(stdout)
                assert stdout is not None
                stdout.write_text(
                    "Decl\tMIPStarRE/Foo.lean\t1\t2\n", encoding="utf-8"
                )
                return ""

            with patch.object(check_challenge_drift, "run", side_effect=fake_run) as run:
                check_challenge_drift.closure_tsv(REPO_ROOT, workdir, challenge)

            command = run.call_args.args[0]
            self.assertEqual(
                command[:4],
                ["lake", "env", "lean", "-DElab.inServer=true"],
            )

    def test_pr_ci_runs_drift_guard_after_lean_build_for_comparator_changes(self) -> None:
        workflow = PR_CI.read_text(encoding="utf-8")
        self.assertIn("comparator: ${{ steps.filter.outputs.comparator }}", workflow)
        self.assertIn("- 'scripts/comparator/**'", workflow)
        self.assertIn("needs.changes.outputs.comparator == 'true'", workflow)
        build = workflow.index("lake build MIPStarRE.LDT.Test.AxiomAudit")
        palomar_guard = workflow.index(
            "python3 scripts/comparator/check_challenge_drift.py "
            "--root . --challenge palomar"
        )
        palomar_write = workflow.index("--challenge palomar --write")
        palomar_compile = workflow.index('lake env lean "$PALOMAR_CHALLENGE"')
        self.assertLess(build, palomar_guard)
        self.assertLess(palomar_guard, palomar_write)
        self.assertLess(palomar_write, palomar_compile)

    def test_readme_documents_update_command_and_footer_source(self) -> None:
        readme = README.read_text(encoding="utf-8")
        self.assertIn(
            "python3 scripts/comparator/check_challenge_drift.py --root . --update",
            readme,
        )
        self.assertIn("challenge_footer.lean.in", readme)
        self.assertIn("MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean", readme)
        self.assertIn("--challenge", readme)
        self.assertIn("challenges/qpbt.json", readme)
        self.assertIn("challenges/palomar.json", readme)
        self.assertIn(
            "refuses a challenge whose configured header or footer file is not",
            readme,
        )
        self.assertIn("challenge_qpbt_footer.lean.in", readme)
        self.assertIn("MIPStarRE/QPBT/Test/Completeness.lean", readme)
        self.assertIn("MIPStarRE/QPBT/Test/LowDegreeGameTheorems.lean", readme)
        self.assertIn("MIPStarRE/QPBT/Test/Soundness.lean", readme)
        self.assertIn("MIPStarRE/QPBT/Test/QubitForm.lean", readme)
        self.assertIn("definition_names", readme)
        self.assertIn("provenance_comments", readme)
        self.assertIn("Solution axiom audit", readme)
        self.assertIn("994 physical lines and 52,141 UTF-8 bytes", readme)
        self.assertIn("Lean 4.35.0-rc2", readme)
        self.assertIn("3,509 physical lines and 161,038 bytes", readme)
        self.assertIn("module-conversion packet #753", readme)
        self.assertIn(LDT_BASELINE_SHA256, readme)

    def test_ldt_expected_matches_baseline(self) -> None:
        actual = hashlib.sha256(LDT_EXPECTED.read_bytes()).hexdigest()

        self.assertEqual(
            actual,
            LDT_BASELINE_SHA256,
            "the checked-in LDT challenge changed from its preserved baseline; "
            "QPBT-only work must restore the original bytes, while an intentional "
            "LDT closure change must follow the explicit baseline-update process "
            "in scripts/comparator/README.md",
        )

    def test_machine_wide_guard_selects_every_configured_challenge(self) -> None:
        # `local/bin/ci.sh` passes no --challenge, so every configuration under
        # challenges/ is checked; a new challenge is picked up by adding its
        # file alone.
        configured = {path.stem for path in (COMPARATOR / "challenges").glob("*.json")}
        self.assertEqual(sorted(configured), ["ldt", "palomar", "qpbt"])

        self.assertIn(
            "python3 scripts/comparator/check_challenge_drift.py --root .\n",
            CI_SH.read_text(encoding="utf-8"),
        )
        local_ci = CI_SH.read_text(encoding="utf-8")
        self.assertIn("--root . --challenge palomar --write", local_ci)
        self.assertIn('lake env lean "$palomar_challenge"', local_ci)

    def test_pr_ci_names_published_challenges(self) -> None:
        workflow = PR_CI.read_text(encoding="utf-8")
        for name in ("ldt", "qpbt", "palomar"):
            self.assertIn(
                "python3 scripts/comparator/check_challenge_drift.py "
                f"--root . --challenge {name}",
                workflow,
            )

    def test_palomar_solution_axiom_roots_are_explicit(self) -> None:
        audit = QPBT_AXIOM_AUDIT.read_text(encoding="utf-8")
        for module in (
            "MIPStarRE.QPBT.Palomar.PauliCompleteness",
            "MIPStarRE.QPBT.Palomar.LowDegreeSoundness",
            "MIPStarRE.QPBT.Palomar.PauliSoundness",
        ):
            self.assertIn(f"import {module}", audit)
        for declaration in (
            "MIPStarRE.QPBT.Palomar.exists_spcc_value_one",
            "MIPStarRE.QPBT.Palomar.exists_ld_soundness",
            "MIPStarRE.QPBT.Palomar.pauli_soundness",
            "MIPStarRE.QPBT.Palomar.pauli_soundness_qubit",
            "MIPStarRE.QPBT.fixedFieldModel",
        ):
            self.assertIn(f"audit_standard_axioms {declaration}", audit)

    def test_every_challenge_is_configured_completely(self) -> None:
        challenges = {
            challenge.name: challenge
            for challenge in challenge_config.load_challenges()
        }
        self.assertEqual(sorted(challenges), ["ldt", "palomar", "qpbt"])
        for name, challenge in challenges.items():
            with self.subTest(challenge=name):
                self.assertTrue(challenge.targets)
                self.assertTrue(challenge.imports)
                for path in (challenge.header, challenge.footer):
                    self.assertIsNotNone(path, f"{name}: unconfigured challenge part")
                    assert path is not None
                    self.assertTrue(
                        (REPO_ROOT / path).is_file(), f"{name}: missing {path}"
                    )
                expected = REPO_ROOT / challenge.expected
                if challenge.split:
                    # one generated module per contributing library module
                    self.assertTrue(
                        expected.is_dir(),
                        f"{name}: missing directory {challenge.expected}",
                    )
                    self.assertTrue(
                        (expected / "Challenge.lean").is_file(),
                        f"{name}: {challenge.expected} has no root module",
                    )
                    self.assertTrue(
                        any(expected.rglob("Challenge/**/*.lean")),
                        f"{name}: {challenge.expected} has no mirror modules",
                    )
                else:
                    self.assertTrue(
                        expected.is_file(), f"{name}: missing {challenge.expected}"
                    )

    def test_qpbt_targets_are_the_headline_theorems(self) -> None:
        qpbt = challenge_config.load_challenges(["qpbt"])[0]
        self.assertEqual(
            qpbt.targets,
            (
                "MIPStarRE.QPBT.pauli_soundness",
                "MIPStarRE.QPBT.pauli_soundness_qubit",
                "MIPStarRE.QPBT.exists_spcc_value_one",
                "MIPStarRE.QPBT.exists_ld_soundness",
            ),
        )
        self.assertEqual(qpbt.expected, "scripts/comparator/expected/qpbt")
        assert qpbt.footer is not None
        footer = (REPO_ROOT / qpbt.footer).read_text(encoding="utf-8")
        for target in qpbt.targets:
            self.assertIn(target.rsplit(".", 1)[1], footer)

    def test_qpbt_challenge_is_split_and_mathlib_only(self) -> None:
        qpbt = challenge_config.load_challenges(["qpbt"])[0]
        self.assertTrue(
            qpbt.split,
            "the QPBT challenge must mirror the library module partition: a "
            "single module cannot reproduce Lean's per-module auxiliary names",
        )
        expected = REPO_ROOT / qpbt.expected
        parts = sorted(expected.rglob("Challenge/**/*.lean"))
        self.assertTrue(parts)
        allowed_prefixes = ("Mathlib", "Challenge")
        for part in [expected / "Challenge.lean", *parts]:
            with self.subTest(module=part.name):
                text = part.read_text(encoding="utf-8")
                lines = text.splitlines()
                self.assertEqual(lines[0], "module")
                imports = []
                for line in lines[1:]:
                    # imports are only legal in the leading block of a module
                    match = re.fullmatch(r"public import\s+(.+)", line)
                    if match:
                        imports.append(match.group(1))
                    elif line.strip():
                        break
                self.assertTrue(imports, f"{part} has no imports")
                for imported in imports:
                    self.assertTrue(
                        imported.startswith(allowed_prefixes),
                        f"{part}: challenge modules may only import Mathlib and "
                        f"other challenge modules, found {imported!r}",
                    )
                self.assertIn("@[expose] public section", text)

    def test_palomar_challenge_is_monolithic_bounded_and_mathlib_only(self) -> None:
        palomar = challenge_config.load_challenges(["palomar"])[0]
        self.assertFalse(palomar.split)
        self.assertEqual(
            palomar.definition_names,
            ("MIPStarRE.QPBT.fixedFieldModel",),
        )
        data = PALOMAR_EXPECTED.read_bytes()
        self.assertEqual(hashlib.sha256(data).hexdigest(), PALOMAR_BASELINE_SHA256)
        text = data.decode("utf-8")
        self.assertLessEqual(len(text.splitlines()), 1000)
        self.assertLessEqual(len(data), 102400)
        self.assertIn("public import Mathlib", text)
        imports = re.findall(r"^(?:public )?import\s+(.+)$", text, re.MULTILINE)
        self.assertEqual(imports, ["Mathlib"])
        self.assertEqual(
            len(re.findall(r"^\s+sorry$", text, re.MULTILINE)),
            5,
        )
        self.assertNotRegex(text, r"^\s*axiom\s", "challenge declares an axiom")
        self.assertEqual(
            len(re.findall(r"^noncomputable def fixedFieldModel\b", text, re.MULTILINE)),
            1,
        )
        for target in palomar.targets:
            self.assertEqual(
                len(re.findall(
                    rf"^theorem {re.escape(target.rsplit('.', 1)[1])}\b",
                    text,
                    re.MULTILINE,
                )),
                1,
            )

    def test_extractor_reads_targets_from_the_environment(self) -> None:
        extractor = EXTRACTOR.read_text(encoding="utf-8")
        self.assertIn(challenge_config.TARGETS_ENV, extractor)


if __name__ == "__main__":
    unittest.main()
