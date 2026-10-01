#!/usr/bin/env python3
"""Regression tests for multi-challenge comparator configuration."""

from __future__ import annotations

import io
import json
import os
import subprocess
import sys
import tempfile
import textwrap
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
COMPARATOR = REPO_ROOT / "scripts" / "comparator"

# The comparator scripts import each other by module name, the way Python puts
# a script's own directory on the path; importing them here the same way keeps
# one `challenge_config` module object, so exception classes compare equal.
if str(COMPARATOR) not in sys.path:
    sys.path.insert(0, str(COMPARATOR))

import assemble_challenge  # noqa: E402
import challenge_config  # noqa: E402
import check_challenge_drift  # noqa: E402


MINIMAL = {
    "name": "sample",
    "imports": ["MIPStarRE.Foo"],
    "targets": ["MIPStarRE.Foo.bar"],
    "expected": "scripts/comparator/expected/sample.expected",
}


def write_config(directory: Path, name: str, **overrides) -> Path:
    data = dict(MINIMAL, name=name)
    data.update(overrides)
    path = directory / f"{name}.json"
    path.write_text(json.dumps(data), encoding="utf-8")
    return path


class ChallengeConfigLoadingTests(unittest.TestCase):
    def test_checked_in_challenges_load_and_are_distinct(self) -> None:
        challenges = challenge_config.load_challenges()
        by_name = {challenge.name: challenge for challenge in challenges}

        self.assertIn("ldt", by_name)
        self.assertIn("qpbt", by_name)
        self.assertEqual(
            by_name["ldt"].targets, ("MIPStarRE.LDT.Test.mainFormal",)
        )
        self.assertEqual(
            by_name["qpbt"].targets,
            (
                "MIPStarRE.QPBT.pauli_soundness",
                "MIPStarRE.QPBT.pauli_soundness_qubit",
                "MIPStarRE.QPBT.exists_spcc_value_one",
                "MIPStarRE.QPBT.exists_ld_soundness",
            ),
        )
        # the context tables are per challenge: neither challenge's keys may
        # constrain the other's closure
        self.assertTrue(by_name["ldt"].extras)
        self.assertTrue(by_name["qpbt"].extras)
        self.assertEqual(
            set(by_name["ldt"].module_preludes)
            & set(by_name["qpbt"].module_preludes),
            {"MIPStarRE/Quantum/FiniteMatrix/NormalizedTrace.lean"},
        )
        # both challenges have a checked-in expected copy
        self.assertTrue(by_name["ldt"].require_expected)
        self.assertTrue(by_name["qpbt"].require_expected)
        self.assertEqual(by_name["ldt"].definition_names, ())
        self.assertEqual(by_name["qpbt"].definition_names, ())
        self.assertTrue((REPO_ROOT / by_name["ldt"].expected).exists())
        self.assertTrue((REPO_ROOT / by_name["qpbt"].expected).exists())

    def test_ldt_expected_path_and_tables_are_unchanged(self) -> None:
        ldt = challenge_config.load_challenges(["ldt"])[0]

        self.assertEqual(
            ldt.expected, "scripts/comparator/expected/Challenge.lean.expected"
        )
        self.assertEqual(ldt.header, "scripts/comparator/challenge_header.lean")
        self.assertEqual(ldt.footer, "scripts/comparator/challenge_footer.lean")
        self.assertEqual(
            sorted(ldt.extras),
            [
                "MIPStarRE.LDT.AxisLinePolynomial.toFun",
                "MIPStarRE.LDT.DiagonalLinePolynomial.toFun",
                "MIPStarRE.LDT.FieldModel",
                "MIPStarRE.LDT.Polynomial.toFun",
            ],
        )
        (scope,) = ldt.module_preludes[
            "MIPStarRE/Quantum/FiniteMatrix/NormalizedTrace.lean"
        ]
        self.assertEqual(scope.namespace, ("MIPStarRE.Quantum",))
        self.assertEqual(scope.lines[0], "open scoped Matrix.Norms.Elementwise")
        self.assertTrue(scope.whole_file)
        self.assertFalse(scope.noncomputable)

    def test_qpbt_scopes_carry_line_ranges_and_noncomputable_sections(self) -> None:
        qpbt = challenge_config.load_challenges(["qpbt"])[0]

        submeasurement, measurement = qpbt.module_preludes[
            "MIPStarRE/Quantum/Measurement.lean"
        ]
        for scope, namespace, declaration_line in (
            (submeasurement, "Submeasurement", 67),
            (measurement, "Measurement", 128),
        ):
            self.assertEqual(scope.namespace, ("MIPStarRE.Quantum", namespace))
            self.assertTrue(scope.covers(declaration_line))
            self.assertEqual(scope.lines, (
                "variable {d : Type*} [Fintype d] [DecidableEq d]",
                "variable {α β : Type*} [Fintype α] [Fintype β]",
            ))

        (completeness,) = qpbt.module_preludes[
            "MIPStarRE/QPBT/Test/Completeness.lean"
        ]
        self.assertEqual(completeness.namespace, ("MIPStarRE.QPBT",))
        self.assertTrue(completeness.noncomputable)
        self.assertEqual((completeness.first, completeness.last), (30, 290))

        (qubit_form,) = qpbt.module_preludes["MIPStarRE/QPBT/Test/QubitForm.lean"]
        self.assertTrue(qubit_form.noncomputable)
        self.assertFalse(qubit_form.whole_file)

    def test_overlapping_scopes_of_one_module_are_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = write_config(
                Path(td),
                "sample",
                module_preludes={
                    "MIPStarRE/Foo.lean": [
                        {"namespace": ["A"], "lines": [], "first": 1, "last": 20},
                        {"namespace": ["A"], "lines": [], "first": 20, "last": 40},
                    ]
                },
            )

            with self.assertRaises(challenge_config.ChallengeConfigError) as ctx:
                challenge_config.load_challenge(path)

            self.assertIn("overlapping", str(ctx.exception))

    def test_unknown_scope_key_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = write_config(
                Path(td),
                "sample",
                module_preludes={
                    "MIPStarRE/Foo.lean": {"namespace": ["A"], "lines": [], "las": 3}
                },
            )

            with self.assertRaises(challenge_config.ChallengeConfigError) as ctx:
                challenge_config.load_challenge(path)

            self.assertIn("las", str(ctx.exception))

    def test_challenges_load_in_deterministic_file_name_order(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            directory = Path(td)
            for name in ("zeta", "alpha", "mid"):
                write_config(directory, name)

            names = [
                challenge.name
                for challenge in challenge_config.load_challenges(directory=directory)
            ]

            self.assertEqual(names, ["alpha", "mid", "zeta"])

    def test_missing_required_key_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "sample.json"
            data = dict(MINIMAL)
            del data["targets"]
            path.write_text(json.dumps(data), encoding="utf-8")

            with self.assertRaises(challenge_config.ChallengeConfigError) as ctx:
                challenge_config.load_challenge(path)

            self.assertIn("targets", str(ctx.exception))

    def test_empty_target_list_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = write_config(Path(td), "sample", targets=[])

            with self.assertRaises(challenge_config.ChallengeConfigError):
                challenge_config.load_challenge(path)

    def test_unknown_key_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = write_config(Path(td), "sample", extra_tables={})

            with self.assertRaises(challenge_config.ChallengeConfigError) as ctx:
                challenge_config.load_challenge(path)

            self.assertIn("extra_tables", str(ctx.exception))

    def test_name_must_match_file_stem(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "sample.json"
            path.write_text(json.dumps(dict(MINIMAL, name="other")), encoding="utf-8")

            with self.assertRaises(challenge_config.ChallengeConfigError):
                challenge_config.load_challenge(path)

    def test_unknown_challenge_name_lists_what_is_configured(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            directory = Path(td)
            write_config(directory, "alpha")

            with self.assertRaises(challenge_config.ChallengeConfigError) as ctx:
                challenge_config.load_challenges(["nope"], directory=directory)

            self.assertIn("alpha", str(ctx.exception))

    def test_targets_reach_the_extractor_through_the_environment(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = write_config(
                Path(td), "sample", targets=["A.one", "A.two"], imports=["A", "B"]
            )
            challenge = challenge_config.load_challenge(path)

            self.assertEqual(
                challenge.extractor_env(),
                {challenge_config.TARGETS_ENV: "A.one,A.two"},
            )
            self.assertEqual(challenge.import_block(), "import A\nimport B\n")

    def test_definition_names_are_optional_and_reach_the_extractor(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = write_config(
                Path(td),
                "sample",
                definition_names=["A.selected"],
            )
            challenge = challenge_config.load_challenge(path)

            self.assertEqual(challenge.definition_names, ("A.selected",))
            self.assertEqual(
                challenge.extractor_env(),
                {
                    challenge_config.TARGETS_ENV: "MIPStarRE.Foo.bar",
                    challenge_config.DEFINITIONS_ENV: "A.selected",
                },
            )

            empty_path = write_config(Path(td), "empty", definition_names=[])
            empty = challenge_config.load_challenge(empty_path)
            self.assertNotIn(
                challenge_config.DEFINITIONS_ENV,
                empty.extractor_env(),
            )

    def test_duplicate_definition_names_are_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = write_config(
                Path(td),
                "sample",
                definition_names=["A.selected", "A.selected"],
            )

            with self.assertRaises(challenge_config.ChallengeConfigError) as ctx:
                challenge_config.load_challenge(path)

            self.assertIn("duplicates", str(ctx.exception))


class MultiTargetAssemblyTests(unittest.TestCase):
    """The assembler orders a many-module closure by import rank, then line."""

    def _tree(self, root: Path) -> None:
        (root / "MIPStarRE").mkdir(parents=True)
        (root / "MIPStarRE" / "Base.lean").write_text(
            "\n".join(
                [
                    "import Mathlib",
                    "namespace MIPStarRE",
                    "def base : Nat := 0",
                    "def later : Nat := 1",
                    "end MIPStarRE",
                ]
            )
            + "\n",
            encoding="utf-8",
        )
        (root / "MIPStarRE" / "Mid.lean").write_text(
            "\n".join(
                [
                    "import MIPStarRE.Base",
                    "namespace MIPStarRE",
                    "def mid : Nat := base",
                    "end MIPStarRE",
                ]
            )
            + "\n",
            encoding="utf-8",
        )
        (root / "MIPStarRE" / "Top.lean").write_text(
            "\n".join(
                [
                    "import MIPStarRE.Mid",
                    "namespace MIPStarRE",
                    "def top : Nat := mid",
                    "end MIPStarRE",
                ]
            )
            + "\n",
            encoding="utf-8",
        )

    def _tsv(self, root: Path) -> Path:
        # deliberately shuffled, and mixing the two targets' closures
        tsv = root / "closure.clean.tsv"
        tsv.write_text(
            "\n".join(
                [
                    "MIPStarRE.top\tMIPStarRE/Top.lean\t3\t3",
                    "MIPStarRE.later\tMIPStarRE/Base.lean\t4\t4",
                    "MIPStarRE.mid\tMIPStarRE/Mid.lean\t3\t3",
                    "MIPStarRE.base\tMIPStarRE/Base.lean\t3\t3",
                    "MIPStarRE.generated\tMIPStarRE/Top.lean\tNORANGE\tNORANGE",
                ]
            )
            + "\n",
            encoding="utf-8",
        )
        return tsv

    def test_declarations_follow_import_rank_then_line_number(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            self._tree(root)
            tsv = self._tsv(root)
            challenge = challenge_config.load_challenge(
                write_config(root, "sample", targets=["MIPStarRE.top", "MIPStarRE.later"])
            )

            body = assemble_challenge.assemble(challenge, root, tsv)

            order = [
                line.split("(")[1].rstrip(")")
                for line in body.splitlines()
                if line.startswith("-- source:")
            ]
            self.assertEqual(
                order,
                ["MIPStarRE.base", "MIPStarRE.later", "MIPStarRE.mid", "MIPStarRE.top"],
            )
            self.assertIn("--   MIPStarRE.generated  (from MIPStarRE/Top.lean)", body)

    def test_assembly_is_independent_of_the_row_order(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            self._tree(root)
            tsv = self._tsv(root)
            challenge = challenge_config.load_challenge(write_config(root, "sample"))
            first = assemble_challenge.assemble(challenge, root, tsv)

            rows = tsv.read_text(encoding="utf-8").splitlines()
            tsv.write_text("\n".join(reversed(rows)) + "\n", encoding="utf-8")
            second = assemble_challenge.assemble(challenge, root, tsv)

        self.assertEqual(first, second)

    def test_stale_context_table_names_the_offending_challenge(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            self._tree(root)
            tsv = self._tsv(root)
            challenge = challenge_config.load_challenge(
                write_config(root, "sample", extras={"MIPStarRE.gone": ["-- x"]})
            )

            with self.assertRaises(assemble_challenge.StaleContextTables) as ctx:
                assemble_challenge.assemble(challenge, root, tsv)

            message = str(ctx.exception)
            self.assertIn("sample.json", message)
            self.assertIn("MIPStarRE.gone", message)


class DefinitionFrontierAssemblyTests(unittest.TestCase):
    def _source_tree(self, root: Path) -> tuple[Path, dict[str, int]]:
        source = root / "MIPStarRE" / "Frontier.lean"
        source.parent.mkdir(parents=True)
        lines = [
            "import Mathlib",
            "namespace MIPStarRE.Frontier",
            "def typeDependency : Type := Nat",
            "def valueOnlyHelper : Nat := 7",
            "noncomputable def selected.{u} (α : Type u)",
            "    (_n : typeDependency) : Type u :=",
            "  if valueOnlyHelper = 7 then α else α",
            "theorem proofHelper : True := trivial",
            "def ordinary : True := proofHelper",
            "end MIPStarRE.Frontier",
        ]
        source.write_text("\n".join(lines) + "\n", encoding="utf-8")
        return source, {line: index + 1 for index, line in enumerate(lines)}

    def test_registered_value_is_replaced_and_other_values_remain(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _, line = self._source_tree(root)
            tsv = root / "closure.tsv"
            tsv.write_text(
                "\n".join(
                    [
                        "MIPStarRE.Frontier.typeDependency\t"
                        f"MIPStarRE/Frontier.lean\t{line['def typeDependency : Type := Nat']}\t"
                        f"{line['def typeDependency : Type := Nat']}",
                        "MIPStarRE.Frontier.selected\tMIPStarRE/Frontier.lean\t"
                        f"{line['noncomputable def selected.{u} (α : Type u)']}\t"
                        f"{line['  if valueOnlyHelper = 7 then α else α']}\tDEF_SAFE",
                        "MIPStarRE.Frontier.proofHelper\tMIPStarRE/Frontier.lean\t"
                        f"{line['theorem proofHelper : True := trivial']}\t"
                        f"{line['theorem proofHelper : True := trivial']}",
                        "MIPStarRE.Frontier.ordinary\tMIPStarRE/Frontier.lean\t"
                        f"{line['def ordinary : True := proofHelper']}\t"
                        f"{line['def ordinary : True := proofHelper']}",
                    ]
                )
                + "\n",
                encoding="utf-8",
            )
            challenge = challenge_config.load_challenge(
                write_config(
                    root,
                    "sample",
                    definition_names=["MIPStarRE.Frontier.selected"],
                )
            )

            body = assemble_challenge.assemble(challenge, root, tsv)

            self.assertIn("def typeDependency : Type := Nat", body)
            self.assertIn("noncomputable def selected.{u} (α : Type u)", body)
            self.assertIn("(_n : typeDependency) : Type u := by\n  sorry", body)
            self.assertNotIn("valueOnlyHelper", body)
            self.assertIn("theorem proofHelper : True := trivial", body)
            self.assertIn("def ordinary : True := proofHelper", body)

    def test_registered_definition_without_metadata_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            _, line = self._source_tree(root)
            tsv = root / "closure.tsv"
            selected = line["noncomputable def selected.{u} (α : Type u)"]
            tsv.write_text(
                "MIPStarRE.Frontier.selected\tMIPStarRE/Frontier.lean\t"
                f"{selected}\t{selected + 2}\n",
                encoding="utf-8",
            )
            challenge = challenge_config.load_challenge(
                write_config(
                    root,
                    "sample",
                    definition_names=["MIPStarRE.Frontier.selected"],
                )
            )

            with self.assertRaises(assemble_challenge.StaleContextTables):
                assemble_challenge.assemble(challenge, root, tsv)

    def test_value_replacement_preserves_definition_safety_modifier(self) -> None:
        cases = {
            "safe": "def selected : Nat := 1",
            "unsafe": "unsafe def selected : Nat := 1",
            "partial": "partial def selected : Nat := selected",
        }
        for safety, source in cases.items():
            with self.subTest(safety=safety):
                replaced = assemble_challenge.replace_definition_value(
                    "selected",
                    [source],
                    assemble_challenge.DefinitionHole(safety=safety),
                )
                self.assertEqual(
                    replaced,
                    source.split(":=", 1)[0].rstrip() + " := by\n  sorry",
                )


class DefinitionFrontierExtractionTests(unittest.TestCase):
    FIXTURE = """
namespace MIPStarRE.ComparatorDefinitionFrontierFixture

def typeDependency : Type := Nat
def registeredValueHelper : Nat := 7
def registered (_n : typeDependency) : Nat := registeredValueHelper
theorem ordinaryProofHelper (n : Nat) : n = n := rfl
def ordinaryValueHelper : Nat := 1
def ordinary : { n : Nat // n = n } :=
  ⟨registered ordinaryValueHelper, ordinaryProofHelper _⟩
theorem target : ordinary = ordinary := rfl

end MIPStarRE.ComparatorDefinitionFrontierFixture
"""

    def _run_extractor(self, definition_names: str | None) -> subprocess.CompletedProcess[str]:
        template = (COMPARATOR / "extract_closure.lean").read_text(encoding="utf-8")
        source = check_challenge_drift.IMPORT_BLOCK.sub(
            "import Mathlib\n", template, count=1
        )
        source = source.replace(
            "\n#eval runExtract\n",
            "\n" + textwrap.dedent(self.FIXTURE) + "\n#eval runExtract\n",
        )
        with tempfile.TemporaryDirectory() as td:
            extractor = Path(td) / "extract_fixture.lean"
            extractor.write_text(source, encoding="utf-8")
            env = dict(os.environ)
            env[challenge_config.TARGETS_ENV] = (
                "MIPStarRE.ComparatorDefinitionFrontierFixture.target"
            )
            env.pop(challenge_config.DEFINITIONS_ENV, None)
            if definition_names is not None:
                env[challenge_config.DEFINITIONS_ENV] = definition_names
            return subprocess.run(
                ["lake", "env", "lean", str(extractor)],
                cwd=REPO_ROOT,
                env=env,
                check=False,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
            )

    @staticmethod
    def _declaration_names(output: str) -> set[str]:
        return {
            line.split("\t", 1)[0]
            for line in output.splitlines()
            if len(line.split("\t")) in (4, 5)
        }

    def test_real_extraction_stops_only_the_registered_value(self) -> None:
        prefix = "MIPStarRE.ComparatorDefinitionFrontierFixture."
        selected = prefix + "registered"
        result = self._run_extractor(selected)

        self.assertEqual(result.returncode, 0, result.stdout)
        names = self._declaration_names(result.stdout)
        self.assertIn(selected, names)
        self.assertIn(prefix + "typeDependency", names)
        self.assertNotIn(prefix + "registeredValueHelper", names)
        self.assertIn(prefix + "ordinary", names)
        self.assertIn(prefix + "ordinaryValueHelper", names)
        self.assertIn(prefix + "ordinaryProofHelper", names)
        selected_row = next(
            line for line in result.stdout.splitlines() if line.startswith(selected + "\t")
        )
        self.assertTrue(selected_row.endswith("\tDEF_SAFE"), selected_row)

        ordinary = self._run_extractor(None)
        self.assertEqual(ordinary.returncode, 0, ordinary.stdout)
        self.assertIn(prefix + "registeredValueHelper", self._declaration_names(ordinary.stdout))

    def test_real_extraction_rejects_bad_registered_names(self) -> None:
        prefix = "MIPStarRE.ComparatorDefinitionFrontierFixture."
        for name, message in (
            (prefix + "missing", "registered definition not found"),
            (prefix + "target", "registered definition is not a definition"),
        ):
            with self.subTest(name=name):
                result = self._run_extractor(name)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn(message, result.stdout)


class AbsentExpectedFileTests(unittest.TestCase):
    def _challenge(self, directory: Path, **overrides):
        return challenge_config.load_challenge(
            write_config(
                directory,
                "sample",
                expected="expected/sample.expected",
                **overrides,
            )
        )

    def test_optional_expected_file_is_skipped_not_regenerated(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            challenge = self._challenge(root, require_expected=False)
            buffer = io.StringIO()

            # no lake invocation may happen: the expected file gates assembly
            with redirect_stdout(buffer):
                status = check_challenge_drift.check_challenge(
                    root, challenge, update=False, write=None
                )

            self.assertEqual(status, 0)
            self.assertIn("no expected file yet", buffer.getvalue())
            self.assertIn("expected/sample.expected", buffer.getvalue())

    def test_required_expected_file_is_an_error_when_absent(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            challenge = self._challenge(root, require_expected=True)
            buffer = io.StringIO()

            with redirect_stderr(buffer):
                status = check_challenge_drift.check_challenge(
                    root, challenge, update=False, write=None
                )

            self.assertEqual(status, 1)
            self.assertIn("does not exist", buffer.getvalue())

    def test_update_refuses_a_challenge_with_an_absent_part(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            challenge = self._challenge(
                root, footer="footer.lean", require_expected=False
            )
            buffer = io.StringIO()

            # the refusal precedes assembly: no lake invocation may happen,
            # and no expected copy without the footer may be left behind
            with redirect_stderr(buffer):
                status = check_challenge_drift.check_challenge(
                    root, challenge, update=True, write=None
                )

            self.assertEqual(status, 1)
            self.assertIn("refusing to update", buffer.getvalue())
            self.assertIn("footer.lean", buffer.getvalue())
            self.assertFalse((root / challenge.expected).exists())

    def test_write_of_a_challenge_with_an_absent_part_is_still_allowed(self) -> None:
        # `--write` is the development loop; only the checked-in copy is gated
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            challenge = self._challenge(
                root, footer="footer.lean", require_expected=False
            )

            self.assertEqual(
                check_challenge_drift.missing_challenge_inputs(root, challenge),
                ["footer.lean"],
            )
            calls = []
            original = check_challenge_drift.assemble_candidate

            def fake(assemble_root, workdir, assemble_challenge_config):
                calls.append(assemble_challenge_config.name)
                candidate = workdir / "Challenge.lean"
                candidate.write_bytes(b"-- draft\n")
                return candidate

            check_challenge_drift.assemble_candidate = fake
            try:
                status = check_challenge_drift.check_challenge(
                    root, challenge, update=True, write=root / "draft.lean"
                )
            finally:
                check_challenge_drift.assemble_candidate = original

            self.assertEqual(status, 0)
            self.assertEqual(calls, ["sample"])
            self.assertEqual((root / "draft.lean").read_bytes(), b"-- draft\n")
            self.assertFalse((root / challenge.expected).exists())

    def test_write_needs_exactly_one_challenge(self) -> None:
        buffer = io.StringIO()

        with redirect_stderr(buffer):
            status = check_challenge_drift.main(
                ["--root", str(REPO_ROOT), "--write", "/dev/null"]
            )

        self.assertEqual(status, 1)
        self.assertIn("exactly one --challenge", buffer.getvalue())

    def test_missing_header_and_footer_are_reported(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            challenge = self._challenge(
                root, header="header.lean", footer="footer.lean"
            )

            self.assertEqual(
                check_challenge_drift.missing_challenge_inputs(root, challenge),
                ["header.lean", "footer.lean"],
            )
            # and are omitted rather than crashing the assembly
            self.assertEqual(check_challenge_drift.challenge_part(root, None), b"")
            self.assertEqual(
                check_challenge_drift.challenge_part(root, "footer.lean"), b""
            )
            (root / "header.lean").write_text("import Mathlib\n", encoding="utf-8")
            self.assertEqual(
                check_challenge_drift.challenge_part(root, "header.lean"),
                b"import Mathlib\n",
            )


class ExtractorRenderingTests(unittest.TestCase):
    def test_import_block_is_substituted_once(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            challenge = challenge_config.load_challenge(
                write_config(Path(td), "sample", imports=["A.B", "C"])
            )
            template = "import Old.Module\n\n/-! doc -/\nimport-looking text\n"

            rendered = check_challenge_drift.render_extractor(challenge, template)

            self.assertEqual(
                rendered, "import A.B\nimport C\n\n/-! doc -/\nimport-looking text\n"
            )

    def test_checked_in_extractor_keeps_its_default_target(self) -> None:
        source = (COMPARATOR / "extract_closure.lean").read_text(encoding="utf-8")

        self.assertIn("MIPSTARRE_COMPARATOR_TARGETS", source)
        self.assertIn("`MIPStarRE.LDT.Test.mainFormal", source)
        self.assertTrue(source.startswith("import "))

    def test_template_without_an_import_block_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            challenge = challenge_config.load_challenge(write_config(Path(td), "sample"))

            with self.assertRaises(challenge_config.ChallengeConfigError):
                check_challenge_drift.render_extractor(challenge, "open Lean\n")


if __name__ == "__main__":
    unittest.main()
