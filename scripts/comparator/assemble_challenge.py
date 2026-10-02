#!/usr/bin/env python3
"""Assemble the body of a comparator `Challenge.lean` from the extractor's TSV.

Input: the TSV produced by ``extract_closure.lean`` (one declaration per row:
name, module path, start line, end line, plus optional registered-definition
metadata).  For each declaration this script re-reads its source lines and
records the namespace stack active at that point (tracking
``namespace``/``section``/``end`` lines), orders declarations topologically
(module import rank, then line number), and emits the snippets grouped under
merged namespace blocks.  Per-declaration provenance comments are configurable;
they are enabled by default.

The elaboration context that the kernel closure cannot see (attribute commands,
``CoeFun`` instances, ``variable``/``open`` blocks) lives in the ``extras`` and
``module_preludes`` tables of the selected challenge configuration under
``challenges/``; the script fails if one of *that challenge's* keys no longer
matches any extracted declaration.  See README.md in this directory for the
full regeneration pipeline.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import NamedTuple

from challenge_config import (
    DEFAULT_CHALLENGE,
    ChallengeConfig,
    ChallengeConfigError,
    Prelude,
    load_challenges,
)


class DefinitionHole(NamedTuple):
    """Exact declaration data for a registered definition value frontier."""

    safety: str


Entry = tuple[str, str, int, int, list[str], DefinitionHole | None]


class StaleContextTables(ValueError):
    """A challenge's ``extras``/``module_preludes`` key matches no declaration."""


class DefinitionFrontierError(ValueError):
    """Definition-hole metadata does not match the selected challenge."""


def source_range_with_context(
    lines: list[str], start: int, end: int
) -> tuple[int, list[str]]:
    """Extend a declaration range to include adjacent scoped context commands."""
    # Lean's source range starts at a declaration's docstring and can omit a
    # declaration-scoped command immediately before it.  Preserve that command:
    # dropping `open scoped Classical in`, for example, removes the local
    # decidability instances needed to re-elaborate the definition body.
    if start > 1 and re.fullmatch(r"open\s+scoped\s+.+\s+in", lines[start - 2].strip()):
        start -= 1
    return start, lines[start - 1 : end]


class Assembler:
    def __init__(
        self,
        repo_root: Path,
        extras: dict[str, list[str]] | None = None,
        module_preludes: dict[str, tuple[Prelude, ...]] | None = None,
        definition_names: tuple[str, ...] = (),
        provenance_comments: bool = True,
    ) -> None:
        self.repo_root = repo_root
        self.extras = extras or {}
        self.module_preludes = module_preludes or {}
        self.definition_names = set(definition_names)
        self.provenance_comments = provenance_comments
        self._file_cache: dict[str, list[str]] = {}
        self.out: list[str] = []
        self.cur_ns: list[str] = []
        self.open_prelude: tuple[str, Prelude] | None = None
        self.used_preludes: set[tuple[str, int]] = set()
        self._closure_cache: dict[str, set[str]] = {}
        self.emitted_definition_names: set[str] = set()

    @staticmethod
    def definition_hole_source(
        name: str, source: list[str], hole: DefinitionHole
    ) -> list[str]:
        return replace_definition_value(name, source, hole).splitlines()

    def get_lines(self, path: str) -> list[str]:
        if path not in self._file_cache:
            text = (self.repo_root / path).read_text(encoding="utf-8")
            self._file_cache[path] = text.splitlines()
        return self._file_cache[path]

    def ns_stack_at(self, path: str, line_no: int) -> list[str]:
        """Namespace stack (list of names) active just before 1-indexed line_no."""
        stack: list[tuple[str, str | None]] = []
        for raw in self.get_lines(path)[: line_no - 1]:
            s = raw.strip()
            m = re.match(r"namespace\s+([\w.À-￿']+)", s)
            if m:
                stack.append(("ns", m.group(1)))
                continue
            m = re.match(r"(?:noncomputable\s+)?section\s*([\w.À-￿']*)", s)
            if m:
                stack.append(("sec", m.group(1) or None))
                continue
            m = re.match(r"end\s*([\w.À-￿']*)\s*(?:--.*)?$", s)
            if m and s.startswith("end") and stack:
                stack.pop()
        return [n for kind, n in stack if kind == "ns" and n is not None]

    def imports_of(self, path: str) -> list[str]:
        # imports are only legal at the top of a Lean file, so scanning the
        # whole file is safe and robust against comment and module headers
        return [
            m.group(1).replace(".", "/") + ".lean"
            for raw in self.get_lines(path)
            if (
                m := re.match(
                    r"(?:public\s+)?(?:meta\s+)?import(?:\s+all)?\s+([\w.]+)",
                    raw,
                )
            )
        ]

    def local_closure(self, path: str) -> set[str]:
        """All `MIPStarRE/...` modules `path` imports, transitively."""
        cached = self._closure_cache.get(path)
        if cached is not None:
            return cached
        self._closure_cache[path] = set()  # cycle guard
        out: set[str] = set()
        for dep in self.imports_of(path):
            if not dep.startswith("MIPStarRE/"):
                continue
            if not (self.repo_root / dep).exists():
                continue
            out.add(dep)
            out |= self.local_closure(dep)
        self._closure_cache[path] = out
        return out

    def module_ranks(self, mods: set[str]) -> dict[str, int]:
        rank: dict[str, int] = {}

        def visit(p: str, depth: int = 0) -> None:
            if p in rank or depth > 200:
                return
            rank[p] = -1  # in progress
            local = [d for d in self.imports_of(p) if d.startswith("MIPStarRE/")]
            for d in local:
                if rank.get(d) != -1:
                    visit(d, depth + 1)
            rank[p] = max((rank.get(d, 0) for d in local), default=0) + 1

        for p in sorted(mods):
            visit(p)
        return rank

    def switch_ns(self, target: list[str]) -> None:
        common = 0
        while (
            common < min(len(self.cur_ns), len(target))
            and self.cur_ns[common] == target[common]
        ):
            common += 1
        for n in reversed(self.cur_ns[common:]):
            self.out.append(f"end {n}")
        for n in target[common:]:
            self.out.append(f"namespace {n}")
        self.cur_ns = target

    def prelude_for(self, path: str, line: int) -> Prelude | None:
        """The configured scope of ``path`` covering ``line``, if any."""
        for prelude in self.module_preludes.get(path, ()):
            if prelude.covers(line):
                return prelude
        return None

    def close_prelude(self) -> None:
        if self.open_prelude:
            self.switch_ns(list(self.open_prelude[1].namespace))
            self.out.append("end  -- module scope")
            self.open_prelude = None

    def open_prelude_for(self, path: str, prelude: Prelude) -> None:
        self.switch_ns(list(prelude.namespace))
        label = path if prelude.whole_file else f"{path}:{prelude.first}-{prelude.last}"
        self.out.append("")
        self.out.append(f"-- elaboration context of {label}")
        self.out.append("noncomputable section" if prelude.noncomputable else "section")
        self.out.extend(prelude.lines)
        self.open_prelude = (path, prelude)
        self.used_preludes.add((path, prelude.first))

    def emit(self, entries: list[Entry], generated: list[tuple[str, str]]) -> str:
        if not self.provenance_comments and (entries or generated):
            self.out.append("")
        # compiler-generated declarations (no source range) regenerate
        # identically during elaboration; record them up front as comments so
        # they never interact with namespace or prelude state
        if generated:
            self.out.append("-- Compiler-generated declarations in the closure (no source")
            self.out.append("-- range); they regenerate identically during elaboration:")
            for name, path in generated:
                self.out.append(f"--   {name}  (from {path})")

        emitted_ranges: set[tuple[str, int]] = set()
        # widest range emitted so far per module, to swallow the pieces of a
        # declaration that the closure reports separately
        enclosing: dict[str, tuple[int, int]] = {}
        for name, path, a, b, src, hole in entries:
            if (path, a) in emitted_ranges and hole is None:
                # deriving twins share the range
                continue
            if (path, a) in emitted_ranges:
                raise DefinitionFrontierError(
                    f"registered definition {name!r} shares an already emitted "
                    f"source range {path}:{a}-{b}"
                )
            # a constructor's `.elim`/`.noConfusion`/`.injEq` companion and a
            # `deriving` clause report a range *inside* their inductive's
            # range; emitting those lines on their own is a syntax error, and
            # the inductive command regenerates them anyway
            outer = enclosing.get(path)
            if outer is not None and outer[0] <= a and b <= outer[1] and hole is None:
                continue
            if outer is not None and outer[0] <= a and b <= outer[1]:
                raise DefinitionFrontierError(
                    f"registered definition {name!r} is nested in source range "
                    f"{path}:{outer[0]}-{outer[1]}"
                )
            emitted_ranges.add((path, a))
            enclosing[path] = (a, b)
            prelude = self.prelude_for(path, a)
            if self.open_prelude and self.open_prelude != (path, prelude):
                self.close_prelude()
            if prelude is not None and self.open_prelude is None:
                self.open_prelude_for(path, prelude)
            self.switch_ns(self.ns_stack_at(path, a))
            if self.provenance_comments:
                self.out.append("")
                self.out.append(f"-- source: {path}:{a}-{b}  ({name})")
            if hole is None:
                self.out.extend(src)
            else:
                self.out.extend(self.definition_hole_source(name, src, hole))
                self.emitted_definition_names.add(name)
            self.out.extend(self.extras.get(name, []))
        self.close_prelude()
        self.switch_ns([])
        return "\n".join(self.out)


MIRROR_ROOT = "Challenge"


def mirror_module(path: str) -> str:
    """`MIPStarRE/QPBT/Algebra/Pauli.lean` -> `Challenge.MIPStarRE.QPBT.Algebra.Pauli`."""
    return f"{MIRROR_ROOT}." + path.removesuffix(".lean").replace("/", ".")


def mirror_file(path: str) -> str:
    return f"{MIRROR_ROOT}/" + path


def optional_part_text(root: Path, relative: str | None) -> str:
    """A configured challenge part, or empty text when omitted or absent."""
    if relative is None:
        return ""
    path = root / relative
    return path.read_text(encoding="utf-8") if path.exists() else ""


class SplitAssembler(Assembler):
    """Emit one Mathlib-only challenge module per contributing library module.

    Lean caches an abstracted nested proof and a `match` auxiliary *per module*,
    keyed by the statement and named after the first declaration of that module
    that needs it, and a module only sees the instances its imports declare.  A
    single-file challenge therefore cannot reproduce either name when a library
    fact is needed in two library modules, and it makes every instance visible
    to every declaration.  Mirroring the library's module partition and import
    graph reproduces both by construction.
    """

    def module_body(self, path: str, entries: list[Entry]) -> str:
        self.out = []
        self.cur_ns = []
        self.open_prelude = None
        return self.emit(entries, [])


def minimal_mirror_imports(
    asm: SplitAssembler, path: str, contributing: set[str]
) -> list[str]:
    """Contributing modules `path` imports, with redundant ancestors dropped."""
    reach = {q for q in asm.local_closure(path) if q in contributing}
    minimal = [
        q
        for q in reach
        if not any(r != q and q in asm.local_closure(r) for r in reach)
    ]
    return sorted(minimal)


def assemble_split(
    challenge: ChallengeConfig, root: Path, tsv: Path
) -> dict[str, str]:
    """Return {path relative to the challenge repository: file contents}."""
    asm = SplitAssembler(
        root,
        challenge.extras,
        challenge.module_preludes,
        challenge.definition_names,
        challenge.provenance_comments,
    )
    entries, generated = read_entries(asm, tsv)

    rank = asm.module_ranks({e[1] for e in entries})
    entries.sort(key=lambda e: (rank.get(e[1], 999), e[1], e[2]))

    by_module: dict[str, list[Entry]] = {}
    for entry in entries:
        by_module.setdefault(entry[1], []).append(entry)
    contributing = set(by_module)
    ordered = sorted(contributing, key=lambda m: (rank.get(m, 999), m))

    opens = list(challenge.common_opens)
    files: dict[str, str] = {}
    for path in ordered:
        deps = minimal_mirror_imports(asm, path, contributing)
        head = ["module", "", "public import Mathlib"]
        head += [f"public import {mirror_module(d)}" for d in deps]
        head += [
            "",
            f"/-! Challenge mirror of `{path}`.",
            "",
            "One challenge module per contributing library module, importing the",
            "mirrors of the library modules this one imports.  The partition is",
            "what makes Lean generate the same auxiliary declarations, under the",
            "same names, as the library does. -/",
            "",
        ]
        head += opens
        head += ["@[expose] public section", ""]
        body = asm.module_body(path, by_module[path])
        files[mirror_file(path)] = "\n".join(head) + "\n" + body + "\n"

    header = optional_part_text(root, challenge.header)
    footer = optional_part_text(root, challenge.footer)
    part_imports = "\n".join(f"public import {mirror_module(m)}" for m in ordered)
    marker = "import Mathlib\n"
    if not header:
        header = marker
    elif marker not in header:
        raise SystemExit("challenge header must start with `import Mathlib`")
    module_imports = "module\n\npublic import Mathlib\n" + part_imports + "\n"
    header = header.replace(marker, module_imports, 1)
    header += "@[expose] public section\n\n"

    lines: list[str] = []
    if generated:
        lines.append("-- Compiler-generated declarations in the closure (no source")
        lines.append("-- range); they regenerate identically during elaboration:")
        for name, gpath in generated:
            lines.append(f"--   {name}  (from {gpath})")
        lines.append("")
    files["Challenge.lean"] = header + "\n".join(lines) + footer

    check_stale_tables(asm, challenge, entries)
    return files


def read_entries(
    asm: Assembler, tsv: Path
) -> tuple[list[Entry], list[tuple[str, str]]]:
    entries: list[Entry] = []
    generated: list[tuple[str, str]] = []
    for row in tsv.read_text(encoding="utf-8").splitlines():
        if not row or "\t" not in row:
            continue
        columns = row.split("\t", 4)
        if len(columns) not in (4, 5):
            raise DefinitionFrontierError(f"malformed closure row: {row!r}")
        name, path, a, b = columns[:4]
        hole = parse_definition_hole(name, columns[4] if len(columns) == 5 else None)
        if hole is not None and name not in asm.definition_names:
            raise DefinitionFrontierError(
                f"closure marks unregistered definition {name!r} as a value hole"
            )
        if a == "NORANGE":
            if hole is not None:
                raise DefinitionFrontierError(
                    f"registered definition {name!r} has no source range"
                )
            generated.append((name, path))
            continue
        start, end = int(a), int(b)
        start, source = source_range_with_context(asm.get_lines(path), start, end)
        entries.append((name, path, start, end, source, hole))
    return entries, generated


def parse_definition_hole(name: str, raw: str | None) -> DefinitionHole | None:
    if raw is None:
        return None
    markers = {
        "DEF_SAFE": "safe",
        "DEF_UNSAFE": "unsafe",
        "DEF_PARTIAL": "partial",
    }
    safety = markers.get(raw)
    if safety is None:
        raise DefinitionFrontierError(
            f"invalid definition-hole marker for {name!r}: {raw!r}"
        )
    return DefinitionHole(safety=safety)


def replace_definition_value(
    name: str, source: list[str], hole: DefinitionHole
) -> str:
    """Keep a definition command's header and replace its top-level value."""
    text = "\n".join(source)
    declaration_seen = False
    paren_depth = 0
    bracket_depth = 0
    brace_depth = 0
    block_comment_depth = 0
    in_string = False
    escaped = False
    in_line_comment = False
    index = 0

    def at_top_level() -> bool:
        return paren_depth == bracket_depth == brace_depth == 0

    def token_at(token: str) -> bool:
        if not text.startswith(token, index):
            return False
        before = text[index - 1] if index else " "
        after_index = index + len(token)
        after = text[after_index] if after_index < len(text) else " "
        identifier = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'"
        return before not in identifier and after not in identifier

    while index < len(text):
        char = text[index]
        next_char = text[index + 1] if index + 1 < len(text) else ""

        if in_line_comment:
            if char == "\n":
                in_line_comment = False
            index += 1
            continue
        if block_comment_depth:
            if char == "/" and next_char == "-":
                block_comment_depth += 1
                index += 2
            elif char == "-" and next_char == "/":
                block_comment_depth -= 1
                index += 2
            else:
                index += 1
            continue
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if char == "-" and next_char == "-":
            in_line_comment = True
            index += 2
            continue
        if char == "/" and next_char == "-":
            block_comment_depth = 1
            index += 2
            continue
        if char == '"':
            in_string = True
            index += 1
            continue

        if char == "(":
            paren_depth += 1
        elif char == ")":
            paren_depth -= 1
        elif char == "[":
            bracket_depth += 1
        elif char == "]":
            bracket_depth -= 1
        elif char == "{":
            brace_depth += 1
        elif char == "}":
            brace_depth -= 1
        elif at_top_level() and not declaration_seen:
            if token_at("def") or token_at("abbrev") or token_at("instance"):
                declaration_seen = True
        elif at_top_level() and declaration_seen:
            if char == ":" and next_char == "=":
                return text[:index].rstrip() + " := by\n  sorry"
            if token_at("where") or char == "|":
                return text[:index].rstrip() + " := by\n  sorry"
        index += 1

    raise DefinitionFrontierError(
        f"could not locate the value of registered definition {name!r} "
        f"(validated safety: {hole.safety})"
    )


def check_stale_tables(
    asm: Assembler, challenge: ChallengeConfig, entries: list[Entry]
) -> None:
    unused_extras = set(challenge.extras) - {name for name, *_ in entries}
    unused_preludes = {
        f"{path}:{scope.first}"
        for path, scopes in challenge.module_preludes.items()
        for scope in scopes
        if (path, scope.first) not in asm.used_preludes
    }
    missing_definitions = set(challenge.definition_names) - asm.emitted_definition_names
    unexpected_definitions = asm.emitted_definition_names - set(challenge.definition_names)
    if unused_extras or unused_preludes or missing_definitions or unexpected_definitions:
        raise StaleContextTables(
            f"stale context tables in {challenge.path} — "
            f"unmatched extras keys: {sorted(unused_extras)}; "
            f"unmatched module_preludes scopes: {sorted(unused_preludes)}; "
            f"missing definition holes: {sorted(missing_definitions)}; "
            f"unexpected definition holes: {sorted(unexpected_definitions)}"
        )


def assemble(challenge: ChallengeConfig, root: Path, tsv: Path) -> str:
    """Assembled body text; raises ``StaleContextTables`` on an unmatched key."""
    asm = Assembler(
        root,
        challenge.extras,
        challenge.module_preludes,
        challenge.definition_names,
        challenge.provenance_comments,
    )
    entries, generated = read_entries(asm, tsv)

    rank = asm.module_ranks({e[1] for e in entries})
    entries.sort(key=lambda e: (rank.get(e[1], 999), e[2]))

    body = asm.emit(entries, generated)
    check_stale_tables(asm, challenge, entries)
    return body


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tsv", type=Path, help="TSV from extract_closure.lean")
    parser.add_argument(
        "--root",
        type=Path,
        default=Path.cwd(),
        help="repository root (default: current directory)",
    )
    parser.add_argument(
        "--challenge",
        default=DEFAULT_CHALLENGE,
        help=(
            "challenge name under challenges/, or a path to a configuration "
            f"file (default: {DEFAULT_CHALLENGE})"
        ),
    )
    parser.add_argument(
        "--split-dir",
        type=Path,
        default=None,
        help="write one challenge module per library module into this directory",
    )
    args = parser.parse_args()

    try:
        challenge = load_challenges([args.challenge])[0]
        if args.split_dir is not None:
            files = assemble_split(challenge, args.root, args.tsv)
            for rel, text in sorted(files.items()):
                dest = args.split_dir / rel
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_text(text, encoding="utf-8")
            print(f"wrote {len(files)} challenge files to {args.split_dir}")
            return 0
        print(assemble(challenge, args.root, args.tsv))
    except (ChallengeConfigError, StaleContextTables, DefinitionFrontierError) as exc:
        print(exc, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
