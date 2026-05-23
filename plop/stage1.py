"""Stage 1: parsing and analysis for Prolog source."""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from pathlib import Path
import json
import re
from typing import Iterable


@dataclass(frozen=True)
class IRClause:
    """Simple stage-1 IR clause."""

    name: str
    args: tuple[str, ...]
    body: tuple[str, ...]
    raw: str


_VAR_RE = re.compile(r"\b([A-Z][A-Za-z0-9_]*)\b")
_HEAD_RE = re.compile(r"^\s*([a-z][A-Za-z0-9_]*)\s*(?:\((.*)\))?\s*$")
_PRED_CALL_RE = re.compile(r"^\s*([a-z][A-Za-z0-9_]*)\s*(?:\((.*)\))?\s*$")
_ENUM_FUNCTORS = {"member", "between", "nth1", "nth0"}
_GEN_FUNCTORS = {"findall", "bagof", "setof"}


def _strip_comments(source: str) -> str:
    return "\n".join(line.split("%", 1)[0] for line in source.splitlines())


def _split_top_level(text: str, delimiter: str) -> list[str]:
    parts: list[str] = []
    start = 0
    depth_paren = 0
    depth_bracket = 0
    for idx, ch in enumerate(text):
        if ch == "(":
            depth_paren += 1
        elif ch == ")":
            depth_paren -= 1
        elif ch == "[":
            depth_bracket += 1
        elif ch == "]":
            depth_bracket -= 1
        elif ch == delimiter and depth_paren == 0 and depth_bracket == 0:
            parts.append(text[start:idx].strip())
            start = idx + 1
    parts.append(text[start:].strip())
    return [part for part in parts if part]


def parse_prolog_source(source: str | Path) -> list[str]:
    """Parse Prolog source into normalized raw clause strings."""

    content = Path(source).read_text(encoding="utf-8") if isinstance(source, Path) else source
    cleaned = _strip_comments(content)
    return _split_top_level(cleaned, ".")


def _predicate_signature(goal: str) -> tuple[str, int] | None:
    match = _PRED_CALL_RE.match(goal)
    if not match:
        return None
    name = match.group(1)
    arg_blob = match.group(2)
    args = _split_top_level(arg_blob, ",") if arg_blob else []
    return name, len(args)


def call_args(goal: str) -> str:
    match = _PRED_CALL_RE.match(goal)
    return match.group(2) if match and match.group(2) else ""


def build_ir_clauses(raw_clauses: Iterable[str]) -> list[IRClause]:
    """Build IR clauses from raw clause strings."""

    ir: list[IRClause] = []
    for raw in raw_clauses:
        clause_text = raw.strip()
        if not clause_text:
            continue
        if ":-" in clause_text:
            head_text, body_text = clause_text.split(":-", 1)
        else:
            head_text, body_text = clause_text, ""
        head_match = _HEAD_RE.match(head_text.strip())
        if not head_match:
            continue
        name = head_match.group(1)
        arg_blob = head_match.group(2)
        args = tuple(_split_top_level(arg_blob, ",")) if arg_blob else ()
        body = tuple(_split_top_level(body_text, ",")) if body_text else ()
        ir.append(IRClause(name=name, args=args, body=body, raw=clause_text))
    return ir


def detect_recursive_predicates(ir_clauses: Iterable[IRClause]) -> list[str]:
    recursive: set[str] = set()
    for clause in ir_clauses:
        signature = f"{clause.name}/{len(clause.args)}"
        for goal in clause.body:
            call = _predicate_signature(goal)
            if call and call == (clause.name, len(clause.args)):
                recursive.add(signature)
    return sorted(recursive)


def detect_enumerators(ir_clauses: Iterable[IRClause]) -> list[str]:
    matches: set[str] = set()
    for clause in ir_clauses:
        for goal in clause.body:
            call = _predicate_signature(goal)
            if call and call[0] in _ENUM_FUNCTORS:
                matches.add(f"{clause.name}/{len(clause.args)}")
    return sorted(matches)


def detect_accumulators(ir_clauses: Iterable[IRClause]) -> list[str]:
    matches: set[str] = set()
    for clause in ir_clauses:
        if not any(_predicate_signature(goal) == (clause.name, len(clause.args)) for goal in clause.body):
            continue
        if any(re.search(r"\bis\b", goal) for goal in clause.body) and any(
            marker in arg.casefold() for arg in clause.args for marker in ("acc", "sum", "total", "out")
        ):
            matches.add(f"{clause.name}/{len(clause.args)}")
    return sorted(matches)


def detect_generators(ir_clauses: Iterable[IRClause]) -> list[str]:
    matches: set[str] = set()
    for clause in ir_clauses:
        for goal in clause.body:
            call = _predicate_signature(goal)
            if call and call[0] in _GEN_FUNCTORS:
                matches.add(f"{clause.name}/{len(clause.args)}")
    return sorted(matches)


def detect_reusable_variables(ir_clauses: Iterable[IRClause]) -> dict[str, list[str]]:
    reusable: dict[str, list[str]] = {}
    for clause in ir_clauses:
        counts = Counter(_VAR_RE.findall(clause.raw))
        shared = sorted(var for var, count in counts.items() if count > 1)
        if shared:
            reusable[f"{clause.name}/{len(clause.args)}"] = shared
    return reusable


def detect_list_patterns(ir_clauses: Iterable[IRClause]) -> list[str]:
    matches: set[str] = set()
    for clause in ir_clauses:
        joined = " ".join([*clause.args, *clause.body])
        if "[" in joined and "]" in joined:
            matches.add(f"{clause.name}/{len(clause.args)}")
    return sorted(matches)


def detect_matrix_patterns(ir_clauses: Iterable[IRClause]) -> list[str]:
    matches: set[str] = set()
    for clause in ir_clauses:
        has_nested_nth1 = False
        previous_row_var = None
        for goal in clause.body:
            call = _predicate_signature(goal)
            if call and call[0] == "nth1":
                nth1_args = _split_top_level(call_args(goal), ",")
                if len(nth1_args) >= 3:
                    source = nth1_args[1].strip()
                    row = nth1_args[2].strip()
                    if previous_row_var and source == previous_row_var:
                        has_nested_nth1 = True
                    previous_row_var = row
        if has_nested_nth1:
            matches.add(f"{clause.name}/{len(clause.args)}")
    return sorted(matches)


def detect_nested_subterm_traversals(ir_clauses: Iterable[IRClause]) -> list[str]:
    matches: set[str] = set()
    for clause in ir_clauses:
        for idx in range(len(clause.body) - 1):
            first_call = _predicate_signature(clause.body[idx])
            second_call = _predicate_signature(clause.body[idx + 1])
            if not first_call or not second_call:
                continue
            if first_call[0] in {"nth1", "arg"} and second_call[0] in {"nth1", "arg"}:
                first_call_args = _split_top_level(call_args(clause.body[idx]), ",")
                second_call_args = _split_top_level(call_args(clause.body[idx + 1]), ",")
                if (
                    len(first_call_args) >= 3
                    and len(second_call_args) >= 2
                    and first_call_args[2].strip() == second_call_args[1].strip()
                ):
                    matches.add(f"{clause.name}/{len(clause.args)}")
    return sorted(matches)


def analyze_stage1(source: str | Path) -> dict[str, object]:
    """Run full stage-1 analysis."""

    raw_clauses = parse_prolog_source(source)
    ir_clauses = build_ir_clauses(raw_clauses)
    return {
        "stage": 1,
        "name": "parsing_and_analysis",
        "clauses": [clause.__dict__ for clause in ir_clauses],
        "recursive_predicates": detect_recursive_predicates(ir_clauses),
        "enumerators": detect_enumerators(ir_clauses),
        "accumulators": detect_accumulators(ir_clauses),
        "generators": detect_generators(ir_clauses),
        "reusable_variables": detect_reusable_variables(ir_clauses),
        "list_patterns": detect_list_patterns(ir_clauses),
        "matrix_patterns": detect_matrix_patterns(ir_clauses),
        "nested_subterm_traversals": detect_nested_subterm_traversals(ir_clauses),
    }


def as_json(source: str | Path) -> str:
    return json.dumps(analyze_stage1(source), indent=2, sort_keys=True)
