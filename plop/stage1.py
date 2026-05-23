from __future__ import annotations

import argparse
import json
import re
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable


ENUMERATOR_GOALS = {
    "between",
    "findall",
    "forall",
    "maplist",
    "member",
    "memberchk",
    "nth0",
    "nth1",
    "bagof",
    "setof",
}

LIST_GOALS = {
    "append",
    "length",
    "maplist",
    "member",
    "memberchk",
    "nth0",
    "nth1",
    "reverse",
    "same_length",
    "select",
}

MATRIX_GOALS = {"nth0", "nth1", "transpose"}
SUBTERM_GOALS = {"arg", "nth0", "nth1"}
NONDET_GOALS = ENUMERATOR_GOALS | {"repeat"}
AGGREGATE_GOALS = {"bagof", "findall", "setof"}
VAR_PATTERN = re.compile(r"\b([A-Z_][A-Za-z0-9_]*)\b")


@dataclass(frozen=True)
class IRClause:
    name: str
    args: list[str]
    body: list[str]
    source: str

    @property
    def arity(self) -> int:
        return len(self.args)

    @property
    def signature(self) -> str:
        return f"{self.name}/{self.arity}"


def strip_comments(source: str) -> str:
    without_block = re.sub(r"/\*.*?\*/", "", source, flags=re.S)
    return re.sub(r"%.*$", "", without_block, flags=re.M)


def split_top_level(text: str, separator: str) -> list[str]:
    parts: list[str] = []
    current: list[str] = []
    depth_paren = depth_list = depth_brace = 0
    in_single = False
    in_double = False
    i = 0
    while i < len(text):
        char = text[i]
        next_chars = text[i : i + len(separator)]
        if char == "'" and not in_double:
            in_single = not in_single
        elif char == '"' and not in_single:
            in_double = not in_double
        elif not in_single and not in_double:
            if char == "(":
                depth_paren += 1
            elif char == ")":
                depth_paren -= 1
            elif char == "[":
                depth_list += 1
            elif char == "]":
                depth_list -= 1
            elif char == "{":
                depth_brace += 1
            elif char == "}":
                depth_brace -= 1
            elif (
                depth_paren == 0
                and depth_list == 0
                and depth_brace == 0
                and next_chars == separator
            ):
                parts.append("".join(current).strip())
                current = []
                i += len(separator)
                continue
        current.append(char)
        i += 1
    tail = "".join(current).strip()
    if tail:
        parts.append(tail)
    return parts


def split_clauses(source: str) -> list[str]:
    return [clause for clause in split_top_level(strip_comments(source), ".") if clause]


def split_rule(clause: str) -> tuple[str, str | None]:
    pieces = split_top_level(clause, ":-")
    if len(pieces) == 1:
        return pieces[0], None
    head = pieces[0]
    body = ":-".join(pieces[1:]).strip()
    return head, body


def parse_callable(term: str) -> tuple[str, list[str]] | None:
    term = term.strip()
    match = re.fullmatch(r"([a-z][A-Za-z0-9_]*)\((.*)\)", term)
    if match:
        return match.group(1), split_top_level(match.group(2), ",")
    if re.fullmatch(r"[a-z][A-Za-z0-9_]*", term):
        return term, []
    return None


def parse_clause(clause: str) -> IRClause:
    head_text, body_text = split_rule(clause)
    head = parse_callable(head_text)
    if head is None:
        raise ValueError(f"Unsupported clause head: {head_text}")
    name, args = head
    body = split_top_level(body_text, ",") if body_text else []
    return IRClause(name=name, args=args, body=body, source=clause.strip())


def extract_variables(fragment: str) -> list[str]:
    return [var for var in VAR_PATTERN.findall(fragment) if var != "_"]


def goal_signature(goal: str) -> str | None:
    parsed = parse_callable(goal)
    if parsed is not None:
        name, args = parsed
        return f"{name}/{len(args)}"
    return None


def is_recursive(signature: str, graph: dict[str, set[str]]) -> bool:
    stack = [signature]
    seen: set[str] = set()
    while stack:
        current = stack.pop()
        for neighbour in graph.get(current, set()):
            if neighbour == signature:
                return True
            if neighbour not in seen:
                seen.add(neighbour)
                stack.append(neighbour)
    return False


def analyse_clauses(clauses: Iterable[IRClause]) -> dict[str, object]:
    clause_list = list(clauses)
    call_graph: dict[str, set[str]] = defaultdict(set)
    predicate_clauses: dict[str, list[IRClause]] = defaultdict(list)

    for clause in clause_list:
        predicate_clauses[clause.signature].append(clause)
        for goal in clause.body:
            signature = goal_signature(goal)
            if signature is not None:
                call_graph[clause.signature].add(signature)

    recursive_predicates = sorted(
        signature for signature in predicate_clauses if is_recursive(signature, call_graph)
    )

    predicate_reports: dict[str, dict[str, object]] = {}
    reusable_variables: set[str] = set()
    nested_subterm_traversals: list[dict[str, object]] = []

    for signature, members in sorted(predicate_clauses.items()):
        enumerators: set[str] = set()
        generators: set[str] = set()
        accumulators: set[str] = set()
        list_patterns: set[str] = set()
        matrix_patterns: set[str] = set()
        deterministic = len(members) == 1

        for clause in members:
            body_var_counts = Counter(var for goal in clause.body for var in extract_variables(goal))
            reusable_variables.update(var for var, count in body_var_counts.items() if count > 1)

            for goal in clause.body:
                parsed_goal = parse_callable(goal)
                name = parsed_goal[0] if parsed_goal is not None else None
                if name in ENUMERATOR_GOALS:
                    enumerators.add(name)
                if name in AGGREGATE_GOALS or name in ENUMERATOR_GOALS:
                    generators.add(name)
                if any(op in goal for op in (" is ", "=:=", "=\\=", "<", ">", "=<", ">=")):
                    accumulators.update(var for var in extract_variables(goal) if var in clause.args)
                if name in LIST_GOALS or "[" in goal or any("[" in arg for arg in clause.args):
                    list_patterns.add(goal)
                if (
                    name in MATRIX_GOALS
                    or "[[" in goal
                    or any("[[" in arg for arg in clause.args)
                ):
                    matrix_patterns.add(goal)
                if name in NONDET_GOALS or ";" in goal:
                    deterministic = False

            parsed_goals = [parse_callable(goal) for goal in clause.body]
            for left, right in zip(parsed_goals, parsed_goals[1:]):
                if left is None or right is None:
                    continue
                left_name, left_args = left
                right_name, right_args = right
                if (
                    left_name in SUBTERM_GOALS
                    and right_name in SUBTERM_GOALS
                    and left_args
                    and right_args
                    and left_args[-1] == right_args[1]
                ):
                    nested_subterm_traversals.append(
                        {
                            "predicate": signature,
                            "path": [clause.body[parsed_goals.index(left)], clause.body[parsed_goals.index(right)]],
                        }
                    )

        predicate_reports[signature] = {
            "recursive": signature in recursive_predicates,
            "enumerators": sorted(enumerators),
            "accumulators": sorted(accumulators),
            "generators": sorted(generators),
            "deterministic": deterministic,
            "list_processing_patterns": sorted(list_patterns),
            "matrix_processing_patterns": sorted(matrix_patterns),
        }

    return {
        "ir_clauses": [asdict(clause) for clause in clause_list],
        "recursive_predicates": recursive_predicates,
        "reusable_variables": sorted(reusable_variables),
        "nested_subterm_traversals": nested_subterm_traversals,
        "predicates": predicate_reports,
    }


def analyse_source(source: str) -> dict[str, object]:
    return analyse_clauses(parse_clause(clause) for clause in split_clauses(source))


def analyse_file(path: str | Path) -> dict[str, object]:
    return analyse_source(Path(path).read_text())


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run stage 1 structural analysis on a Prolog source file.")
    parser.add_argument("path", help="Path to a Prolog source file")
    parser.add_argument("--indent", type=int, default=2, help="JSON indentation")
    args = parser.parse_args(argv)
    report = analyse_file(args.path)
    print(json.dumps(report, indent=args.indent, sort_keys=True))
    return 0
