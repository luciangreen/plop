from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path

from .stage1 import ENUMERATOR_GOALS, IRClause, parse_callable, parse_clause, split_clauses
from .stage2 import analyse_clauses as analyse_stage2_clauses


def enumerators_in_clause(clause: IRClause) -> set[str]:
    names: set[str] = set()
    for goal in clause.body:
        parsed = parse_callable(goal)
        if parsed is None:
            continue
        name, _ = parsed
        if name in ENUMERATOR_GOALS:
            names.add(name)
    return names


def enumerators_in_clause_text(clause_text: str) -> set[str]:
    clauses = [parse_clause(clause) for clause in split_clauses(clause_text)]
    return set().union(*(enumerators_in_clause(clause) for clause in clauses))


def _sorted_entries(values: dict[str, set[str]]) -> list[dict[str, str]]:
    return [
        {"predicate": predicate, "enumerator": enumerator}
        for predicate in sorted(values)
        for enumerator in sorted(values[predicate])
    ]


def analyse_clauses(clauses: list[IRClause]) -> dict[str, object]:
    base_report = analyse_stage2_clauses(clauses)
    predicates = base_report["predicates"]
    stage2_unfolded = base_report["stage2"]["unfolded_predicates"]

    original_by_predicate = {
        signature: set(details["enumerators"]) for signature, details in predicates.items()
    }
    unfolded_by_predicate: dict[str, set[str]] = {}
    for item in stage2_unfolded:
        unfolded_by_predicate[item["predicate"]] = enumerators_in_clause_text(item["unfolded"])

    created: dict[str, set[str]] = defaultdict(set)
    removed: dict[str, set[str]] = defaultdict(set)
    retained: dict[str, set[str]] = defaultdict(set)
    per_predicate: dict[str, dict[str, list[str]]] = {}

    for signature in sorted(original_by_predicate):
        original = original_by_predicate[signature]
        unfolded = unfolded_by_predicate.get(signature, original)
        created_names = unfolded - original
        removed_names = original - unfolded
        retained_names = original & unfolded

        if created_names:
            created[signature].update(created_names)
        if removed_names:
            removed[signature].update(removed_names)
        if retained_names:
            retained[signature].update(retained_names)

        per_predicate[signature] = {
            "created": sorted(created_names),
            "removed": sorted(removed_names),
            "retained": sorted(retained_names),
        }

    base_report["stage3"] = {
        "created_enumerators": _sorted_entries(created),
        "removed_enumerators": _sorted_entries(removed),
        "retained_enumerators": _sorted_entries(retained),
        "classifications_by_predicate": per_predicate,
    }
    return base_report


def analyse_source(source: str) -> dict[str, object]:
    return analyse_clauses([parse_clause(clause) for clause in split_clauses(source)])


def analyse_file(path: str | Path) -> dict[str, object]:
    return analyse_source(Path(path).read_text())


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run stage 3 enumerator optimization analysis on a Prolog source file.")
    parser.add_argument("path", help="Path to a Prolog source file")
    parser.add_argument("--indent", type=int, default=2, help="JSON indentation")
    args = parser.parse_args(argv)
    report = analyse_file(args.path)
    print(json.dumps(report, indent=args.indent, sort_keys=True))
    return 0
