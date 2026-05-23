from __future__ import annotations

import argparse
import json
from pathlib import Path

from .stage1 import IRClause, parse_callable, parse_clause, split_clauses
from .stage3 import analyse_clauses as analyse_stage3_clauses

INDEX_GOALS = {"nth0", "nth1", "arg"}


def _index_base(goal_name: str) -> int:
    return 0 if goal_name == "nth0" else 1


def _sorted_dicts(rows: list[dict[str, object]], keys: tuple[str, ...]) -> list[dict[str, object]]:
    return sorted(rows, key=lambda row: tuple(str(row[key]) for key in keys))


def _join_address(parts: list[str]) -> str:
    return "[" + ", ".join(parts) + "]"


def analyse_clauses(clauses: list[IRClause]) -> dict[str, object]:
    base_report = analyse_stage3_clauses(clauses)

    list_indices: list[dict[str, object]] = []
    matrix_indices: list[dict[str, object]] = []
    tree_indices: list[dict[str, object]] = []
    nested_subterm_positions: list[dict[str, object]] = []
    input_output_address_mappings: list[dict[str, object]] = []
    subterm_with_address_queries: list[str] = []
    addr_rewrites: list[dict[str, str]] = []

    for clause in clauses:
        parsed_goals: list[tuple[int, str, list[str], str]] = []
        for index, goal_text in enumerate(clause.body):
            parsed = parse_callable(goal_text)
            if parsed is None:
                continue
            name, args = parsed
            parsed_goals.append((index, name, args, goal_text))

            if name in {"nth0", "nth1"} and len(args) >= 3:
                list_indices.append(
                    {
                        "predicate": clause.signature,
                        "goal": goal_text,
                        "list_term": args[1],
                        "index": args[0],
                        "element": args[2],
                        "index_base": _index_base(name),
                    }
                )

            if name == "arg" and len(args) >= 3:
                tree_indices.append(
                    {
                        "predicate": clause.signature,
                        "goal": goal_text,
                        "tree_term": args[1],
                        "index": args[0],
                        "subterm": args[2],
                        "index_base": 1,
                    }
                )

        for start in range(len(parsed_goals)):
            _, name, args, goal_text = parsed_goals[start]
            if name not in INDEX_GOALS or len(args) < 3:
                continue

            address = [args[0]]
            goals = [goal_text]
            input_term = args[1]
            output_term = args[2]
            chain_names = [name]

            cursor = start + 1
            while cursor < len(parsed_goals):
                _, next_name, next_args, next_goal = parsed_goals[cursor]
                if next_name not in INDEX_GOALS or len(next_args) < 3:
                    break
                if next_args[1] != output_term:
                    break
                address.append(next_args[0])
                goals.append(next_goal)
                output_term = next_args[2]
                chain_names.append(next_name)
                cursor += 1

            if len(address) > 1:
                position = {
                    "predicate": clause.signature,
                    "input_term": input_term,
                    "address": address,
                    "output_term": output_term,
                    "goals": goals,
                }
                nested_subterm_positions.append(position)
                input_output_address_mappings.append(
                    {
                        "predicate": clause.signature,
                        "kind": "nested_subterm",
                        "input_term": input_term,
                        "address": address,
                        "output_term": output_term,
                    }
                )
                subterm_with_address_queries.append(
                    f"subterm_with_address({input_term}, {_join_address(address)}, {output_term})"
                )

                if all(chain_name in {"nth0", "nth1"} for chain_name in chain_names):
                    matrix_indices.append(
                        {
                            "predicate": clause.signature,
                            "matrix_term": input_term,
                            "address": address,
                            "value_term": output_term,
                            "goals": goals,
                        }
                    )
                    addr_rewrites.append(
                        {
                            "predicate": clause.signature,
                            "addr": f"addr({_join_address(address)},{output_term})",
                        }
                    )
                    input_output_address_mappings.append(
                        {
                            "predicate": clause.signature,
                            "kind": "matrix",
                            "input_term": input_term,
                            "address": address,
                            "output_term": output_term,
                        }
                    )

        for entry in list_indices:
            if entry["predicate"] != clause.signature:
                continue
            input_output_address_mappings.append(
                {
                    "predicate": clause.signature,
                    "kind": "list",
                    "input_term": entry["list_term"],
                    "address": [entry["index"]],
                    "output_term": entry["element"],
                }
            )
            subterm_with_address_queries.append(
                f"subterm_with_address({entry['list_term']}, [{entry['index']}], {entry['element']})"
            )

        for entry in tree_indices:
            if entry["predicate"] != clause.signature:
                continue
            input_output_address_mappings.append(
                {
                    "predicate": clause.signature,
                    "kind": "tree",
                    "input_term": entry["tree_term"],
                    "address": [entry["index"]],
                    "output_term": entry["subterm"],
                }
            )
            subterm_with_address_queries.append(
                f"subterm_with_address({entry['tree_term']}, [{entry['index']}], {entry['subterm']})"
            )

    deduped_queries = sorted(set(subterm_with_address_queries))
    deduped_mappings = []
    seen_mappings: set[tuple[str, str, str, str, str]] = set()
    for mapping in input_output_address_mappings:
        key = (
            str(mapping["predicate"]),
            str(mapping["kind"]),
            str(mapping["input_term"]),
            ",".join(str(part) for part in mapping["address"]),
            str(mapping["output_term"]),
        )
        if key in seen_mappings:
            continue
        seen_mappings.add(key)
        deduped_mappings.append(mapping)

    base_report["stage4"] = {
        "list_indices": _sorted_dicts(
            list_indices,
            ("predicate", "goal", "list_term", "index", "element"),
        ),
        "matrix_indices": _sorted_dicts(
            matrix_indices,
            ("predicate", "matrix_term", "value_term"),
        ),
        "tree_indices": _sorted_dicts(
            tree_indices,
            ("predicate", "goal", "tree_term", "index", "subterm"),
        ),
        "nested_subterm_positions": _sorted_dicts(
            nested_subterm_positions,
            ("predicate", "input_term", "output_term"),
        ),
        "input_output_address_mappings": _sorted_dicts(
            deduped_mappings,
            ("predicate", "kind", "input_term", "output_term"),
        ),
        "subterm_with_address_queries": deduped_queries,
        "addr_rewrites": _sorted_dicts(addr_rewrites, ("predicate", "addr")),
    }
    return base_report


def analyse_source(source: str) -> dict[str, object]:
    return analyse_clauses([parse_clause(clause) for clause in split_clauses(source)])


def analyse_file(path: str | Path) -> dict[str, object]:
    return analyse_source(Path(path).read_text())


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run stage 4 indexical optimization analysis on a Prolog source file.")
    parser.add_argument("path", help="Path to a Prolog source file")
    parser.add_argument("--indent", type=int, default=2, help="JSON indentation")
    args = parser.parse_args(argv)
    report = analyse_file(args.path)
    print(json.dumps(report, indent=args.indent, sort_keys=True))
    return 0
