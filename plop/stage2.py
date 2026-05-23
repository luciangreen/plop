from __future__ import annotations

import argparse
import json
import re
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path

from .stage1 import (
    IRClause,
    analyse_clauses as analyse_stage1_clauses,
    parse_callable,
    parse_clause,
    split_clauses,
)

IS_GOAL_PATTERN = re.compile(r"^\s*([A-Z_][A-Za-z0-9_]*)\s+is\s+(.+?)\s*$")
VARIABLE_PATTERN = re.compile(r"\b([A-Z_][A-Za-z0-9_]*)\b")


@dataclass(frozen=True)
class FormulaDefinition:
    predicate: str
    head_name: str
    head_args: list[str]
    output_index: int
    output_var: str
    expression: str
    source: str
    kind: str


def parse_is_goal(goal: str) -> tuple[str, str] | None:
    match = IS_GOAL_PATTERN.fullmatch(goal.strip())
    if match is None:
        return None
    return match.group(1), match.group(2).strip()


def substitute_variables(expression: str, replacements: dict[str, str]) -> str:
    def replace(match: re.Match[str]) -> str:
        variable = match.group(1)
        replacement = replacements.get(variable)
        if replacement is None:
            return variable
        if replacement == variable:
            return variable
        return f"({replacement})"

    return VARIABLE_PATTERN.sub(replace, expression)


def format_clause(name: str, args: list[str], body: list[str]) -> str:
    head = f"{name}({','.join(args)})" if args else name
    if not body:
        return f"{head}."
    return f"{head}:- {', '.join(body)}."


def find_direct_formula(clause: IRClause) -> FormulaDefinition | None:
    if len(clause.body) != 1:
        return None
    parsed = parse_is_goal(clause.body[0])
    if parsed is None:
        return None
    output_var, expression = parsed
    if output_var not in clause.args:
        return None
    return FormulaDefinition(
        predicate=clause.signature,
        head_name=clause.name,
        head_args=clause.args,
        output_index=clause.args.index(output_var),
        output_var=output_var,
        expression=expression,
        source=clause.source,
        kind="direct_formula",
    )


def find_sum_to_n_formula(clauses: list[IRClause]) -> FormulaDefinition | None:
    if len(clauses) != 2:
        return None
    base_clause = next(
        (
            clause
            for clause in clauses
            if not clause.body and len(clause.args) == 2 and clause.args[0] == "0" and clause.args[1] == "0"
        ),
        None,
    )
    recursive_clause = next((clause for clause in clauses if clause.body), None)
    if base_clause is None or recursive_clause is None or len(recursive_clause.args) != 2:
        return None

    n_var, s_var = recursive_clause.args
    decremented_var: str | None = None
    recursive_result_var: str | None = None

    for goal in recursive_clause.body:
        is_goal = parse_is_goal(goal)
        if is_goal is not None:
            target, expression = is_goal
            if expression.replace(" ", "") == f"{n_var}-1":
                decremented_var = target
            continue
        parsed_goal = parse_callable(goal)
        if parsed_goal is None:
            continue
        name, args = parsed_goal
        if f"{name}/{len(args)}" != recursive_clause.signature:
            continue
        if len(args) != 2 or decremented_var is None:
            continue
        if args[0] != decremented_var:
            continue
        recursive_result_var = args[1]

    final_assignment = next(
        (
            parse_is_goal(goal)
            for goal in reversed(recursive_clause.body)
            if parse_is_goal(goal) is not None
        ),
        None,
    )
    if recursive_result_var is None or final_assignment is None:
        return None
    target, expression = final_assignment
    compact_expression = expression.replace(" ", "")
    if target != s_var or compact_expression not in {
        f"{recursive_result_var}+{n_var}",
        f"{n_var}+{recursive_result_var}",
    }:
        return None

    return FormulaDefinition(
        predicate=recursive_clause.signature,
        head_name=recursive_clause.name,
        head_args=recursive_clause.args,
        output_index=1,
        output_var=s_var,
        expression=f"{n_var}*({n_var}+1)//2",
        source=recursive_clause.source,
        kind="sum_formula",
    )


def collect_formula_definitions(predicate_clauses: dict[str, list[IRClause]]) -> dict[str, FormulaDefinition]:
    definitions: dict[str, FormulaDefinition] = {}
    for signature, clauses in predicate_clauses.items():
        if len(clauses) == 1:
            direct_formula = find_direct_formula(clauses[0])
            if direct_formula is not None:
                definitions[signature] = direct_formula
                continue
        sum_formula = find_sum_to_n_formula(clauses)
        if sum_formula is not None:
            definitions[signature] = sum_formula
    return definitions


def unfold_clause(clause: IRClause, formulas: dict[str, FormulaDefinition]) -> str | None:
    if not clause.body:
        return None

    derived: dict[str, str] = {}
    remaining_goals: list[str] = []
    unfolded = False

    for goal in clause.body:
        is_goal = parse_is_goal(goal)
        if is_goal is not None:
            target, expression = is_goal
            derived[target] = substitute_variables(expression, derived)
            remaining_goals.append(f"{target} is {derived[target]}")
            continue

        parsed_goal = parse_callable(goal)
        if parsed_goal is None:
            remaining_goals.append(goal)
            continue
        name, args = parsed_goal
        formula = formulas.get(f"{name}/{len(args)}")
        if formula is None:
            remaining_goals.append(goal)
            continue

        replacements = {
            formal: actual
            for index, (formal, actual) in enumerate(zip(formula.head_args, args))
            if index != formula.output_index
        }
        expression = substitute_variables(formula.expression, replacements)
        expression = substitute_variables(expression, derived)
        output_actual = args[formula.output_index]
        derived[output_actual] = expression
        unfolded = True

    if not unfolded:
        return None

    final_body: list[str] = []
    for goal in remaining_goals:
        is_goal = parse_is_goal(goal)
        if is_goal is None:
            final_body.append(goal)
            continue
        target, expression = is_goal
        final_body.append(f"{target} is {substitute_variables(expression, derived)}")

    if not final_body:
        head_output = next((arg for arg in reversed(clause.args) if arg in derived), None)
        if head_output is None:
            return None
        final_body = [f"{head_output} is {derived[head_output]}"]

    return format_clause(clause.name, clause.args, final_body)


def repeated_subcomputations(clauses: list[IRClause]) -> list[dict[str, object]]:
    repeated: list[dict[str, object]] = []
    for clause in clauses:
        counts = Counter(goal.strip() for goal in clause.body)
        for goal, count in sorted(counts.items()):
            if count > 1:
                repeated.append({"predicate": clause.signature, "goal": goal, "count": count})
    return repeated


def variable_reuse_opportunities(clauses: list[IRClause]) -> list[dict[str, object]]:
    opportunities: list[dict[str, object]] = []
    for clause in clauses:
        positions: dict[str, list[int]] = defaultdict(list)
        for index, goal in enumerate(clause.body):
            for variable in sorted(set(VARIABLE_PATTERN.findall(goal)) - {"_"}):
                positions[variable].append(index)
        for variable, indexes in sorted(positions.items()):
            if len(indexes) > 1:
                opportunities.append(
                    {
                        "predicate": clause.signature,
                        "variable": variable,
                        "goal_indexes": indexes,
                    }
                )
    return opportunities


def analyse_clauses(clauses: list[IRClause]) -> dict[str, object]:
    stage1_report = analyse_stage1_clauses(clauses)
    predicate_clauses: dict[str, list[IRClause]] = defaultdict(list)
    for clause in clauses:
        predicate_clauses[clause.signature].append(clause)

    formulas = collect_formula_definitions(predicate_clauses)
    unfolded = [
        {
            "predicate": clause.signature,
            "original": clause.source,
            "unfolded": unfolded_clause,
        }
        for clause in clauses
        if (unfolded_clause := unfold_clause(clause, formulas)) is not None
    ]

    memoisation_candidates = [
        {
            "predicate": signature,
            "memoised_name": f"memo_{signature.split('/')[0]}",
            "reason": "recursive predicate with reusable subcomputations",
        }
        for signature in stage1_report["recursive_predicates"]
    ]

    stage2_report = {
        "formula_predicates": {
            signature: {
                "kind": formula.kind,
                "expression": formula.expression,
                "output_variable": formula.output_var,
                "source": formula.source,
            }
            for signature, formula in sorted(formulas.items())
        },
        "unfolded_predicates": unfolded,
        "memoisation_candidates": memoisation_candidates,
        "repeated_subcomputations": repeated_subcomputations(clauses),
        "variable_reuse_opportunities": variable_reuse_opportunities(clauses),
    }

    return {**stage1_report, "stage2": stage2_report}


def analyse_source(source: str) -> dict[str, object]:
    return analyse_clauses([parse_clause(clause) for clause in split_clauses(source)])


def analyse_file(path: str | Path) -> dict[str, object]:
    return analyse_source(Path(path).read_text())


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run stage 2 unfolding and memoisation analysis on a Prolog source file.")
    parser.add_argument("path", help="Path to a Prolog source file")
    parser.add_argument("--indent", type=int, default=2, help="JSON indentation")
    args = parser.parse_args(argv)
    report = analyse_file(args.path)
    print(json.dumps(report, indent=args.indent, sort_keys=True))
    return 0
