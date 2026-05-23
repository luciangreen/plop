import json
import unittest

from plop.stage1 import analyze_stage1, build_ir_clauses, parse_prolog_source


SOURCE = """
sum_to_n(0, SumAcc) :- SumAcc is 0.
sum_to_n(N, SumAcc) :-
    N > 0,
    N1 is N - 1,
    sum_to_n(N1, Prev),
    SumAcc is Prev + N.

list_pick([H|_], H).

matrix_lookup(Matrix, I, J, X) :-
    nth1(I, Matrix, Row),
    nth1(J, Row, X).

generate_pair(N, Pair) :-
    findall(X, between(1, N, X), Pair).
"""


class Stage1Tests(unittest.TestCase):
    def test_parse_and_ir_build(self) -> None:
        clauses = parse_prolog_source(SOURCE)
        self.assertGreaterEqual(len(clauses), 5)
        ir = build_ir_clauses(clauses)
        self.assertEqual(ir[0].name, "sum_to_n")
        self.assertEqual(ir[0].args, ["0", "SumAcc"])

    def test_stage1_analysis(self) -> None:
        report = analyze_stage1(SOURCE)
        self.assertEqual(report["stage"], 1)
        self.assertIn("sum_to_n/2", report["recursive_predicates"])
        self.assertIn("sum_to_n/2", report["accumulators"])
        self.assertIn("matrix_lookup/4", report["enumerators"])
        self.assertIn("generate_pair/2", report["generators"])
        self.assertIn("list_pick/2", report["list_patterns"])
        self.assertIn("matrix_lookup/4", report["matrix_patterns"])
        self.assertIn("matrix_lookup/4", report["nested_subterm_traversals"])
        self.assertIn("sum_to_n/2", report["reusable_variables"])

    def test_report_is_json_serializable(self) -> None:
        report = analyze_stage1(SOURCE)
        encoded = json.dumps(report, sort_keys=True)
        self.assertTrue(encoded.startswith("{"))


if __name__ == "__main__":
    unittest.main()
