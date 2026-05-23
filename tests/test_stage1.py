import json
import subprocess
import sys
import tempfile
import textwrap
import unittest

from plop.stage1 import analyse_source


SOURCE = textwrap.dedent(
    """
    sum_to_n(0,0).
    sum_to_n(N,S):-
        N>0,
        N1 is N-1,
        sum_to_n(N1,S1),
        S is S1+N.

    collect_pair(X,List,Pairs):-
        member(X,List),
        findall(Y, member(Y,List), Pairs).

    matrix_entry(I,J,Matrix,X):-
        nth1(I,Matrix,Row),
        nth1(J,Row,X).
    """
)


class Stage1AnalysisTests(unittest.TestCase):
    def test_structural_analysis_detects_stage1_signals(self) -> None:
        report = analyse_source(SOURCE)

        self.assertEqual(len(report["ir_clauses"]), 4)
        self.assertIn("sum_to_n/2", report["recursive_predicates"])
        self.assertIn("List", report["reusable_variables"])

        collect_pair = report["predicates"]["collect_pair/3"]
        self.assertEqual(collect_pair["enumerators"], ["findall", "member"])
        self.assertFalse(collect_pair["deterministic"])

        sum_to_n = report["predicates"]["sum_to_n/2"]
        self.assertIn("S", sum_to_n["accumulators"])

        matrix_entry = report["predicates"]["matrix_entry/4"]
        self.assertIn("nth1(I,Matrix,Row)", matrix_entry["matrix_processing_patterns"])
        self.assertEqual(
            report["nested_subterm_traversals"][0]["predicate"],
            "matrix_entry/4",
        )

    def test_cli_emits_json_report(self) -> None:
        with tempfile.NamedTemporaryFile("w+", suffix=".pl") as handle:
            handle.write(SOURCE)
            handle.flush()
            output = subprocess.check_output(
                [sys.executable, "-m", "plop", handle.name],
                text=True,
            )

        report = json.loads(output)
        self.assertIn("predicates", report)
        self.assertIn("sum_to_n/2", report["predicates"])


if __name__ == "__main__":
    unittest.main()
