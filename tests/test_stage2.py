import json
import subprocess
import sys
import tempfile
import textwrap
import unittest

from plop import analyse_source
from plop.stage2 import analyse_source as analyse_stage2_source


SOURCE = textwrap.dedent(
    """
    inc(X,Y):-
        Y is X+1.

    double(X,Y):-
        Y is X*2.

    combined(X,Y):-
        inc(X,Z),
        double(Z,Y).

    sum_to_n(0,0).
    sum_to_n(N,S):-
        N>0,
        N1 is N-1,
        sum_to_n(N1,S1),
        S is S1+N.

    duplicated(N,Out):-
        inc(N,T),
        inc(N,T),
        Out is T.
    """
)


class Stage2AnalysisTests(unittest.TestCase):
    def test_stage2_detects_formulas_and_unfolding(self) -> None:
        report = analyse_stage2_source(SOURCE)

        formulas = report["stage2"]["formula_predicates"]
        self.assertEqual(formulas["inc/2"]["expression"], "X+1")
        self.assertEqual(formulas["sum_to_n/2"]["expression"], "N*(N+1)//2")

        unfolded = {
            item["predicate"]: item["unfolded"] for item in report["stage2"]["unfolded_predicates"]
        }
        self.assertEqual(unfolded["combined/2"], "combined(X,Y):- Y is (((X)+1))*2.")

        memoisation_candidates = report["stage2"]["memoisation_candidates"]
        self.assertEqual(memoisation_candidates[0]["memoised_name"], "memo_sum_to_n")

    def test_stage2_reports_repeated_subcomputations_and_cli_output(self) -> None:
        report = analyse_source(SOURCE)
        repeated = report["stage2"]["repeated_subcomputations"]
        self.assertIn(
            {"predicate": "duplicated/2", "goal": "inc(N,T)", "count": 2},
            repeated,
        )

        with tempfile.NamedTemporaryFile("w+", suffix=".pl") as handle:
            handle.write(SOURCE)
            handle.flush()
            output = subprocess.check_output(
                [sys.executable, "-m", "plop", handle.name],
                text=True,
            )

        cli_report = json.loads(output)
        self.assertIn("stage2", cli_report)
        self.assertIn("formula_predicates", cli_report["stage2"])


if __name__ == "__main__":
    unittest.main()
