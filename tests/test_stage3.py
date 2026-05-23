import json
import subprocess
import sys
import tempfile
import textwrap
import unittest

from plop import analyse_source
from plop.stage3 import analyse_source as analyse_stage3_source


SOURCE = textwrap.dedent(
    """
    member(X,Y):-
        Y is X+1.

    collector(X,Out):-
        member(X,T),
        Out is T.

    retained_pred(List,Pairs):-
        findall(X, member(X,List), Pairs).
    """
)


class Stage3AnalysisTests(unittest.TestCase):
    def test_stage3_classifies_removed_and_retained_enumerators(self) -> None:
        report = analyse_stage3_source(SOURCE)
        stage3 = report["stage3"]

        self.assertIn(
            {"predicate": "collector/2", "enumerator": "member"},
            stage3["removed_enumerators"],
        )
        self.assertIn(
            {"predicate": "retained_pred/2", "enumerator": "findall"},
            stage3["retained_enumerators"],
        )
        self.assertEqual(stage3["created_enumerators"], [])

    def test_default_cli_includes_stage3_output(self) -> None:
        report = analyse_source(SOURCE)
        self.assertIn("stage3", report)

        with tempfile.NamedTemporaryFile("w+", suffix=".pl") as handle:
            handle.write(SOURCE)
            handle.flush()
            output = subprocess.check_output(
                [sys.executable, "-m", "plop", handle.name],
                text=True,
            )

        cli_report = json.loads(output)
        self.assertIn("stage3", cli_report)
        self.assertIn("removed_enumerators", cli_report["stage3"])


if __name__ == "__main__":
    unittest.main()
