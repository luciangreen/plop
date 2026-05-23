import json
import subprocess
import sys
import tempfile
import textwrap
import unittest

from plop import analyse_source
from plop.stage4 import analyse_source as analyse_stage4_source


SOURCE = textwrap.dedent(
    """
    matrix_entry(I,J,Matrix,X):-
        nth1(I,Matrix,Row),
        nth1(J,Row,X).

    tree_child(I,Tree,X):-
        arg(I,Tree,X).

    deep_item(I,J,K,Data,X):-
        nth0(I,Data,Row),
        nth0(J,Row,Cell),
        arg(K,Cell,X).
    """
)


class Stage4AnalysisTests(unittest.TestCase):
    def test_stage4_records_indexical_signals(self) -> None:
        report = analyse_stage4_source(SOURCE)
        stage4 = report["stage4"]

        self.assertIn("list_indices", stage4)
        self.assertIn("matrix_indices", stage4)
        self.assertIn("tree_indices", stage4)
        self.assertIn("nested_subterm_positions", stage4)

        self.assertIn(
            {
                "predicate": "matrix_entry/4",
                "matrix_term": "Matrix",
                "address": ["I", "J"],
                "value_term": "X",
                "goals": ["nth1(I,Matrix,Row)", "nth1(J,Row,X)"],
            },
            stage4["matrix_indices"],
        )

        self.assertIn(
            {
                "predicate": "tree_child/3",
                "goal": "arg(I,Tree,X)",
                "tree_term": "Tree",
                "index": "I",
                "subterm": "X",
                "index_base": 1,
            },
            stage4["tree_indices"],
        )

        self.assertIn(
            {
                "predicate": "deep_item/5",
                "input_term": "Data",
                "address": ["I", "J", "K"],
                "output_term": "X",
                "goals": ["nth0(I,Data,Row)", "nth0(J,Row,Cell)", "arg(K,Cell,X)"],
            },
            stage4["nested_subterm_positions"],
        )

        self.assertIn(
            "subterm_with_address(Matrix, [I, J], X)",
            stage4["subterm_with_address_queries"],
        )

    def test_default_cli_includes_stage4_output(self) -> None:
        report = analyse_source(SOURCE)
        self.assertIn("stage4", report)

        with tempfile.NamedTemporaryFile("w+", suffix=".pl") as handle:
            handle.write(SOURCE)
            handle.flush()
            output = subprocess.check_output(
                [sys.executable, "-m", "plop", handle.name],
                text=True,
            )

        cli_report = json.loads(output)
        self.assertIn("stage4", cli_report)
        self.assertIn("nested_subterm_positions", cli_report["stage4"])


if __name__ == "__main__":
    unittest.main()
