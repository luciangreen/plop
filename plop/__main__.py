"""CLI entrypoint."""

from __future__ import annotations

import argparse
from pathlib import Path

from .stage1 import as_json


def main() -> None:
    parser = argparse.ArgumentParser(description="Run stage 1 parsing and analysis for Prolog source.")
    parser.add_argument("input", type=Path, help="Path to a Prolog source file")
    args = parser.parse_args()
    print(as_json(args.input))


if __name__ == "__main__":
    main()
