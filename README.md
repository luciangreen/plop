# plop

Stage 1 implementation for `pr2.txt`: parsing and analysis of Prolog source.

## What stage 1 provides

- Parse Prolog clauses from source text/files
- Build IR clause records (`name`, `args`, `body`, `raw`)
- Detect:
  - recursive predicates
  - enumerators
  - accumulators
  - generators
  - reusable variables
  - list patterns
  - matrix patterns
  - nested subterm traversals

## CLI usage

```bash
python -m plop /path/to/source.pl
```

The command prints a JSON stage-1 analysis report.

## Tests

```bash
python -m unittest discover -s tests -v
```
