# plop

Memoises, uses indexical optimisation, subterm with address, subterm-index looping and Gaussian elimination to optimise Prolog.

## Stage 1

Stage 1 from `pr1.txt` is implemented as a structural-analysis pass for Prolog source files. It:

- parses facts and rules into `ir_clause(Name, Args, Body)`-style records,
- identifies recursive predicates,
- flags enumerators, generators, accumulators, and reusable variables,
- detects deterministic predicates,
- recognises list-processing, matrix-processing, and nested subterm traversal patterns.

Run it with:

```bash
python -m plop /path/to/source.pl
```

The command prints a JSON report containing the internal representation and detected structural features.

## Stage 2

Stage 2 extends the report with:

- direct arithmetic formula detection,
- simple recursive sum-to-formula simplification,
- base-up unfolding of arithmetic helper predicates,
- memoisation candidates for recursive predicates,
- repeated subcomputation and variable-reuse signals.

The default CLI now runs the stage 2 pass and includes the stage 1 report alongside a `stage2` section.

## Stage 3

Stage 3 extends the report with enumerator optimisation signals by classifying enumerators as:

- created enumerators,
- removed enumerators,
- retained enumerators.

The default CLI now runs the stage 3 pass and includes stage 1 + stage 2 output plus a `stage3` section.

## Stage 4

Stage 4 extends the report with indexical optimisation signals by recording symbolic addresses and direct input-to-output mappings across:

- list indices,
- matrix indices,
- tree indices,
- nested subterm positions.

It also emits `subterm_with_address(...)` query forms and `addr(...)` rewrite candidates for index-based access.

The default CLI now runs the stage 4 pass and includes stage 1 + stage 2 + stage 3 output plus a `stage4` section.
