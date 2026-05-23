# plop

Stage 1 (base-up data unfolding), stage 2 (memoisation), stage 3 (predicate-to-formula simplification), and stage 4 (enumerator analysis) from `pr3.txt` are implemented as a SWI-Prolog optimiser.

## Run tests

```bash
swipl -q -s tests/test_optimiser.pl -g run_tests -t halt
```

## Example — stage 1 (unfolding)

```bash
swipl -q -s optimiser.pl -g "optimise_file('examples/stage1_input.pl','out/stage1_output.pl')" -t halt
```

## Example — stage 2 (memoisation)

```bash
swipl -q -s optimiser.pl -g "optimise_file('examples/stage2_input.pl','out/stage2_output.pl')" -t halt
```

Duplicate calls to `expensive/2` in `p/3` are detected and the redundant call is removed, with its output variable unified with that of the first call.

## Example — stage 3 (predicate-to-formula simplification)

```bash
swipl -q -s optimiser.pl -g "optimise_file('examples/sum_to_n.pl','out/sum_to_n_opt.pl')" -t halt
```

`sum_to_n/2` recursion is rewritten to:

```prolog
sum_to_n(N,S) :-
    S is N*(N+1)//2.
```
