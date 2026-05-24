# plop

Implemented stages from `pr3.txt`:

- Stage 1: base-up data unfolding
- Stage 2: memoisation
- Stage 3: predicate-to-formula simplification
- Stage 4: enumerator analysis
- Stage 5: indexical mapping analysis
- Stage 6: subterm address system
- Stage 7: recursive index-loop analysis with `needed_subterms/3`
- Stage 8: Gaussian elimination formula discovery

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

## Example — stage 7 (recursive index-loop analysis)

`needed_subterms/3` reuses stage 6 addresses to fetch only requested nested values:

```prolog
?- needed_subterms(tree(tree(leaf(a), branch(b, c)), branch(d, e)),
                   [[1, 2, 1], [2, 2]],
                   Values).
Values = [b, e].
```
