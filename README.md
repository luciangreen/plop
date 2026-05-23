# plop

Stage 1 implementation from `pr3.txt` is provided as a SWI-Prolog optimiser.

## Run tests

```bash
swipl -q -s tests/test_optimiser.pl -g run_tests -t halt
```

## Example

```bash
swipl -q -s optimiser.pl -g "optimise_file('examples/stage1_input.pl','out/stage1_output.pl')" -t halt
```
