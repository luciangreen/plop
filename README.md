# plop

`plop` is a SWI-Prolog source-to-source optimizer for symbolic and recursive
Prolog programs. It parses clauses into an intermediate representation (IR),
applies conservative transformations, and can write the optimized clauses to a
new file.

## Requirements

- SWI-Prolog 9 or newer
- Run commands from the repository root

## Quick start

Optimize an example:

```sh
swipl -q -s optimiser.pl \
  -g "optimiser:optimise_file('examples/stage1_input.pl','out/stage1_output.pl')" \
  -t halt
```

Inspect the result:

```sh
cat out/stage1_output.pl
```

Run the complete test suite, including hierarchical splicing:

```sh
swipl -q -s tests/run_tests.pl -g run_tests -t halt
```

Run one test group:

```sh
swipl -q -s tests/run_tests.pl -g "run_tests(indexical)" -t halt
```

The test groups are `unfold`, `memoise`, `simplify`, `indexical`,
`subterm_address`, `enumerators`, `recursive_index`, `list_formula`, `gaussian`,
`formula_discovery`, `loop_conversion`, `splice`, `safety`, `reporter`, and
`hierarchical_splice`.

## Features

| Feature | Behavior | Implementation |
|---|---|---|
| Base-up unfolding | Inlines eligible defined helper predicates; recursive and side-effecting helpers are retained. | `unfold.pl` |
| Dependency analysis | Builds predicate dependency information and hoists common dependencies shared by callers. | `dependency_graph.pl`, `common_dependency_hoist.pl` |
| Hierarchical splicing | Shares safe, deterministic subgoals across templates while preserving output order. | `hierarchical_splice.pl` |
| Memoization | Removes repeated calls with identical inputs when safe. | `memoise.pl` |
| Triangular-sum formula | Replaces the recognized recursive `sum_to_n/2` recurrence with a closed-form arithmetic goal. | `simplify.pl` |
| List-sum formulas | Replaces `build_1_to_n/2` or `build_sequence/4` followed by `sum_list/2` with arithmetic formulas when the list does not escape. | `list_formula.pl` |
| Indexical optimization | Rewrites nested `nth1/3` access chains to `subterm_with_address/3`, including compatible grouped output shapes. | `indexical.pl`, `grouped_subterms.pl` |
| Recursive index analysis | Reports address candidates for supported recursive traversals; `needed_subterms/3` fetches values at explicit addresses. | `recursive_index.pl`, `subterm_address.pl` |
| Shortcut splicing | Inlines single-use arithmetic temporaries without changing clause arguments. | `splice.pl` |
| Deterministic loop conversion | Converts supported `findall/3` patterns using `member/2`, `between/3`, `nth0/3`, or `nth1/3` into recursive helper predicates. | `loop_conversion.pl` |
| Enumerator analysis | Reports enumerators retained, removed, or created by optimization, and identifies indexical candidates. | `enumerators.pl` |
| Safety classification | Classifies goals as `safe`, `unsafe`, or `unknown`; unsafe or unknown changed predicates are restored by default. | `safety.pl` |
| Polynomial utilities | Fits polynomials with Gaussian elimination and infers/verifies sequence formulas. | `gaussian.pl`, `formula_discovery.pl` |
| Optimization reports | Returns structured report items and formats them as text. | `reporter.pl` |

`optimise_program/3` applies the stages in sequence and returns a report shaped
as `optimisation_report(Items)`. The program IR consists of
`ir_clause(Id, Head, Goals, Metadata)` terms.

## Common workflows

### Optimize a file or inspect the IR

```sh
swipl -q -s optimiser.pl \
  -g "optimiser:optimise_file('examples/sum_to_n.pl','out/sum_to_n_opt.pl')" \
  -t halt
```

In an interactive session:

```prolog
?- use_module(optimiser).
?- parse_file('examples/sum_to_n.pl', IR),
   optimise_program(IR, OptimisedIR, Report).
?- optimise_predicate(sum_to_n/2, IR, OptimisedIR, Report).
```

The main module exports `optimise_file/2`, `optimise_program/3`,
`optimise_predicate/4`, and `parse_file/2`.

### Allow experimental rewrites

The default safety policy restores any changed predicate containing an
`unsafe` or `unknown` goal. This commonly keeps transformations involving
undefined user predicates from being emitted. For controlled experiments:

```prolog
?- use_module(optimiser).
?- use_module(safety).
?- set_experimental_mode(true),
   optimise_file('examples/stage2_input.pl', 'out/stage2_output.pl').
?- set_experimental_mode(false).
```

Experimental mode is process-global. Turn it off again after the experiment.

### Work with indexical addresses

For nested list lookups, the optimizer can replace chains of `nth1/3` with an
address-based lookup. The generated code calls `subterm_with_address/3`; load
`subterm_address.pl` in the program that uses that output:

```prolog
?- use_module(subterm_address).
?- subterm_with_address([[a,b],[c,d]], [2,1], Value).
Value = c.
```

The standalone address utilities also include:

```prolog
?- subterm_addresses([[a,b],[c,d]], AddressValuePairs).
?- needed_subterms(tree(tree(leaf(a),branch(b,c)),branch(d,e)),
                   [[1,2,1],[2,2]], Values).
Values = [b,e].
```

### Discover and check sequence formulas

These are module utilities; they are not general-purpose automatic formula
rewrites for arbitrary program predicates:

```prolog
?- use_module(gaussian).
?- fit_polynomial([1,4,9,16,25], 2, Formula).
Formula = polynomial([0,0,1]).
```

```prolog
?- use_module(formula_discovery).
?- infer_sequence_formula([1,3,6,10,15], Formula).
?- verify_formula(test_sequence, 2*n-1, 1-5).
```

`verify_formula/3` calls the named two-argument predicate over the inclusive
integer range and compares its results with the supplied formula.

### Format an optimization report

```prolog
?- use_module(reporter).
?- report_text(optimisation_report([unfolded(p/2),memoised(p/3)]), Text).
Text = "unfolded: p/2\nmemoised: p/3".
```

## Current limitations and remaining work

There is no separate roadmap or declared backlog in the repository. The
following are current implementation boundaries and reasonable next features,
not promised release commitments:

- The recursive simplifier recognizes the exact triangular-sum recurrence;
  polynomial fitting and sequence inference are standalone utilities rather
  than general optimizer passes.
- List-sum rewriting recognizes only the two constructors documented above.
- Automatic indexical rewriting currently targets `nth1/3` chains; `nth0/3`
  chains are not rewritten.
- Recursive-index analysis reports candidates and provides address lookup, but
  does not yet rewrite arbitrary recursive predicates into specialized loops.
- Loop conversion accepts only the listed enumerators and restricted mapping
  goals. More general control flow and external variables are intentionally
  left unchanged.
- Safety has no user purity-annotation mechanism. Unknown calls are therefore
  conservative by default; experimental mode bypasses that final safety gate.
- The project currently has no packaging, configurable command-line interface,
  or benchmark suite.

## Repository layout

```text
optimiser.pl                 Optimization pipeline and public API
parser.pl                    Prolog source to IR parser
*.pl                         Optimization stages and analysis utilities
examples/                    Input programs for examples
tests/run_tests.pl           Combined PL-Unit test loader
tests/test_optimiser.pl       Main feature tests
tests/test_hierarchical_splice.pl
out/                         Example optimization outputs
```

## License

BSD 3-Clause License. Copyright © 2026 Lucian Green.
