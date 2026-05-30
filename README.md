# plop

Optimiser

Optimiser is a SWI-Prolog source-to-source optimiser for symbolic and recursive Prolog programs.

It analyses Prolog predicates and rewrites selected computations into simpler, faster, deterministic forms where safe.

Implemented stages include:

* base-up unfolding
* memoisation
* predicate-to-formula simplification
* enumerator analysis
* indexical optimisation
* subterm-address indexing
* recursive index-loop analysis
* Gaussian elimination formula discovery
* list-manipulation-to-formula optimisation
* shortcut splicing
* hierarchical shared-subgoal splicing
* deterministic loop conversion
* safety classification
* optimisation reporting

Repository contents include modules such as optimiser.pl, memoise.pl, gaussian.pl, loop_conversion.pl, and recursive_index.pl.  ￼

⸻

Requirements

* SWI-Prolog 9+
* Unix/macOS/Linux/WSL recommended

⸻

Repository Structure

optimiser/
  optimiser.pl
  parser.pl
  unfold.pl
  memoise.pl
  simplify.pl
  enumerators.pl
  indexical.pl
  recursive_index.pl
  subterm_address.pl
  gaussian.pl
  formula_discovery.pl
  list_formula.pl
  loop_conversion.pl
  splice.pl
  safety.pl
  reporter.pl
  examples/
  tests/
  out/

⸻

Quick Start

Run the optimiser

swipl -q -s optimiser.pl

⸻

Main Commands

Optimise a Prolog file

swipl -q -s optimiser.pl \
  -g "optimise_file('examples/sum_to_n.pl','out/sum_to_n_opt.pl')" \
  -t halt

Expected output file:

sum_to_n(N,S) :-
    S is N*(N+1)//2.

⸻

Optimise a program already parsed into IR

?- parse_file('examples/sum_to_n.pl', IR),
   optimise_program(IR, OptimisedIR, Report).

⸻

Optimise a single predicate

?- parse_file('examples/stage2_input.pl', IR),
   optimise_predicate(p/3, IR, OptimisedIR, Report).

⸻

Run Tests

Run all tests:

swipl -q -s tests/test_optimiser.pl \
  -g run_tests \
  -t halt

Run a specific test group:

swipl -q -s tests/test_optimiser.pl \
  -g "run_tests(gaussian)" \
  -t halt

⸻

Example Optimisations

Stage 1 — Base-Up Unfolding

Input:

inc(X,Y) :- Y is X+1.
double(X,Y) :- Y is X*2.
combined(X,Y) :-
    inc(X,A),
    double(A,Y).

Run:

swipl -q -s optimiser.pl \
  -g "optimise_file('examples/stage1_input.pl','out/stage1_output.pl')" \
  -t halt

Output:

combined(X,Y) :-
    Y is (X+1)*2.

⸻

Stage 2 — Memoisation

Input:

p(X,Y,Z) :-
    expensive(X,A),
    expensive(X,B),
    Y is A+1,
    Z is B+2.

Run:

swipl -q -s optimiser.pl \
  -g "optimise_file('examples/stage2_input.pl','out/stage2_output.pl')" \
  -t halt

Output:

p(X,Y,Z) :-
    expensive(X,A),
    Y is A+1,
    Z is A+2.

⸻

Stage 3 — Formula Discovery

Run:

swipl -q -s optimiser.pl \
  -g "optimise_file('examples/sum_to_n.pl','out/sum_to_n_opt.pl')" \
  -t halt

Output:

sum_to_n(N,S) :-
    S is N*(N+1)//2.

⸻

Stage 18 — Hierarchical Shared-Subgoal Splicing

Input:

```prolog
expensive(X, A) :-
    expensive_sub(X, S),
    finish(S, A).

template1(X, T1) :-
    expensive(X, A),
    T1 = row1(A).

template2(X, T2) :-
    expensive(X, A),
    T2 = row2(A).

report(X, Z) :-
    template1(X, T1),
    template2(X, T2),
    Z = [T1,T2].
```

Run:

```sh
swipl -q -s optimiser.pl \
  -g "optimise_file('examples/hierarchical_splice_input.pl', \
                    'out/hierarchical_splice_output.pl')" \
  -t halt
```

Output:

```prolog
report(X, Z) :-
    expensive_sub(X, S),
    finish(S, A),
    T1 = row1(A),
    T2 = row2(A),
    Z = [T1,T2].
```

⸻

Gaussian Formula Discovery

Infer a sequence formula

?- infer_sequence_formula([1,3,6,10,15], Formula).

Expected:

Formula = n*(n+1)/2.

⸻

Fit a polynomial

?- fit_polynomial([1,4,9,16,25], 2, Formula).

Expected:

Formula = polynomial([0,0,1]).

⸻

Verify a discovered formula

?- verify_formula(sum_to_n, n*(n+1)/2, 1-100).

⸻

Indexical Optimisation

Detect matrix-style indexing

Input pattern:

nth1(I, Matrix, Row),
nth1(J, Row, X)

Internal representation:

addr(Matrix, [I,J], X)

⸻

Run indexical analysis

?- parse_file('examples/matrix_lookup.pl', IR),
   optimise_program(IR, _, Report).

⸻

Subterm Address System

Query nested data

?- subterm_with_address([[a,b],[c,d]], [2,1], X).

Expected:

X = c.

⸻

Extract all addresses

?- subterm_addresses([[a,b],[c,d]], Pairs).

⸻

Recursive Index Loop Analysis

Fetch only required nested values

?- needed_subterms(
       tree(tree(leaf(a), branch(b,c)), branch(d,e)),
       [[1,2,1],[2,2]],
       Values
   ).

Expected:

Values = [b,e].

⸻

Optimisation Reports

Print optimisation report text

swipl -q -s reporter.pl \
  -g "report_text(optimisation_report([unfolded(p/2),memoised(p/3)]),T),writeln(T)" \
  -t halt

Example output:

unfolded: p/2
memoised: p/3

⸻

Safety System

The optimiser classifies rewrites as:

safe
unsafe
unknown

Unsafe rewrites are skipped unless experimental mode is enabled.

⸻

Enable experimental mode

?- set_experimental_mode(true).

Disable experimental mode

?- set_experimental_mode(false).

⸻

Output Files

Optimised output files are written into:

out/

Examples:

out/stage1_output.pl
out/stage2_output.pl
out/sum_to_n_opt.pl

⸻

Example Full Workflow

swipl -q -s optimiser.pl \
  -g "parse_file('examples/sum_to_n.pl',IR),
      optimise_program(IR,OptIR,Report),
      print(Report)" \
  -t halt


⸻

Input:

matrix_output(Matrix, Output) :-

    nth1(1, Matrix, Row1),

    nth1(1, Row1, A),

    nth1(2, Row1, B),

    nth1(2, Matrix, Row2),

    nth1(1, Row2, C),

    Output = [[A,B], C].
    
Use this for the final optimised file:

swipl -q -s optimiser.pl \
  -g "optimiser:optimise_file('examples/matrix_reconstruct.pl','out/matrix_reconstruct_opt.pl')" \
  -t halt

Then view it:

cat out/matrix_reconstruct_opt.pl

Expected output shape:

matrix_output(A,B) :-
    subterm_with_address(A,[1],[C,D]),
    subterm_with_address(A,[2,1],F),
    B=[[C,D],F].
    
⸻

ND→D Loop-Splice Class System

The ND→D (nondeterminism-to-determinism) system classifies every Prolog predicate into one of 13 structural classes and decides whether it can be safely converted to a deterministic accumulator loop, map, fold, flatmap, filter, or spliced multi-accumulator loop.

Classes

| Class | Meaning |
|---|---|
| `deterministic` | No choicepoints; already deterministic |
| `enumerator` | Generates solutions via `member/2` or backtracking; use as generator only |
| `map_compatible` | `findall`-based map; convert to `maplist/3` or explicit accumulator loop |
| `fold_compatible` | Accumulator recursion; convert to `foldl/4` or explicit fold loop |
| `flatmap_compatible` | `findall` over expanding generator; convert to nested loop |
| `filter_compatible` | Conditional `findall`; convert to explicit filter loop |
| `splice_compatible` | Multiple `findall` calls over same list; fuse into single shared loop |
| `dependent_nested_loop` | Nested `findall` with shared variable; requires careful hoisting |
| `hoistable_expensive_dependency` | Expensive pure subgoal inside loop; safe to hoist before loop |
| `memo_safe_expensive_dependency` | Unknown-cost subgoal; add memoisation table |
| `unknown_cost_dependency` | Cannot determine cost statically; emit warning |
| `unsafe_nondeterminism` | Contains side-effectful goals (`write`, `assert`, `retract`) or cut; do **not** transform |
| `requires_interpreter_construct` | Uses `call/N` or meta-call; cannot inline |

Running the Classifier

```prolog
swipl -q -s nd_classify.pl -g "nd_classify_program(P,Classified,Report), print_term(Classified,[]), halt" examples/nd_class_input.pl
```

Loop Splice Example

Input (`examples/loop_splice_input.pl`):

```prolog
collect(List, Words, Lengths) :-
    findall(W, (member(W, List), atom(W)), Words),
    findall(L, (member(E, List), atom_length(E, L)), Lengths).
```

Running the loop-splice optimiser:

```
swipl -q -s loop_splice.pl -g "loop_splice_program(P,Out,Report), print_term(Out,[]), halt" examples/loop_splice_input.pl
```

Expected output — two `findall` templates over the same list fused into a single loop:

```prolog
collect(List, Words, Lengths) :-
    loop_splice(List, [W,L], [(atom(W)),(atom_length(E,L))], Words, Lengths).
```

Report example:

```prolog
report(nd_splice_converted, collect/3, [templates(2), list_var('List')]).
```

Expensive Dependency Analysis

Subgoals inside loops are classified and optionally hoisted or memoised:

- `pure_deterministic_expensive` → hoist before loop
- `impure_expensive` → block transformation (`must_not_hoist`)
- `recursive_expensive` → add memoisation table
- `memo_safe_unknown` → suggest memoisation

MNN Signature Index

A O(1) pattern-signature index (`mnn_signature.pl`) lets the pipeline classify and dispatch common patterns instantly, falling back to the full structural classifier only for unknown patterns.

Safety Note

The ND→D system **never** transforms a predicate classified as `unsafe_nondeterminism` or `requires_interpreter_construct` unless experimental mode is enabled via `set_experimental_mode(true)`. All other classes are converted conservatively, preserving answer order and duplicates.

⸻

Licence

BSD 3-Clause License.

Copyright © 2026 Lucian Green.