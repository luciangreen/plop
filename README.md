# plop

```
README.md

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

addr([I,J], X)

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

Licence

BSD 3-Clause License.

Copyright © 2026 Lucian Green.
```