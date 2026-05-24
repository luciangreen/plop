:- module(formula_discovery, [infer_sequence_formula/2, verify_formula/3]).

:- use_module(gaussian, [fit_polynomial/3, polynomial_value/3, approximately_equal/2]).

:- meta_predicate verify_formula(2, +, +).

infer_sequence_formula(Samples, Formula) :-
    length(Samples, SampleCount),
    MaxDegree is max(0, SampleCount - 1),
    between(0, MaxDegree, Degree),
    fit_polynomial(Samples, Degree, Formula),
    !.

verify_formula(OriginalPredicate, Formula, Start-End) :-
    integer(Start),
    integer(End),
    Start =< End,
    forall(
        between(Start, End, N),
        (
            call(OriginalPredicate, N, Expected),
            formula_value(Formula, N, Actual),
            approximately_equal(Expected, Actual)
        )
    ).

formula_value(polynomial(Coefficients), N, Value) :-
    polynomial_value(Coefficients, N, Value).
formula_value(Formula, N, Value) :-
    substitute_n(Formula, N, GroundFormula),
    Value is GroundFormula.

substitute_n(n, N, N) :-
    !.
substitute_n(Term, _, Term) :-
    atomic(Term),
    !.
substitute_n(Term, N, GroundTerm) :-
    compound(Term),
    Term =.. [Functor | Args],
    maplist(substitute_n_with(N), Args, GroundArgs),
    GroundTerm =.. [Functor | GroundArgs].

substitute_n_with(N, Term, GroundTerm) :-
    substitute_n(Term, N, GroundTerm).
