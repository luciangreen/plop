:- module(gaussian, [
    fit_polynomial/3,
    gaussian_eliminate/2,
    infer_sequence_formula/2,
    verify_formula/3
]).

:- meta_predicate verify_formula(2, +, +).

fit_polynomial(Samples, Degree, Formula) :-
    valid_degree(Degree),
    length(Samples, SampleCount),
    RequiredSamples is Degree + 1,
    SampleCount >= RequiredSamples,
    basis_samples(Samples, RequiredSamples, BasisSamples),
    vandermonde_matrix(BasisSamples, Degree, Matrix),
    gaussian_eliminate(Matrix, ReducedMatrix),
    coefficients_from_reduced(ReducedMatrix, Coefficients),
    coefficients_fit_samples(Coefficients, Samples),
    coefficients_formula(Coefficients, Formula).

gaussian_eliminate(Matrix, ReducedMatrix) :-
    matrix_column_count(Matrix, ColumnCount),
    VariableCount is max(0, ColumnCount - 1),
    gauss_jordan([], Matrix, 1, VariableCount, ReducedRaw),
    maplist(sanitise_row, ReducedRaw, ReducedMatrix).

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

valid_degree(Degree) :-
    integer(Degree),
    Degree >= 0.

basis_samples(Samples, Count, Prefix) :-
    length(Prefix, Count),
    append(Prefix, _, Samples),
    !.

vandermonde_matrix(Samples, Degree, Matrix) :-
    vandermonde_matrix(Samples, Degree, 1, Matrix).

vandermonde_matrix([], _, _, []).
vandermonde_matrix([Sample | Rest], Degree, Index, [Row | MatrixRest]) :-
    polynomial_terms(Index, Degree, Terms),
    append(Terms, [Sample], Row),
    NextIndex is Index + 1,
    vandermonde_matrix(Rest, Degree, NextIndex, MatrixRest).

polynomial_terms(_, Degree, []) :-
    Degree < 0,
    !.
polynomial_terms(N, Degree, Terms) :-
    polynomial_terms(N, 0, Degree, Terms).

polynomial_terms(_, CurrentDegree, Degree, []) :-
    CurrentDegree > Degree,
    !.
polynomial_terms(N, CurrentDegree, Degree, [Term | Rest]) :-
    Term is N ^ CurrentDegree,
    NextDegree is CurrentDegree + 1,
    polynomial_terms(N, NextDegree, Degree, Rest).

matrix_column_count([Row | _], Count) :-
    length(Row, Count).

gauss_jordan(Processed, Remaining, Column, VariableCount, Result) :-
    (   Remaining = []
    ;   Column > VariableCount
    ),
    !,
    append(Processed, Remaining, Result).
gauss_jordan(Processed, Remaining, Column, VariableCount, Result) :-
    (   select_pivot_row(Remaining, Column, PivotRow, OtherRows)
    ->  normalise_pivot_row(PivotRow, Column, NormalisedPivot),
        eliminate_rows(Processed, Column, NormalisedPivot, UpdatedProcessed),
        eliminate_rows(OtherRows, Column, NormalisedPivot, UpdatedRemaining),
        append(UpdatedProcessed, [NormalisedPivot], NextProcessed),
        NextColumn is Column + 1,
        gauss_jordan(NextProcessed, UpdatedRemaining, NextColumn, VariableCount, Result)
    ;   NextColumn is Column + 1,
        gauss_jordan(Processed, Remaining, NextColumn, VariableCount, Result)
    ).

select_pivot_row([Row | Rest], Column, Row, Rest) :-
    nth1(Column, Row, Value),
    non_zero(Value),
    !.
select_pivot_row([Row | Rest], Column, PivotRow, [Row | Others]) :-
    select_pivot_row(Rest, Column, PivotRow, Others).

normalise_pivot_row(Row, Column, NormalisedRow) :-
    nth1(Column, Row, PivotValue),
    maplist(divide_by(PivotValue), Row, NormalisedRow).

divide_by(Divisor, Value, Result) :-
    Result is Value / Divisor.

eliminate_rows([], _, _, []).
eliminate_rows([Row | Rest], Column, PivotRow, [ReducedRow | ReducedRest]) :-
    nth1(Column, Row, Factor),
    eliminate_row(Row, Factor, PivotRow, ReducedRow),
    eliminate_rows(Rest, Column, PivotRow, ReducedRest).

eliminate_row(Row, Factor, PivotRow, ReducedRow) :-
    (   approximately_equal(Factor, 0)
    ->  ReducedRow = Row
    ;   maplist(subtract_scaled(Factor), Row, PivotRow, ReducedRaw),
        sanitise_row(ReducedRaw, ReducedRow)
    ).

subtract_scaled(Factor, Value, PivotValue, Result) :-
    Result is Value - Factor * PivotValue.

coefficients_from_reduced([], []).
coefficients_from_reduced([Row | Rest], [Coefficient | Coefficients]) :-
    append(_, [Coefficient], Row),
    coefficients_from_reduced(Rest, Coefficients).

coefficients_fit_samples(Coefficients, Samples) :-
    coefficients_fit_samples(Coefficients, Samples, 1).

coefficients_fit_samples(_, [], _).
coefficients_fit_samples(Coefficients, [Sample | Rest], N) :-
    polynomial_value(Coefficients, N, Value),
    approximately_equal(Value, Sample),
    NextN is N + 1,
    coefficients_fit_samples(Coefficients, Rest, NextN).

coefficients_formula(Coefficients, Formula) :-
    normalised_coefficients(Coefficients, Normalised),
    (   Normalised = [0, 1]
    ->  Formula = n
    ;   Normalised = [-1, 2]
    ->  Formula = 2 * n - 1
    ;   Normalised = [0, one_half, one_half]
    ->  Formula = n * (n + 1) / 2
    ;   Formula = polynomial(Normalised)
    ).

normalised_coefficients([], []).
normalised_coefficients([Coefficient | Rest], [Normalised | NormalisedRest]) :-
    normalise_coefficient(Coefficient, Normalised),
    normalised_coefficients(Rest, NormalisedRest).

normalise_coefficient(Coefficient, Normalised) :-
    (   approximately_equal(Coefficient, 0)
    ->  Normalised = 0
    ;   Rounded is round(Coefficient),
        approximately_equal(Coefficient, Rounded)
    ->  Normalised = Rounded
    ;   approximately_equal(Coefficient, 0.5)
    ->  Normalised = one_half
    ;   approximately_equal(Coefficient, -0.5)
    ->  Normalised = minus_one_half
    ;   Normalised = Coefficient
    ).

formula_value(polynomial(Coefficients), N, Value) :-
    coefficient_values(Coefficients, NumericCoefficients),
    polynomial_value(NumericCoefficients, N, Value).
formula_value(Formula, N, Value) :-
    substitute_n(Formula, N, GroundFormula),
    Value is GroundFormula.

coefficient_values([], []).
coefficient_values([Coefficient | Rest], [Numeric | NumericRest]) :-
    coefficient_value(Coefficient, Numeric),
    coefficient_values(Rest, NumericRest).

coefficient_value(one_half, 0.5).
coefficient_value(minus_one_half, -0.5).
coefficient_value(Value, Value).

polynomial_value(Coefficients, N, Value) :-
    polynomial_value(Coefficients, N, 0, 0, Value).

polynomial_value([], _, _, Accumulator, Accumulator).
polynomial_value([Coefficient | Rest], N, Degree, Accumulator0, Value) :-
    coefficient_value(Coefficient, NumericCoefficient),
    Term is NumericCoefficient * (N ^ Degree),
    Accumulator is Accumulator0 + Term,
    NextDegree is Degree + 1,
    polynomial_value(Rest, N, NextDegree, Accumulator, Value).

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

sanitise_row([], []).
sanitise_row([Value | Rest], [Sanitised | SanitisedRest]) :-
    sanitise_value(Value, Sanitised),
    sanitise_row(Rest, SanitisedRest).

sanitise_value(Value, 0) :-
    approximately_equal(Value, 0),
    !.
sanitise_value(Value, Rounded) :-
    Rounded is round(Value),
    approximately_equal(Value, Rounded),
    !.
sanitise_value(Value, Value).

non_zero(Value) :-
    \+ approximately_equal(Value, 0).

approximately_equal(A, B) :-
    Delta is abs(A - B),
    Delta =< 1.0e-9.
