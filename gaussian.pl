:- module(gaussian, [
    fit_polynomial/3,
    gaussian_eliminate/2,
    polynomial_value/3,
    approximately_equal/2
]).

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
    Result is rationalize(Value / Divisor).

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
    Result is rationalize(Value - Factor * PivotValue).

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
    half(Half),
    (   Normalised = [0, 1]
    ->  Formula = n
    ;   Normalised = [-1, 2]
    ->  Formula = 2 * n - 1
    ;   Normalised = [0, Half, Half]
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
    ;   half(Half),
        approximately_equal(Coefficient, Half)
    ->  Normalised = Half
    ;   minus_half(MinusHalf),
        approximately_equal(Coefficient, MinusHalf)
    ->  Normalised = MinusHalf
    ;   Normalised = Coefficient
    ).

half(1 rdiv 2).
minus_half(-1 rdiv 2).

polynomial_value(Coefficients, N, Value) :-
    polynomial_value(Coefficients, N, 0, 0, Value).

polynomial_value([], _, _, Accumulator, Accumulator).
polynomial_value([Coefficient | Rest], N, Degree, Accumulator0, Value) :-
    Term is Coefficient * (N ^ Degree),
    Accumulator is Accumulator0 + Term,
    NextDegree is Degree + 1,
    polynomial_value(Rest, N, NextDegree, Accumulator, Value).

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
