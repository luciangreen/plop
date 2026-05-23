:- begin_tests(unfold).

:- use_module('../optimiser').
:- use_module('../parser').

test(unfolds_simple_helpers_with_splicing) :-
    ProgramIR = [
        ir_clause(c1, inc(X, Y), [Y is X + 1], []),
        ir_clause(c2, double(X, Y), [Y is X * 2], []),
        ir_clause(c3, combined(X, Y), [inc(X, A), double(A, Y)], [])
    ],
    optimise_program(ProgramIR, OptimisedIR, optimisation_report(Report)),
    member(ir_clause(_, combined(_, _), Body, _), OptimisedIR),
    assertion(Body = [Y is (X + 1) * 2]),
    assertion(member(unfolded(combined/2), Report)).

test(does_not_unfold_recursive_helper) :-
    ProgramIR = [
        ir_clause(c1, loop(X, Y), [loop(X, Y)], []),
        ir_clause(c2, caller(X, Y), [loop(X, Y)], [])
    ],
    optimise_program(ProgramIR, OptimisedIR, _),
    member(ir_clause(_, caller(_, _), Body, _), OptimisedIR),
    assertion(Body = [loop(_, _)]).

test(does_not_unfold_side_effect_helper) :-
    ProgramIR = [
        ir_clause(c1, noisy(X), [writeln(X)], []),
        ir_clause(c2, caller(X), [noisy(X)], [])
    ],
    optimise_program(ProgramIR, OptimisedIR, _),
    member(ir_clause(_, caller(_), Body, _), OptimisedIR),
    assertion(Body = [noisy(_)]).

test(optimise_file_writes_output, [setup(make_directory_path('out')), cleanup(cleanup_output_file)]) :-
    output_file_path(OutputPath),
    optimise_file('examples/stage1_input.pl', OutputPath),
    parse_file(OutputPath, ProgramIR),
    member(ir_clause(_, combined(_, _), Body, _), ProgramIR),
    assertion(Body = [Y is (X + 1) * 2]).

cleanup_output_file :-
    output_file_path(OutputPath),
    (   exists_file(OutputPath)
    ->  delete_file(OutputPath)
    ;   true
    ).

output_file_path('out/test_stage1_output.pl').

:- end_tests(unfold).

:- begin_tests(memoise).

:- use_module('../optimiser').
:- use_module('../memoise').

test(deduplicates_repeated_call) :-
    ProgramIR = [
        ir_clause(c1, p(X, Y, Z),
            [expensive(X, A), expensive(X, B), (Y is A + 1), (Z is B + 2)],
            [])
    ],
    memoise_program(ProgramIR, OptimisedIR, Report),
    member(ir_clause(_, p(_, _, _), Body, _), OptimisedIR),
    assertion(length(Body, 3)),
    assertion(Body = [expensive(X, A), (Y is A + 1), (Z is A + 2)]),
    assertion(member(memoised(p/3), Report)).

test(does_not_deduplicate_different_inputs) :-
    ProgramIR = [
        ir_clause(c1, q(X1, X2, Y1, Y2),
            [compute(X1, Y1), compute(X2, Y2)],
            [])
    ],
    memoise_program(ProgramIR, OptimisedIR, Report),
    member(ir_clause(_, q(_, _, _, _), Body, _), OptimisedIR),
    assertion(length(Body, 2)),
    assertion(Report = []).

test(does_not_memoise_io_goals) :-
    ProgramIR = [
        ir_clause(c1, p(X), [writeln(X), writeln(X)], [])
    ],
    memoise_program(ProgramIR, OptimisedIR, Report),
    member(ir_clause(_, p(_), Body, _), OptimisedIR),
    assertion(length(Body, 2)),
    assertion(Report = []).

test(optimise_program_applies_memoisation) :-
    ProgramIR = [
        ir_clause(c1, r(X, Y, Z),
            [expensive(X, A), expensive(X, B), (Y is A + 1), (Z is B + 2)],
            [])
    ],
    optimise_program(ProgramIR, OptimisedIR, optimisation_report(Report)),
    member(ir_clause(_, r(_, _, _), Body, _), OptimisedIR),
    assertion(length(Body, 3)),
    assertion(member(memoised(r/3), Report)).

:- end_tests(memoise).

:- begin_tests(simplify).

:- use_module('../optimiser').
:- use_module('../simplify').

test(rewrites_sum_to_n_to_formula) :-
    ProgramIR = [
        ir_clause(c1, sum_to_n(0, 0), [], []),
        ir_clause(c2, sum_to_n(N, S),
            [N > 0, N1 is N - 1, sum_to_n(N1, S1), S is S1 + N],
            [])
    ],
    simplify_program(ProgramIR, OptimisedIR, Report),
    include(sum_to_n_clause, OptimisedIR, SumClauses),
    assertion(length(SumClauses, 1)),
    SumClauses = [ir_clause(_, sum_to_n(_, _), Body, _)],
    assertion(Body = [S is N * (N + 1) // 2]),
    assertion(member(formula_discovered(sum_to_n/2, n_times_n_plus_1_over_2), Report)).

test(does_not_rewrite_non_matching_recursive_numeric_predicate) :-
    ProgramIR = [
        ir_clause(c1, bad_sum(0, 0), [], []),
        ir_clause(c2, bad_sum(N, S),
            [N > 0, N1 is N - 1, bad_sum(N1, S1), S is S1 + (N * 2)],
            [])
    ],
    simplify_program(ProgramIR, OptimisedIR, Report),
    include(bad_sum_clause, OptimisedIR, BadSumClauses),
    assertion(length(BadSumClauses, 2)),
    assertion(Report = []).

test(optimise_program_applies_stage3_formula_simplification) :-
    ProgramIR = [
        ir_clause(c1, sum_to_n(0, 0), [], []),
        ir_clause(c2, sum_to_n(N, S),
            [N > 0, N1 is N - 1, sum_to_n(N1, S1), S is S1 + N],
            [])
    ],
    optimise_program(ProgramIR, OptimisedIR, optimisation_report(Report)),
    include(sum_to_n_clause, OptimisedIR, SumClauses),
    assertion(length(SumClauses, 1)),
    assertion(member(formula_discovered(sum_to_n/2, n_times_n_plus_1_over_2), Report)).

sum_to_n_clause(ir_clause(_, Head, _, _)) :-
    functor(Head, sum_to_n, 2).

bad_sum_clause(ir_clause(_, Head, _, _)) :-
    functor(Head, bad_sum, 2).

:- end_tests(simplify).

:- begin_tests(enumerators).

:- use_module('../optimiser').
:- use_module('../enumerators').

test(classifies_retained_enumerator) :-
    ProgramIR = [
        ir_clause(c1, p(N, S), [between(1, N, I), S is I], [])
    ],
    analyse_enumerators(ProgramIR, ProgramIR, Report),
    assertion(member(enumerator(retained, p/2, between/3), Report)).

test(classifies_removed_enumerators) :-
    BeforeIR = [
        ir_clause(c1, seq_sum(N, S), [findall(I, between(1, N, I), L), sum_list(L, S)], [])
    ],
    AfterIR = [
        ir_clause(c2, seq_sum(N, S), [S is N * (N + 1) // 2], [])
    ],
    analyse_enumerators(BeforeIR, AfterIR, Report),
    assertion(member(enumerator(removed, seq_sum/2, between/3), Report)),
    assertion(member(enumerator(removed, seq_sum/2, findall/3), Report)).

test(classifies_created_enumerator) :-
    BeforeIR = [
        ir_clause(c1, p(_), [], [])
    ],
    AfterIR = [
        ir_clause(c2, p(X), [member(X, [1, 2, 3])], [])
    ],
    analyse_enumerators(BeforeIR, AfterIR, Report),
    assertion(member(enumerator(created, p/1, member/2), Report)).

test(distinguishes_indexical_patterns_from_enumerators) :-
    ProgramIR = [
        ir_clause(c1, lookup(Matrix, I, J, X), [nth1(I, Matrix, Row), nth1(J, Row, X)], [])
    ],
    analyse_enumerators(ProgramIR, ProgramIR, Report),
    assertion(member(indexical_candidate(lookup/4, nth1/3), Report)),
    assertion(\+ member(enumerator(_, lookup/4, nth1/3), Report)).

test(optimise_program_includes_stage4_report_items) :-
    ProgramIR = [
        ir_clause(c1, p(X), [member(X, [a, b, c])], [])
    ],
    optimise_program(ProgramIR, _OptimisedIR, optimisation_report(Report)),
    assertion(member(enumerator(retained, p/1, member/2), Report)).

:- end_tests(enumerators).
