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

:- begin_tests(indexical).

:- use_module('../optimiser').
:- use_module('../indexical').

test(detects_matrix_style_nth1_chain) :-
    ProgramIR = [
        ir_clause(c1, lookup(Matrix, I, J, X), [nth1(I, Matrix, Row), nth1(J, Row, X)], [])
    ],
    optimise_indexicals(ProgramIR, OptimisedIR, Report),
    assertion(OptimisedIR = ProgramIR),
    assertion(member(indexical_mapping(lookup/4, addr([I, J], X)), Report)).

test(detects_nested_nth0_chain) :-
    ProgramIR = [
        ir_clause(c1, value(Term, I, J, K, X),
            [nth0(I, Term, A), nth0(J, A, B), nth0(K, B, X)],
            [])
    ],
    optimise_indexicals(ProgramIR, _OptimisedIR, Report),
    assertion(member(indexical_mapping(value/5, addr([I, J, K], X)), Report)).

test(optimise_program_includes_stage5_report_items) :-
    ProgramIR = [
        ir_clause(c1, lookup(Matrix, I, J, X), [nth1(I, Matrix, Row), nth1(J, Row, X)], [])
    ],
    optimise_program(ProgramIR, _OptimisedIR, optimisation_report(Report)),
    assertion(member(indexical_mapping(lookup/4, addr([I, J], X)), Report)).

test(does_not_emit_mapping_for_single_level_nth) :-
    ProgramIR = [
        ir_clause(c1, row(Matrix, I, Row), [nth1(I, Matrix, Row)], [])
    ],
    optimise_indexicals(ProgramIR, _OptimisedIR, Report),
    assertion(Report = []).

:- end_tests(indexical).

:- begin_tests(subterm_address).

:- use_module('../subterm_address').

test(subterm_with_address_matrix_style_lookup) :-
    subterm_with_address([[a, b], [c, d]], [2, 1], X),
    assertion(X == c).

test(subterm_with_address_compound_term_lookup) :-
    subterm_with_address(node(left(a), right(b)), [2, 1], X),
    assertion(X == b).

test(subterm_addresses_collects_nested_list_addresses) :-
    subterm_addresses([[a, b], [c]], Pairs),
    assertion(member([]-[[a, b], [c]], Pairs)),
    assertion(member([1]-[a, b], Pairs)),
    assertion(member([1, 2]-b, Pairs)),
    assertion(member([2]-[c], Pairs)),
    assertion(member([2, 1]-c, Pairs)).

test(subterm_with_address_fails_for_out_of_range_index, [fail]) :-
    subterm_with_address([x, y], [3], _).

:- end_tests(subterm_address).

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

:- begin_tests(recursive_index).

:- use_module('../optimiser').
:- use_module('../recursive_index').

test(extracts_multiple_subterms_by_address) :-
    needed_subterms(
        tree(tree(leaf(a), branch(b, c)), branch(d, e)),
        [[1, 2, 1], [2, 2]],
        Values
    ),
    assertion(Values == [b, e]).

test(detects_recursive_tree_traversal_pattern) :-
    ProgramIR = [
        ir_clause(c1, walk_tree(tree(Left, _), X), [walk_tree(Left, X)], []),
        ir_clause(c2, walk_tree(tree(_, branch(X, _)), X), [], [])
    ],
    optimise_recursive_index_loops(ProgramIR, OptimisedIR, Report),
    assertion(OptimisedIR = ProgramIR),
    assertion(member(recursive_index_mapping(walk_tree/2, addr([1, 2, 1], ReportValue)), Report)),
    assertion(var(ReportValue)).

test(optimise_program_includes_stage7_report_items) :-
    ProgramIR = [
        ir_clause(c1, walk_tree(tree(Left, _), X), [walk_tree(Left, X)], []),
        ir_clause(c2, walk_tree(tree(_, branch(X, _)), X), [], [])
    ],
    optimise_program(ProgramIR, _OptimisedIR, optimisation_report(Report)),
    assertion(member(recursive_index_mapping(walk_tree/2, addr([1, 2, 1], ReportValue)), Report)),
    assertion(var(ReportValue)).

test(does_not_report_non_recursive_index_pattern) :-
    ProgramIR = [
        ir_clause(c1, walk_tree(tree(_, branch(X, _)), X), [], [])
    ],
    optimise_recursive_index_loops(ProgramIR, _OptimisedIR, Report),
    assertion(Report = []).

:- end_tests(recursive_index).

:- begin_tests(list_formula).

:- use_module('../optimiser').
:- use_module('../list_formula').

test(rewrites_build_1_to_n_sum_list_to_formula) :-
    ProgramIR = [
        ir_clause(c1, seq_sum(N, S), [build_1_to_n(N, L), sum_list(L, S)], [])
    ],
    optimise_list_formulas(ProgramIR, OptimisedIR, Report),
    member(ir_clause(_, seq_sum(_, _), Body, _), OptimisedIR),
    assertion(Body = [S is N * (N + 1) // 2]),
    assertion(member(formula_discovered(seq_sum/2, n_times_n_plus_1_over_2), Report)).

test(rewrites_build_sequence_sum_list_to_formula) :-
    ProgramIR = [
        ir_clause(c1, seq_sum(N, Start, Step, S), [build_sequence(N, Start, Step, L), sum_list(L, S)], [])
    ],
    optimise_list_formulas(ProgramIR, OptimisedIR, Report),
    member(ir_clause(_, seq_sum(_, _, _, _), Body, _), OptimisedIR),
    assertion(Body = [S is N * (2 * Start + (N - 1) * Step) // 2]),
    assertion(member(formula_discovered(seq_sum/4, arithmetic_progression_sum), Report)).

test(does_not_rewrite_when_list_is_reused_elsewhere) :-
    ProgramIR = [
        ir_clause(c1, seq_sum(N, S, Len), [build_1_to_n(N, L), sum_list(L, S), length(L, Len)], [])
    ],
    optimise_list_formulas(ProgramIR, OptimisedIR, Report),
    member(ir_clause(_, seq_sum(_, _, _), Body, _), OptimisedIR),
    assertion(Body = [build_1_to_n(N, L), sum_list(L, S), length(L, Len)]),
    assertion(Report = []).

test(does_not_rewrite_when_list_escapes_in_head) :-
    ProgramIR = [
        ir_clause(c1, seq_sum(N, L, S), [build_1_to_n(N, L), sum_list(L, S)], [])
    ],
    optimise_list_formulas(ProgramIR, OptimisedIR, Report),
    member(ir_clause(_, seq_sum(_, _, _), Body, _), OptimisedIR),
    assertion(Body = [build_1_to_n(N, L), sum_list(L, S)]),
    assertion(Report = []).

test(optimise_program_includes_stage9_report_items) :-
    ProgramIR = [
        ir_clause(c1, seq_sum(N, S), [build_1_to_n(N, L), sum_list(L, S)], [])
    ],
    optimise_program(ProgramIR, _OptimisedIR, optimisation_report(Report)),
    assertion(member(formula_discovered(seq_sum/2, n_times_n_plus_1_over_2), Report)).

:- end_tests(list_formula).

:- begin_tests(gaussian).

:- use_module('../gaussian').

test(gaussian_eliminate_reduces_augmented_matrix) :-
    gaussian_eliminate(
        [
            [1, 1, 3],
            [1, -1, -1]
        ],
        Reduced
    ),
    assertion(Reduced = [[1, 0, 1], [0, 1, 2]]).

test(fit_polynomial_detects_identity_sequence) :-
    fit_polynomial([1, 2, 3, 4, 5], 1, Formula),
    assertion(Formula == n).

test(fit_polynomial_detects_triangular_sequence) :-
    fit_polynomial([1, 3, 6, 10, 15], 2, Formula),
    assertion(Formula = (n * (n + 1) / 2)).

:- end_tests(gaussian).

:- begin_tests(formula_discovery).

:- use_module('../formula_discovery').

test(infer_sequence_formula_finds_lowest_degree_match) :-
    infer_sequence_formula([1, 3, 5, 7, 9], Formula),
    assertion(Formula = (2 * n - 1)).

test(infer_sequence_formula_fails_for_empty_samples, [fail]) :-
    infer_sequence_formula([], _).

test(verify_formula_accepts_matching_sequence_predicate) :-
    verify_formula(test_sequence_triangular, n * (n + 1) / 2, 1-5).

test(verify_formula_rejects_wrong_formula, [fail]) :-
    verify_formula(test_sequence_identity, 2 * n - 1, 1-5).

test_sequence_triangular(N, Value) :-
    Value is N * (N + 1) / 2.

test_sequence_identity(N, N).

:- end_tests(formula_discovery).

:- begin_tests(loop_conversion).

:- use_module('../optimiser').
:- use_module('../loop_conversion').

test(converts_member_findall_to_deterministic_loop) :-
    ProgramIR = [
        ir_clause(c1, p(L, Ys), [findall(Y, (member(X, L), process(X, Y)), Ys)], [])
    ],
    convert_deterministic_loops(ProgramIR, OptimisedIR, Report),
    member(ir_clause(_, p(_, _), [HelperCall], _), OptimisedIR),
    functor(HelperCall, HelperName, 2),
    member(ir_clause(_, BaseHead, [], _), OptimisedIR),
    functor(BaseHead, HelperName, 2),
    member(ir_clause(_, StepHead, StepBody, _), OptimisedIR),
    functor(StepHead, HelperName, 2),
    assertion(member(loop_converted(p/2), Report)),
    assertion(StepBody = [process(_, _), _]).

test(converts_between_findall_to_deterministic_loop) :-
    ProgramIR = [
        ir_clause(c1, p(N, Ys), [findall(Y, (between(1, N, X), process(X, Y)), Ys)], [])
    ],
    convert_deterministic_loops(ProgramIR, OptimisedIR, Report),
    member(ir_clause(_, p(_, _), [HelperCall], _), OptimisedIR),
    functor(HelperCall, HelperName, 3),
    assertion(member(loop_converted(p/2), Report)),
    member(ir_clause(_, StepHead, StepBody, _), OptimisedIR),
    functor(StepHead, HelperName, 3),
    assertion(member(_ =< _, StepBody)),
    assertion(member(_ is _ + 1, StepBody)).

test(converts_nth0_findall_to_deterministic_loop) :-
    ProgramIR = [
        ir_clause(c1, p(L, Ys), [findall(Y, (nth0(I, L, X), pair(I, X, Y)), Ys)], [])
    ],
    convert_deterministic_loops(ProgramIR, OptimisedIR, Report),
    member(ir_clause(_, p(_, _), [HelperCall], _), OptimisedIR),
    functor(HelperCall, HelperName, 3),
    assertion(member(loop_converted(p/2), Report)),
    member(ir_clause(_, StepHead, StepBody, _), OptimisedIR),
    functor(StepHead, HelperName, 3),
    assertion(member(pair(_, _, _), StepBody)),
    assertion(member(_ is _ + 1, StepBody)).

test(does_not_convert_when_map_goal_uses_external_variable) :-
    ProgramIR = [
        ir_clause(c1, p(L, Offset, Ys), [findall(Y, (member(X, L), process(X, Offset, Y)), Ys)], [])
    ],
    convert_deterministic_loops(ProgramIR, OptimisedIR, Report),
    assertion(OptimisedIR = ProgramIR),
    assertion(Report = []).

test(optimise_program_includes_stage11_report_items) :-
    ProgramIR = [
        ir_clause(c1, p(L, Ys), [findall(Y, (member(X, L), process(X, Y)), Ys)], [])
    ],
    optimise_program(ProgramIR, _OptimisedIR, optimisation_report(Report)),
    assertion(member(loop_converted(p/2), Report)).

:- end_tests(loop_conversion).

:- begin_tests(splice).

:- use_module('../optimiser').
:- use_module('../splice').

test(splices_single_use_arithmetic_variable) :-
    ProgramIR = [
        ir_clause(c1, p(X, Y), [(A is X + 1), (Y is A * 2)], [])
    ],
    splice_program(ProgramIR, OptimisedIR, Report),
    member(ir_clause(_, p(_, _), Body, _), OptimisedIR),
    assertion(Body = [Y is (X + 1) * 2]),
    assertion(member(spliced(p/2), Report)).

test(splices_chain_of_single_use_variables) :-
    ProgramIR = [
        ir_clause(c1, q(X, Y), [(A is X + 1), (B is A * 2), (Y is B + 3)], [])
    ],
    splice_program(ProgramIR, OptimisedIR, Report),
    member(ir_clause(_, q(_, _), Body, _), OptimisedIR),
    assertion(Body = [Y is (X + 1) * 2 + 3]),
    assertion(member(spliced(q/2), Report)).

test(does_not_splice_multi_use_variable) :-
    ProgramIR = [
        ir_clause(c1, p(X, Y, Z), [(A is X + 1), (Y is A * 2), (Z is A + 3)], [])
    ],
    splice_program(ProgramIR, OptimisedIR, Report),
    member(ir_clause(_, p(_, _, _), Body, _), OptimisedIR),
    assertion(Body = [(A is X + 1), (Y is A * 2), (Z is A + 3)]),
    assertion(Report = []).

test(does_not_splice_variable_used_in_head) :-
    ProgramIR = [
        ir_clause(c1, p(X, A), [(A is X + 1), (writeln(A))], [])
    ],
    splice_program(ProgramIR, OptimisedIR, Report),
    member(ir_clause(_, p(_, _), Body, _), OptimisedIR),
    assertion(Body = [(A is X + 1), (writeln(A))]),
    assertion(Report = []).

test(optimise_program_includes_stage10_report_items) :-
    ProgramIR = [
        ir_clause(c1, p(X, Y), [(A is X + 1), (Y is A * 2)], [])
    ],
    optimise_program(ProgramIR, _OptimisedIR, optimisation_report(Report)),
    assertion(member(spliced(p/2), Report)).

:- end_tests(splice).
