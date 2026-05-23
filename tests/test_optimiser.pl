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
