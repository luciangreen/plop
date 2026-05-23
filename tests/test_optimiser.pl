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

test(optimise_file_writes_output, [setup(make_directory_path('out')), cleanup(delete_file('out/test_stage1_output.pl'))]) :-
    optimise_file('examples/stage1_input.pl', 'out/test_stage1_output.pl'),
    parse_file('out/test_stage1_output.pl', ProgramIR),
    member(ir_clause(_, combined(_, _), Body, _), ProgramIR),
    assertion(Body = [Y is (X + 1) * 2]).

:- end_tests(unfold).
