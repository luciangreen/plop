:- begin_tests(hierarchical_splice).

:- use_module('../optimiser').

base_program([
    ir_clause(c1, expensive(X, A), [expensive_sub(X, S), finish(S, A)], []),
    ir_clause(c2, template1(X, T1), [expensive(X, A), T1 = row1(A)], []),
    ir_clause(c3, template2(X, T2), [expensive(X, A), T2 = row2(A)], []),
    ir_clause(c4, report(X, Z), [template1(X, T1), template2(X, T2), Z = [T1, T2]], []),
    ir_clause(c5, expensive_sub(X, S), [S is X * 10], []),
    ir_clause(c6, finish(S, A), [A is S + 1], [])
]).

test(two_templates_share_expensive) :-
    base_program(ProgramIR),
    optimise_program(ProgramIR, OptimisedIR, optimisation_report(Report)),
    member(ir_clause(_, report(X, Z), Body, _), OptimisedIR),
    assertion(Body = [expensive_sub(X, S), finish(S, A), T1 = row1(A), T2 = row2(A), Z = [T1, T2]]),
    assertion(member(dependency_graph_built(report/2), Report)),
    assertion(member(common_dependency_hoisted(expensive/2, 2), Report)),
    assertion(member(hierarchical_spliced(report/2), Report)).

test(shared_subpredicate_inside_expensive) :-
    base_program(ProgramIR),
    optimise_program(ProgramIR, OptimisedIR, _),
    member(ir_clause(_, report(X, Z), Body, _), OptimisedIR),
    assertion(Body = [expensive_sub(X, S), finish(S, A), T1 = row1(A), T2 = row2(A), Z = [T1, T2]]).

test(three_templates_share_expensive) :-
    base_program(Base),
    append(Base, [ir_clause(c7, template3(X, T3), [expensive(X, A), T3 = row3(A)], []),
                  ir_clause(c8, report3(X, Z), [template1(X, T1), template2(X, T2), template3(X, T3), Z = [T1, T2, T3]], [])], ProgramIR),
    optimise_program(ProgramIR, OptimisedIR, optimisation_report(Report)),
    member(ir_clause(_, report3(X, Z), Body, _), OptimisedIR),
    assertion(Body = [expensive_sub(X, S), finish(S, A), T1 = row1(A), T2 = row2(A), T3 = row3(A), Z = [T1, T2, T3]]),
    assertion(member(common_dependency_hoisted(expensive/2, 3), Report)).

test(skip_if_side_effect) :-
    ProgramIR = [
        ir_clause(c1, noisy(X, A), [read(A), A = X], []),
        ir_clause(c2, template1(X, T1), [noisy(X, A), T1 = row1(A)], []),
        ir_clause(c3, template2(X, T2), [noisy(X, A), T2 = row2(A)], []),
        ir_clause(c4, report(X, Z), [template1(X, T1), template2(X, T2), Z = [T1, T2]], [])
    ],
    optimise_program(ProgramIR, OptimisedIR, optimisation_report(Report)),
    member(ir_clause(_, report(_, _), Body, _), OptimisedIR),
    assertion(Body \= [read(_), _ = _, _ = row1(_), _ = row2(_), _ = [_ , _]]),
    assertion(member(skipped_hierarchical_splice(report/2, side_effect), Report)).

test(skip_if_cut) :-
    ProgramIR = [
        ir_clause(c1, cutty(X, A), [A = X, !], []),
        ir_clause(c2, template1(X, T1), [cutty(X, A), T1 = row1(A)], []),
        ir_clause(c3, template2(X, T2), [cutty(X, A), T2 = row2(A)], []),
        ir_clause(c4, report(X, Z), [template1(X, T1), template2(X, T2), Z = [T1, T2]], [])
    ],
    optimise_program(ProgramIR, _OptimisedIR, optimisation_report(Report)),
    assertion(member(skipped_hierarchical_splice(report/2, cut), Report)).

test(skip_if_nondeterministic) :-
    ProgramIR = [
        ir_clause(c1, expensive(X, A), [A is X + 1], []),
        ir_clause(c2, expensive(X, A), [A is X + 2], []),
        ir_clause(c3, template1(X, T1), [expensive(X, A), T1 = row1(A)], []),
        ir_clause(c4, template2(X, T2), [expensive(X, A), T2 = row2(A)], []),
        ir_clause(c5, report(X, Z), [template1(X, T1), template2(X, T2), Z = [T1, T2]], [])
    ],
    optimise_program(ProgramIR, _OptimisedIR, optimisation_report(Report)),
    assertion(member(skipped_hierarchical_splice(report/2, nondeterministic), Report)).

test(preserves_output_order) :-
    base_program(Base),
    append(Base, [ir_clause(c7, report_order(X, Z), [template2(X, T2), template1(X, T1), Z = [T2, T1]], [])], ProgramIR),
    optimise_program(ProgramIR, OptimisedIR, _),
    member(ir_clause(_, report_order(X, Z), Body, _), OptimisedIR),
    assertion(Body = [expensive_sub(X, S), finish(S, A), T2 = row2(A), T1 = row1(A), Z = [T2, T1]]).

:- end_tests(hierarchical_splice).
