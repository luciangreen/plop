:- begin_tests(hierarchical_splice).

:- use_module('../optimiser').

base_program([
    ir_clause(c1, expensive(X1, A1), [expensive_sub(X1, S1), finish(S1, A1)], []),
    ir_clause(c2, template1(X2, T1a), [expensive(X2, A2), T1a = row1(A2)], []),
    ir_clause(c3, template2(X3, T2a), [expensive(X3, A3), T2a = row2(A3)], []),
    ir_clause(c4, report(X4, Z4), [template1(X4, T14), template2(X4, T24), Z4 = [T14, T24]], []),
    ir_clause(c5, expensive_sub(X5, S5), [S5 is X5 * 10], []),
    ir_clause(c6, finish(S6, A6), [A6 is S6 + 1], [])
]).

test(two_templates_share_expensive) :-
    base_program(ProgramIR),
    optimise_program(ProgramIR, OptimisedIR, optimisation_report(Report)),
    member(ir_clause(_, report(X, Z), Body, _), OptimisedIR),
    assertion(shared_template_body(Body, X, Z, [row1, row2])),
    assertion(member(dependency_graph_built(report/2), Report)),
    assertion(member(common_dependency_hoisted(expensive/2, 2), Report)),
    assertion(member(hierarchical_spliced(report/2), Report)).

test(shared_subpredicate_inside_expensive) :-
    base_program(ProgramIR),
    optimise_program(ProgramIR, OptimisedIR, _),
    member(ir_clause(_, report(X, Z), Body, _), OptimisedIR),
    assertion(shared_template_body(Body, X, Z, [row1, row2])).

test(three_templates_share_expensive) :-
    base_program(Base),
    append(Base, [ir_clause(c7, template3(X, T3), [expensive(X, A), T3 = row3(A)], []),
                  ir_clause(c8, report3(X, Z), [template1(X, T1), template2(X, T2), template3(X, T3), Z = [T1, T2, T3]], [])], ProgramIR),
    optimise_program(ProgramIR, OptimisedIR, optimisation_report(Report)),
    member(ir_clause(_, report3(X, Z), Body, _), OptimisedIR),
    assertion(shared_template_body(Body, X, Z, [row1, row2, row3])),
    assertion(member(common_dependency_hoisted(expensive/2, 3), Report)).

test(skip_if_side_effect) :-
    ProgramIR = [
        ir_clause(c1, noisy(X1, A1), [read(A1), A1 = X1], []),
        ir_clause(c2, template1(X2, T12), [noisy(X2, A2), T12 = row1(A2)], []),
        ir_clause(c3, template2(X3, T23), [noisy(X3, A3), T23 = row2(A3)], []),
        ir_clause(c4, report(X4, Z4), [template1(X4, T14), template2(X4, T24), Z4 = [T14, T24]], [])
    ],
    optimise_program(ProgramIR, OptimisedIR, optimisation_report(Report)),
    member(ir_clause(_, report(_, _), Body, _), OptimisedIR),
    assertion(member(template1(_, _), Body)),
    assertion(member(template2(_, _), Body)),
    assertion(member(skipped_hierarchical_splice(report/2, side_effect), Report)).

test(skip_if_cut) :-
    ProgramIR = [
        ir_clause(c1, cutty(X1, A1), [A1 = X1, !], []),
        ir_clause(c2, template1(X2, T12), [cutty(X2, A2), T12 = row1(A2)], []),
        ir_clause(c3, template2(X3, T23), [cutty(X3, A3), T23 = row2(A3)], []),
        ir_clause(c4, report(X4, Z4), [template1(X4, T14), template2(X4, T24), Z4 = [T14, T24]], [])
    ],
    optimise_program(ProgramIR, _OptimisedIR, optimisation_report(Report)),
    assertion(member(skipped_hierarchical_splice(report/2, cut), Report)).

test(skip_if_nondeterministic) :-
    ProgramIR = [
        ir_clause(c1, expensive(X1, A1), [A1 is X1 + 1], []),
        ir_clause(c2, expensive(X2, A2), [A2 is X2 + 2], []),
        ir_clause(c3, template1(X3, T13), [expensive(X3, A3), T13 = row1(A3)], []),
        ir_clause(c4, template2(X4, T24), [expensive(X4, A4), T24 = row2(A4)], []),
        ir_clause(c5, report(X5, Z5), [template1(X5, T15), template2(X5, T25), Z5 = [T15, T25]], [])
    ],
    optimise_program(ProgramIR, _OptimisedIR, optimisation_report(Report)),
    assertion(member(skipped_hierarchical_splice(report/2, nondeterministic), Report)).

test(preserves_output_order) :-
    base_program(Base),
    append(Base, [ir_clause(c7, report_order(X, Z), [template2(X, T2), template1(X, T1), Z = [T2, T1]], [])], ProgramIR),
    optimise_program(ProgramIR, OptimisedIR, _),
    member(ir_clause(_, report_order(X, Z), Body, _), OptimisedIR),
    assertion(shared_template_body(Body, X, Z, [row2, row1])).

shared_template_body(Body, Input, OutputList, Constructors) :-
    append(Prefix, [OutputGoal], Body),
    Prefix = [SharedGoal | ConstructorGoals],
    length(ConstructorGoals, ConstructorCount),
    length(Constructors, ConstructorCount),
    shared_goal_uses_input(SharedGoal, Input),
    constructor_goals(ConstructorGoals, SharedValue, ConstructorVars, Constructors),
    OutputGoal = (OutputList = ConstructorVars),
    shared_goal_produces_value(SharedGoal, SharedValue),
    \+ member(expensive(_, _), Prefix),
    \+ member(template1(_, _), Prefix),
    \+ member(template2(_, _), Prefix),
    \+ member(template3(_, _), Prefix).

constructor_goals([], _SharedValue, [], []).
constructor_goals([Goal | Rest], SharedValue, [Var | Vars], [Ctor | Ctors]) :-
    Goal = (Var = Term),
    Term =.. [Ctor, SharedValue],
    constructor_goals(Rest, SharedValue, Vars, Ctors).

shared_goal_uses_input(Goal, Input) :-
    term_variables(Goal, Vars),
    member(Var, Vars),
    Var == Input.

shared_goal_produces_value(Goal, Value) :-
    term_variables(Goal, Vars),
    member(Value, Vars),
    Value \== Goal.

:- end_tests(hierarchical_splice).
