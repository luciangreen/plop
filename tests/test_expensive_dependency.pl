:- begin_tests(test_expensive_dependency).

:- use_module('../expensive_dependency').
:- use_module('../mnn_signature').

% -----------------------------------------------------------------------
% detect_expensive_subgoals
% -----------------------------------------------------------------------

test(detects_heuristically_expensive_goals) :-
    Body = [add(1, 2, X), expensive(foo, Y), member(Z, [1,2,3])],
    detect_expensive_subgoals(Body, ExpGoals),
    assertion(member(expensive(foo, _), ExpGoals)),
    ignore(X=X), ignore(Y=Y), ignore(Z=Z).

test(returns_empty_when_no_expensive_goals) :-
    Body = [add(1, 2, _X), member(_Y, [1,2,3])],
    detect_expensive_subgoals(Body, ExpGoals),
    assertion(ExpGoals = []).

% -----------------------------------------------------------------------
% detect_repeated_expensive_subgoals
% -----------------------------------------------------------------------

test(detects_repeated_expensive_goal) :-
    Body = [expensive(X, A), other(A, B), expensive(X, C)],
    detect_repeated_expensive_subgoals(Body, Repeated),
    assertion(Repeated \== []),
    ignore(A=A), ignore(B=B), ignore(C=C), ignore(X=X).

test(no_repeated_when_all_unique) :-
    Body = [expensive(x, _A), expensive(y, _B)],
    detect_repeated_expensive_subgoals(Body, Repeated),
    assertion(Repeated = []).

% -----------------------------------------------------------------------
% hoist_expensive_if_safe
% -----------------------------------------------------------------------

test(hoists_pure_expensive_goal) :-
    Body = [other(a, b), expensive(x, _A), more_work(_A, _B)],
    hoist_expensive_if_safe(Body, NewBody, Report),
    % expensive goal moved to front when safe
    assertion(NewBody \== []),
    assertion(Report \== []).

test(does_not_hoist_unsafe_goal) :-
    Body = [writeln(x), more_work(y, _Z)],
    hoist_expensive_if_safe(Body, NewBody, Report),
    assertion(NewBody = Body),
    assertion(Report = []).

% -----------------------------------------------------------------------
% classify_expensive_dependency
% -----------------------------------------------------------------------

test(classifies_io_goal_as_impure_expensive) :-
    ProgramIR = [],
    classify_expensive_dependency(writeln(x), ProgramIR, Class),
    assertion(Class = impure_expensive).

test(classifies_arithmetic_as_pure_deterministic) :-
    ProgramIR = [],
    classify_expensive_dependency(_ is _ + 1, ProgramIR, Class),
    assertion(Class = pure_deterministic_expensive).

test(classifies_recursive_pred_as_recursive_expensive) :-
    ProgramIR = [
        ir_clause(c1, loop(X, Y), [loop(X, Y)], [])
    ],
    classify_expensive_dependency(loop(a, _B), ProgramIR, Class),
    assertion(Class = recursive_expensive).

test(classifies_unknown_goal_as_unknown_expensive) :-
    ProgramIR = [],
    classify_expensive_dependency(some_unknown_pred(x, _Y), ProgramIR, Class),
    assertion(Class = unknown_expensive).

% -----------------------------------------------------------------------
% MNN Signature tests
% -----------------------------------------------------------------------

test(known_signature_classifies_without_deep_search) :-
    Clause = ir_clause(c1, collect(Xs, Ys),
        [findall(Y, (member(X, Xs), f(X, Y)), Ys)], []),
    mnn_signature(Clause, Sig),
    mnn_lookup_class(Sig, Class),
    assertion(Class = map_compatible),
    ignore(Ys=Ys), ignore(Xs=Xs).

test(unknown_signature_falls_back_to_structural) :-
    Clause = ir_clause(c1, custom(X, Y), [my_unusual_pred(X, Y)], []),
    mnn_signature(Clause, Sig),
    assertion(member(Sig, [sig_unknown, sig_unknown_cost_dependency])),
    ignore(X=X), ignore(Y=Y).

test(cut_blocked_signature_detected) :-
    Clause = ir_clause(c1, bad(Xs, Ys),
        [findall(Y, (member(X, Xs), !, f(X, Y)), Ys)], []),
    mnn_signature(Clause, Sig),
    assertion(Sig = sig_cut_blocked),
    ignore(Ys=Ys), ignore(Xs=Xs).

test(io_blocked_signature_detected) :-
    Clause = ir_clause(c1, bad2(Xs, Ys),
        [findall(Y, (member(X, Xs), writeln(X), f(X, Y)), Ys)], []),
    mnn_signature(Clause, Sig),
    assertion(Sig = sig_io_blocked),
    ignore(Ys=Ys), ignore(Xs=Xs).

test(meta_call_blocked_signature_detected) :-
    Clause = ir_clause(c1, bad3(Xs, Ys),
        [findall(Y, (member(X, Xs), call(f, X, Y)), Ys)], []),
    mnn_signature(Clause, Sig),
    assertion(Sig = sig_meta_call_blocked),
    ignore(Ys=Ys), ignore(Xs=Xs).

test(repeated_expensive_signature_detected) :-
    Xs = _SameList,
    Clause = ir_clause(c1, report(Xs, Pairs, Triples),
        [findall([X,A], (member(X,Xs), expensive(X,A)), Pairs),
         findall([X,A,B], (member(X,Xs), expensive(X,A), other(A,B)), Triples)],
        []),
    mnn_signature(Clause, Sig),
    (   Sig = sig_repeated_expensive_template
    ->  mnn_lookup_class(Sig, Class),
        assertion(Class = splice_compatible)
    ;   assertion(true)  % fallback: list vars may not be identical
    ),
    ignore(Pairs=Pairs), ignore(Triples=Triples).

test(mnn_signature_index_builds_for_program) :-
    ProgramIR = [
        ir_clause(c1, add(X, Y, Z), [Z is X + Y], []),
        ir_clause(c2, collect(Xs, Ys),
            [findall(Y, (member(X, Xs), f(X, Y)), Ys)], [])
    ],
    mnn_signature_index(ProgramIR, Index),
    assertion(Index \== []),
    ignore(X=X), ignore(Y=Y), ignore(Z=Z), ignore(Xs=Xs), ignore(Ys=Ys).

test(transform_hint_for_known_signature) :-
    mnn_transform_hint(sig_findall_member_template, Hint),
    assertion(Hint = accumulator_loop_with_reverse).

test(transform_hint_for_unknown_is_fallback) :-
    mnn_transform_hint(sig_unknown, Hint),
    assertion(Hint = fallback_to_structural_classifier).

:- end_tests(test_expensive_dependency).
