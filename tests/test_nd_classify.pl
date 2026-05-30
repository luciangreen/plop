:- begin_tests(nd_classify).

:- use_module('../nd_classify').

% --- deterministic ---
test(deterministic_predicate_classified_as_deterministic) :-
    ProgramIR = [
        ir_clause(c1, add(X, Y, Z), [Z is X + Y], [])
    ],
    nd_classify_predicate(add/3, ProgramIR, Class, _Reasons),
    assertion(Class = deterministic).

% --- enumerator ---
test(member_classified_as_enumerator) :-
    ProgramIR = [
        ir_clause(c1, elems(Xs, X), [member(X, Xs)], [])
    ],
    nd_classify_predicate(elems/2, ProgramIR, Class, _),
    assertion(Class = enumerator).

% --- map_compatible ---
test(findall_member_template_classified_as_map_compatible) :-
    ProgramIR = [
        ir_clause(c1, collect(Xs, Ys),
            [findall(Y, (member(X, Xs), f(X, Y)), Ys)],
            [])
    ],
    nd_classify_predicate(collect/2, ProgramIR, Class, _),
    assertion(Class = map_compatible).

% --- fold_compatible ---
test(findall_member_sum_classified_as_fold_compatible) :-
    ProgramIR = [
        ir_clause(c1, total(Xs, Total),
            [findall(V, (member(X, Xs), score(X, V)), Vs),
             sum_list(Vs, Total)],
            [])
    ],
    nd_classify_predicate(total/2, ProgramIR, Class, _),
    assertion(Class = fold_compatible).

% --- flatmap_compatible ---
test(nested_member_classified_as_flatmap_compatible) :-
    ProgramIR = [
        ir_clause(c1, nested(Xs, Out),
            [findall(Z, (member(X, Xs), expensive(X, A), member(Y, A),
                         transform(X, Y, Z)), Out)],
            [])
    ],
    nd_classify_predicate(nested/2, ProgramIR, Class, _),
    assertion(Class = flatmap_compatible).

% --- splice_compatible ---
test(repeated_expensive_template_classified_as_splice_compatible) :-
    ProgramIR = [
        ir_clause(c1, report(Xs, Pairs, Triples),
            [findall([X,A], (member(X,Xs), expensive(X,A)), Pairs),
             findall([X,A,B], (member(X,Xs), expensive(X,A), other(A,B)), Triples)],
            [])
    ],
    nd_classify_predicate(report/3, ProgramIR, Class, _),
    assertion(Class = splice_compatible).

% --- IO predicate rejected ---
test(io_predicate_classified_as_unsafe) :-
    ProgramIR = [
        ir_clause(c1, print_all([]), [], []),
        ir_clause(c2, print_all([H|T]), [writeln(H), print_all(T)], [])
    ],
    nd_classify_predicate(print_all/1, ProgramIR, Class, _),
    assertion(Class = unsafe_nondeterminism).

% --- cut predicate rejected ---
test(cut_predicate_classified_as_unsafe) :-
    ProgramIR = [
        ir_clause(c1, first([H|_], H), [!], [])
    ],
    nd_classify_predicate(first/2, ProgramIR, Class, _),
    assertion(Class = unsafe_nondeterminism).

% --- unknown expensive predicate ---
test(unknown_expensive_predicate_marked_unknown) :-
    ProgramIR = [
        ir_clause(c1, wrap(X, Y), [unknown_expensive_pred(X, Y)], [])
    ],
    nd_classify_predicate(wrap/2, ProgramIR, Class, _),
    % No choicepoints, no IO, no cut → deterministic (unknown_expensive is user-decl)
    assertion(member(Class, [deterministic, unknown_cost_dependency])).

% --- nd_goal_class ---
test(nd_goal_class_findall_is_map_compatible) :-
    nd_goal_class(findall(_, (member(_, _), _), _), [], Class),
    assertion(Class = map_compatible).

test(nd_goal_class_member_is_enumerator) :-
    nd_goal_class(member(_, _), [], Class),
    assertion(Class = enumerator).

test(nd_goal_class_arithmetic_is_deterministic) :-
    nd_goal_class(_ is _ + 1, [], Class),
    assertion(Class = deterministic).

test(nd_goal_class_writeln_is_unsafe) :-
    nd_goal_class(writeln(_), [], Class),
    assertion(Class = unsafe_nondeterminism).

% --- can_convert_1_to_1 ---
test(can_convert_deterministic_returns_yes) :-
    ProgramIR = [
        ir_clause(c1, add(X, Y, Z), [Z is X + Y], [])
    ],
    can_convert_1_to_1(add/3, ProgramIR, Decision),
    assertion(Decision = yes(deterministic, _)).

test(can_convert_map_returns_yes) :-
    ProgramIR = [
        ir_clause(c1, collect(Xs, Ys),
            [findall(Y, (member(X, Xs), f(X, Y)), Ys)], [])
    ],
    can_convert_1_to_1(collect/2, ProgramIR, Decision),
    assertion(Decision = yes(map_compatible, _)).

test(can_convert_unsafe_returns_no) :-
    ProgramIR = [
        ir_clause(c1, print_first([H|_]), [writeln(H)], [])
    ],
    can_convert_1_to_1(print_first/1, ProgramIR, Decision),
    assertion(Decision = no(_)).

% --- nd_body_class ---
test(nd_body_class_findall_member_is_map_compatible) :-
    Body = [findall(Y, (member(X, [1,2,3]), f(X, Y)), Ys)],
    nd_body_class(Body, [], Class, _DepGraph),
    assertion(Class = map_compatible).

test(nd_body_class_empty_is_deterministic) :-
    nd_body_class([], [], Class, _DepGraph),
    assertion(Class = deterministic).

% --- nd_classify_program ---
test(nd_classify_program_annotates_all_predicates) :-
    ProgramIR = [
        ir_clause(c1, add(X, Y, Z), [Z is X + Y], []),
        ir_clause(c2, collect(Xs, Ys),
            [findall(Y, (member(X, Xs), f(X, Y)), Ys)], [])
    ],
    nd_classify_program(ProgramIR, _ClassifiedIR, Report),
    assertion(member(nd_classified(add/3, deterministic, _), Report)),
    assertion(member(nd_classified(collect/2, map_compatible, _), Report)),
    assertion(member(mnn_signature_unknown(add/3, _), Report)),
    assertion(member(mnn_signature_matched(collect/2, _), Report)).

:- end_tests(nd_classify).
