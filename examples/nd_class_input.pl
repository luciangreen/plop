% examples/nd_class_input.pl
% ND→D Classifier — example input showing all supported ND patterns.

% 1. Deterministic predicate (no choicepoints).
add(X, Y, Z) :- Z is X + Y.

% 2. Simple enumerator.
first_elem([H|_], H).

% 3. Map-compatible: findall/member/template.
collect(Xs, Ys) :-
    findall(Y, (member(X, Xs), f(X, Y)), Ys).

% 4. Fold-compatible: findall/member + sum_list.
total(Xs, Total) :-
    findall(V, (member(X, Xs), score(X, V)), Vs),
    sum_list(Vs, Total).

% 5. Flatmap-compatible: nested member.
nested(Xs, Out) :-
    findall(Z,
        ( member(X, Xs),
          expensive(X, A),
          member(Y, A),
          transform(X, Y, Z)
        ),
        Out).

% 6. Splice-compatible: repeated expensive call, shared template.
report(Xs, Pairs, Triples) :-
    findall([X,A], (member(X,Xs), expensive(X,A)), Pairs),
    findall([X,A,B], (member(X,Xs), expensive(X,A), other(A,B)), Triples).

% 7. IO predicate — must be rejected.
print_each([]).
print_each([H|T]) :- writeln(H), print_each(T).

% 8. Cut-using predicate — must be rejected.
first_only([H|_], H) :- !.
