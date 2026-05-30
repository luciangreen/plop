% examples/loop_splice_input.pl
% Loop-Splice example — two findall calls over the same member enumerator,
% sharing an expensive subgoal, to be spliced into one shared loop.

report(Xs, Pairs, Triples) :-
    findall([X,A], (member(X,Xs), expensive(X,A)), Pairs),
    findall([X,A,B], (member(X,Xs), expensive(X,A), other(A,B)), Triples).

% Also: simple map conversion.
collect(Xs, Ys) :-
    findall(Y, (member(X, Xs), f(X, Y)), Ys).

% Fold conversion.
total(Xs, Total) :-
    findall(V, (member(X, Xs), score(X, V)), Vs),
    sum_list(Vs, Total).
