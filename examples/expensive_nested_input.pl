% examples/expensive_nested_input.pl
% Expensive nested loop example — outer loop over Xs, inner loop over the
% result of an expensive/2 call.  The inner member/2 depends on the outer
% expensive/2 call so we cannot hoist it out.

nested(Xs, Out) :-
    findall(Z,
        ( member(X, Xs),
          expensive(X, A),
          member(Y, A),
          transform(X, Y, Z)
        ),
        Out).

% Expected output (dependent_nested_loop class):
%
% nested(Xs, Out) :-
%     nested_loop(Xs, [], Rev),
%     reverse(Rev, Out).
% nested_loop([], Acc, Acc).
% nested_loop([X|Xs], Acc0, Out) :-
%     expensive(X, A),
%     nested_inner_loop(X, A, Acc0, Acc1),
%     nested_loop(Xs, Acc1, Out).
% nested_inner_loop(_, [], Acc, Acc).
% nested_inner_loop(X, [Y|Ys], Acc0, Acc) :-
%     transform(X, Y, Z),
%     nested_inner_loop(X, Ys, [Z|Acc0], Acc).
