% Stage 2 memoisation example.
%
% expensive/2 has two clauses so stage 1 will not inline it.
% Stage 2 detects the duplicate expensive(X,A) / expensive(X,B) call
% and removes the second, unifying B with A throughout the clause.

expensive(0, 0).
expensive(X, Y) :-
    X > 0,
    Y is X * X.

p(X, Y, Z) :-
    expensive(X, A),
    expensive(X, B),
    Y is A + 1,
    Z is B + 2.
