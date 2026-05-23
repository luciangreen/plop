inc(X, Y) :-
    Y is X + 1.

double(X, Y) :-
    Y is X * 2.

combined(X, Y) :-
    inc(X, A),
    double(A, Y).
