expensive(X, A) :-
    expensive_sub(X, S),
    finish(S, A).

template1(X, T1) :-
    expensive(X, A),
    T1 = row1(A).

template2(X, T2) :-
    expensive(X, A),
    T2 = row2(A).

report(X, Z) :-
    template1(X, T1),
    template2(X, T2),
    Z = [T1, T2].

expensive_sub(X, S) :-
    S is X * 10.

finish(S, A) :-
    A is S + 1.
