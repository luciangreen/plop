expensive(A, B) :-
    expensive_sub(A, C),
    finish(C, B).

template1(A, B) :-
    expensive(A, C),
    B=row1(C).

template2(A, B) :-
    expensive(A, C),
    B=row2(C).

report(A, B) :-
    expensive_sub(A, C),
    finish(C, D),
    E=row1(D),
    F=row2(D),
    B=[E,F].

expensive_sub(A, B) :-
    B is A*10.

finish(A, B) :-
    B is A+1.
