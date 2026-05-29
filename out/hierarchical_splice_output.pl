expensive(A,B):-B is A*10+1.
template1(A,B):-expensive(A,C),B=row1(C).
template2(A,B):-expensive(A,C),B=row2(C).
report(A,B):-C is A*10+1,D=row1(C),E=row2(C),B=[D,E].
expensive_sub(A,B):-B is A*10.
finish(A,B):-B is A+1.
