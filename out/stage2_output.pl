expensive(0,0).
expensive(A,B):-A>0,B is A*A.
p(A,B,C):-expensive(A,D),B is D+1,C is D+2.
