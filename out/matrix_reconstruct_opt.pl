matrix_output(A,B):-subterm_with_address(A,[1],[C,D]),subterm_with_address(A,[2,1],E),B=[[C,D],E].
