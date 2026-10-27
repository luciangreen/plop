matrix_output(A,B):-B=[[C,D],E],subterm_with_address(A,[1,1],C),subterm_with_address(A,[1,2],D),subterm_with_address(A,[2,1],E).
