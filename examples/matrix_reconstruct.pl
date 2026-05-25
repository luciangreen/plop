matrix_output(Matrix, Output) :-

    nth1(1, Matrix, Row1),

    nth1(1, Row1, A),

    nth1(2, Row1, B),

    nth1(2, Matrix, Row2),

    nth1(1, Row2, C),

    Output = [[A,B], C].