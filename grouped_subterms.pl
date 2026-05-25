:- module(grouped_subterms, [rewrite_grouped_subterms/3]).

rewrite_grouped_subterms(ProgramIR, OptimisedIR, Report) :-
    rewrite_clauses(ProgramIR, OptimisedIR, Report0),
    exclude(=(none), Report0, Report).

rewrite_clauses([], [], []).
rewrite_clauses([C|Cs], [O|Os], [R|Rs]) :-
    rewrite_clause(C, O, R),
    rewrite_clauses(Cs, Os, Rs).

rewrite_clause(ir_clause(Id, Head, Body, Meta),
               ir_clause(Id, Head, NewBody, Meta),
               Report) :-
    predicate_from_head(Head, Pred),
    select(Output = Shape, Body, Body0),
    rewrite_shape(Shape, Body0, Goals, NewShape, UsedGoals, Items),
    Goals \= [],
    !,
remove_used_goals(Body0, UsedGoals, Remaining0),
rewrite_remaining_scalars(Remaining0, ScalarGoals, Remaining),
append(Goals, ScalarGoals, PrefixGoals),
append(PrefixGoals, Remaining, Body1),
append(Body1, [Output = NewShape], NewBody),
    Report = grouped_subterm_rewrite(Pred, Items).
rewrite_clause(Clause, Clause, none).

predicate_from_head(Head, Name/Arity) :-
    functor(Head, Name, Arity).

rewrite_shape(Shape, Body, Goals, NewShape, UsedGoals, Items) :-
    is_list(Shape),
    row_group_lookup(Shape, Body, Matrix, RowIndex, Used),
    !,
    Goals = [subterm_with_address(Matrix, [RowIndex], Shape)],
    NewShape = Shape,
    UsedGoals = Used,
    Items = [grouped(Matrix, [RowIndex], Shape)].

rewrite_shape(Shape, Body, Goals, NewShape, UsedGoals, Items) :-
    is_list(Shape),
    !,
    rewrite_list(Shape, Body, Goals, NewShape, UsedGoals, Items).

rewrite_shape(Value, Body, Goals, Value, UsedGoals, Items) :-
    scalar_lookup(Value, Body, Matrix, RowIndex, ColIndex, UsedGoals),
    !,
    Goals = [subterm_with_address(Matrix, [RowIndex, ColIndex], Value)],
    Items = [single(Matrix, [RowIndex, ColIndex], Value)].

rewrite_shape(Value, _Body, [], Value, [], []).

rewrite_list([], _Body, [], [], [], []).
rewrite_list([X|Xs], Body, Goals, [Y|Ys], Used, Items) :-
    rewrite_shape(X, Body, G1, Y, U1, I1),
    rewrite_list(Xs, Body, G2, Ys, U2, I2),
    append(G1, G2, Goals),
    append(U1, U2, Used),
    append(I1, I2, Items).

row_group_lookup(Values, Body, Matrix, RowIndex, UsedGoals) :-
    Values \= [],
    member(nth1(RowIndex, Matrix, RowVar), Body),
    values_are_consecutive_row_items(Values, Body, RowVar, 1, CellGoals),
    UsedGoals = [nth1(RowIndex, Matrix, RowVar)|CellGoals].

values_are_consecutive_row_items([], _Body, _RowVar, _Col, []).
values_are_consecutive_row_items([V|Vs], Body, RowVar, Col, [nth1(Col, RowVar, V)|Gs]) :-
    member(Goal, Body),
    Goal == nth1(Col, RowVar, V),
    Col2 is Col + 1,
    values_are_consecutive_row_items(Vs, Body, RowVar, Col2, Gs).

scalar_lookup(Value, Body, Matrix, RowIndex, ColIndex, UsedGoals) :-
    member(RowGoal, Body),
    RowGoal = nth1(RowIndex, Matrix, RowVar),
    member(CellGoal, Body),
    CellGoal == nth1(ColIndex, RowVar, Value),
    UsedGoals = [RowGoal, CellGoal].

remove_used_goals([], _Used, []).
remove_used_goals([G|Gs], Used, Rest) :-
    member(U, Used),
    G == U,
    !,
    remove_used_goals(Gs, Used, Rest).
remove_used_goals([G|Gs], Used, [G|Rest]) :-
    remove_used_goals(Gs, Used, Rest).
    
rewrite_remaining_scalars(Body, ScalarGoals, Remaining) :-
    rewrite_remaining_scalars_(Body, [], ScalarGoals0, Remaining),
    reverse(ScalarGoals0, ScalarGoals).

rewrite_remaining_scalars_([], _, [], []).
rewrite_remaining_scalars_([G|Gs], Used, ScalarGoals, Remaining) :-
    member(U, Used),
    G == U,
    !,
    rewrite_remaining_scalars_(Gs, Used, ScalarGoals, Remaining).
rewrite_remaining_scalars_([nth1(RowIndex, Matrix, RowVar)|Gs], Used, ScalarGoals, Remaining) :-
    select(CellGoal, Gs, GsWithoutCell),
    CellGoal = nth1(ColIndex, RowVar, Value),
    !,
    NewGoal = subterm_with_address(Matrix, [RowIndex, ColIndex], Value),
    rewrite_remaining_scalars_(
        GsWithoutCell,
        [nth1(RowIndex, Matrix, RowVar), CellGoal | Used],
        RestScalarGoals,
        Remaining
    ),
    ScalarGoals = [NewGoal | RestScalarGoals].
rewrite_remaining_scalars_([G|Gs], Used, ScalarGoals, [G|Remaining]) :-
    rewrite_remaining_scalars_(Gs, Used, ScalarGoals, Remaining).    