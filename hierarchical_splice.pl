:- module(hierarchical_splice, [hierarchical_splice_program/3]).

hierarchical_splice_program(ProgramIR, OptimisedIR, Report) :-
    hierarchical_splice_clauses(ProgramIR, ProgramIR, OptimisedIR, [], Report0),
    sort(Report0, Report).

hierarchical_splice_clauses(_, [], [], Report, Report).
hierarchical_splice_clauses(ProgramIR, [Clause | Rest], [Updated | UpdatedRest], Report0, Report) :-
    hierarchical_splice_clause(ProgramIR, Clause, Updated, Item),
    (   Item == none
    ->  Report1 = Report0
    ;   Report1 = [Item | Report0]
    ),
    hierarchical_splice_clauses(ProgramIR, Rest, UpdatedRest, Report1, Report).

hierarchical_splice_clause(ProgramIR, ir_clause(Id, Head, Body, Meta), ir_clause(Id, Head, NewBody, NewMeta), Item) :-
    (   select(hierarchical_splice_ready, Meta, MetaRest)
    ->  NewMeta = MetaRest,
        expand_shared_prefix(Body, ProgramIR, NewBody),
        predicate_from_head(Head, Pred),
        Item = hierarchical_spliced(Pred)
    ;   NewMeta = Meta,
        NewBody = Body,
        Item = none
    ).

expand_shared_prefix([Goal | Rest], ProgramIR, ExpandedBody) :-
    expand_goal_fully(Goal, ProgramIR, ExpandedPrefix),
    append(ExpandedPrefix, Rest, ExpandedBody).
expand_shared_prefix([], _, []).

expand_goal_fully(Goal, ProgramIR, ExpandedGoals) :-
    expandable_goal(Goal, ProgramIR, Head, Body),
    !,
    copy_term((Head, Body), (HeadCopy, BodyCopy)),
    Goal = HeadCopy,
    ExpandedGoals = BodyCopy.
expand_goal_fully(Goal, _ProgramIR, [Goal]).

expandable_goal(Goal, ProgramIR, Head, Body) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    Pred = Name/Arity,
    include(matches_pred(Pred), ProgramIR, Clauses),
    Clauses = [ir_clause(_, Head, Body, _)].

matches_pred(Pred, ir_clause(_, Head, _, _)) :-
    functor(Head, Name, Arity),
    Pred = Name/Arity.

predicate_from_head(Head, Name/Arity) :-
    callable(Head),
    functor(Head, Name, Arity).
