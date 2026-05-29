:- module(common_dependency_hoist, [hoist_common_dependencies/4]).

:- use_module(safety, [has_side_effects/1, has_cut/1]).

hoist_common_dependencies(ProgramIR, _Graph, OptimisedIR, Report) :-
    hoist_clauses(ProgramIR, ProgramIR, OptimisedIR, [], Report0),
    sort(Report0, Report).

hoist_clauses(_, [], [], Acc, Acc).
hoist_clauses(ProgramIR, [Clause | Rest], [Updated | UpdatedRest], Acc0, Acc) :-
    hoist_clause(ProgramIR, Clause, Updated, Items),
    append(Items, Acc0, Acc1),
    hoist_clauses(ProgramIR, Rest, UpdatedRest, Acc1, Acc).

hoist_clause(ProgramIR, ir_clause(Id, Head, Body, Meta), UpdatedClause, Items) :-
    predicate_from_head(Head, Pred),
    find_expansions(Body, ProgramIR, 1, Expansions),
    best_group(Expansions, Group),
    (   Group = group(Members),
        Members = [_ , _ | _],
        common_prefix_and_suffixes(Members, Prefix, Suffixes),
        Prefix \= [],
        safe_prefix(Prefix, ProgramIR, [], Reason),
        Reason == ok,
        rewrite_with_group(Body, Members, Prefix, Suffixes, NewBody),
        NewBody \== Body
    ->  shared_subgoal_report(Prefix, SharedPred),
        length(Members, Count),
        UpdatedClause = ir_clause(Id, Head, NewBody, [hierarchical_splice_ready | Meta]),
        Items = [common_dependency_hoisted(SharedPred, Count)]
    ;   skip_reason(ProgramIR, Group, Reason0),
        UpdatedClause = ir_clause(Id, Head, Body, Meta),
        (Reason0 == none -> Items = [] ; Items = [skipped_hierarchical_splice(Pred, Reason0)])
    ).

find_expansions([], _, _, []).
find_expansions([Goal | Rest], ProgramIR, Index, Expansions) :-
    NextIndex is Index + 1,
    find_expansions(Rest, ProgramIR, NextIndex, RestExpansions),
    (   expand_goal(Goal, ProgramIR, Expanded)
    ->  Expansions = [expansion(Index, Goal, Expanded) | RestExpansions]
    ;   Expansions = RestExpansions
    ).

expand_goal(Goal, ProgramIR, ExpandedBody) :-
    callable(Goal),
    predicate_from_goal(Goal, Pred),
    predicate_clauses(ProgramIR, Pred, [ir_clause(_, Head, Body, _)]),
    Body \= [],
    copy_term((Head, Body), (HeadCopy, BodyCopy)),
    Goal = HeadCopy,
    ExpandedBody = BodyCopy.

predicate_clauses(ProgramIR, Pred, Clauses) :-
    include(matches_pred(Pred), ProgramIR, Clauses).

matches_pred(Pred, ir_clause(_, Head, _, _)) :-
    predicate_from_head(Head, Pred).

best_group(Expansions, Group) :-
    group_expansions(Expansions, Groups),
    include(group_size_at_least_two, Groups, NonTrivial),
    (   NonTrivial == []
    ->  Group = none
    ;   largest_group(NonTrivial, Best),
        Group = group(Best)
    ).

group_size_at_least_two(Members) :-
    length(Members, N),
    N >= 2.

largest_group([Group | Rest], Largest) :-
    largest_group(Rest, Group, Largest).

largest_group([], Largest, Largest).
largest_group([Group | Rest], Current, Largest) :-
    length(Group, NGroup),
    length(Current, NCurrent),
    (   NGroup > NCurrent
    ->  Next = Group
    ;   Next = Current
    ),
    largest_group(Rest, Next, Largest).

group_expansions(Expansions, Groups) :-
    group_expansions(Expansions, [], Buckets),
    buckets_members(Buckets, Groups).

group_expansions([], Buckets, Buckets).
group_expansions([expansion(Index, Goal, Expanded) | Rest], Buckets0, Buckets) :-
    Expanded = [First | _],
    canonical(First, Key),
    insert_bucket_member(Key, member_entry(Index, Goal, Expanded), Buckets0, Buckets1),
    group_expansions(Rest, Buckets1, Buckets).

insert_bucket_member(Key, Member, [], [bucket(Key, [Member])]).
insert_bucket_member(Key, Member, [bucket(Key, Members) | Rest], [bucket(Key, [Member | Members]) | Rest]) :- !.
insert_bucket_member(Key, Member, [B | Rest], [B | UpdatedRest]) :-
    insert_bucket_member(Key, Member, Rest, UpdatedRest).

buckets_members([], []).
buckets_members([bucket(_, Members) | Rest], [Members | GroupRest]) :-
    buckets_members(Rest, GroupRest).

canonical(Term, Canonical) :-
    copy_term(Term, Copy),
    numbervars(Copy, 0, _),
    Canonical = Copy.

common_prefix_and_suffixes(Members0, Prefix, Suffixes) :-
    sort_members(Members0, Members),
    Members = [member_entry(_, _, FirstExpanded) | Rest],
    bodies_from_members([member_entry(0, none, FirstExpanded) | Rest], Bodies),
    min_body_length(Bodies, MinLen),
    longest_prefix(Bodies, MinLen, PrefixLen),
    PrefixLen > 0,
    take_prefix(PrefixLen, FirstExpanded, Prefix, FirstSuffix),
    align_suffixes(Rest, Prefix, [FirstSuffix], Suffixes),
    contiguous(Members).

bodies_from_members([], []).
bodies_from_members([member_entry(_, _, Body) | Rest], [Body | BodiesRest]) :-
    bodies_from_members(Rest, BodiesRest).

sort_members(Members, Sorted) :-
    sort_members(Members, [], Sorted).

sort_members([], Acc, Sorted) :-
    Sorted = Acc.
sort_members([Member | Rest], Acc, Sorted) :-
    insert_member_by_pos(Member, Acc, Acc1),
    sort_members(Rest, Acc1, Sorted).

insert_member_by_pos(Member, [], [Member]).
insert_member_by_pos(member_entry(Pos, Goal, Expanded), [member_entry(PosH, GoalH, ExpandedH) | Rest], [member_entry(Pos, Goal, Expanded), member_entry(PosH, GoalH, ExpandedH) | Rest]) :-
    Pos =< PosH,
    !.
insert_member_by_pos(Member, [Head | Rest], [Head | RestOut]) :-
    insert_member_by_pos(Member, Rest, RestOut).

min_body_length(Bodies, Min) :-
    findall(L, (member(B, Bodies), length(B, L)), Lens),
    min_list(Lens, Min).

longest_prefix(Bodies, MinLen, PrefixLen) :-
    longest_prefix(Bodies, 1, MinLen, 0, PrefixLen).

longest_prefix(_, Pos, MinLen, Best, Best) :-
    Pos > MinLen,
    !.
longest_prefix(Bodies, Pos, MinLen, _Best, PrefixLen) :-
    prefix_position_variant(Bodies, Pos),
    Next is Pos + 1,
    longest_prefix(Bodies, Next, MinLen, Pos, PrefixLen).
longest_prefix(_, _, _, Best, Best).

prefix_position_variant([First | Rest], Pos) :-
    nth1(Pos, First, Goal),
    forall((member(Body, Rest), nth1(Pos, Body, Other)), Goal =@= Other).

take_prefix(0, Body, [], Body) :- !.
take_prefix(N, [G | Rest], [G | PrefixRest], Suffix) :-
    N1 is N - 1,
    take_prefix(N1, Rest, PrefixRest, Suffix).

align_suffixes([], _, Acc, Suffixes) :-
    reverse(Acc, Suffixes).
align_suffixes([member_entry(_, _, Expanded) | Rest], Prefix, Acc0, Suffixes) :-
    length(Prefix, PrefixLen),
    take_prefix(PrefixLen, Expanded, CandidatePrefix, Suffix),
    unify_prefix(CandidatePrefix, Prefix),
    align_suffixes(Rest, Prefix, [Suffix | Acc0], Suffixes).

unify_prefix([], []).
unify_prefix([A | As], [B | Bs]) :-
    A = B,
    unify_prefix(As, Bs).

contiguous(Members) :-
    findall(Pos, member(member_entry(Pos, _, _), Members), Pos0),
    sort(Pos0, PosList),
    PosList = [First | _],
    last(PosList, Last),
    length(PosList, Count),
    Last - First + 1 =:= Count.

safe_prefix([], _, _, ok).
safe_prefix([Goal | Rest], ProgramIR, Visiting, Reason) :-
    safe_goal(Goal, ProgramIR, Visiting, GoalReason),
    (   GoalReason == ok
    ->  safe_prefix(Rest, ProgramIR, Visiting, Reason)
    ;   Reason = GoalReason
    ).

safe_goal(Goal, _, _, cut) :- has_cut(Goal), !.
safe_goal(Goal, _, _, side_effect) :- has_side_effects(Goal), !.
safe_goal(Goal, _, _, meta) :- meta_goal(Goal), !.
safe_goal(Goal, _, _, random) :- random_goal(Goal), !.
safe_goal(Goal, _, _, var_sensitive) :- var_sensitive_goal(Goal), !.
safe_goal(Goal, _, _, control_flow) :- control_flow_goal(Goal), !.
safe_goal(Goal, ProgramIR, Visiting, Reason) :-
    predicate_from_goal(Goal, Pred),
    predicate_clauses(ProgramIR, Pred, Clauses),
    Clauses \= [],
    !,
    (   member(Pred, Visiting)
    ->  Reason = recursive
    ;   Clauses = [ir_clause(_, _, Body, _)]
    ->  safe_prefix(Body, ProgramIR, [Pred | Visiting], Reason)
    ;   Reason = nondeterministic
    ).
safe_goal(_, _, _, ok).

meta_goal(Goal) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    member(Name/Arity, [call/1, call/2, call/3, call/4, once/1, findall/3, bagof/3, setof/3, maplist/2, maplist/3, maplist/4]).

random_goal(Goal) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    member(Name/Arity, [random/1, random/3, random_between/3, setrand/1, getrand/1]).

var_sensitive_goal(Goal) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    member(Name/Arity, [var/1, nonvar/1]).

control_flow_goal((_;_)).
control_flow_goal((_->_)).
control_flow_goal((_->_;_)).
control_flow_goal(\+ _).

rewrite_with_group(Body, Members0, Prefix, Suffixes, NewBody) :-
    sort_members(Members0, Members),
    Members = [member_entry(FirstPos, _, _) | _],
    findall(Pos, member(member_entry(Pos, _, _), Members), Selected),
    flatten(Suffixes, FlatSuffixes),
    rewrite_positions(Body, 1, FirstPos, Selected, Prefix, FlatSuffixes, NewBody).

rewrite_positions([], _, _, _, _, _, []).
rewrite_positions([_Goal | Rest], Pos, FirstPos, Selected, Prefix, FlatSuffixes, NewBody) :-
    Pos =:= FirstPos,
    member(Pos, Selected),
    !,
    Next is Pos + 1,
    rewrite_positions(Rest, Next, FirstPos, Selected, Prefix, FlatSuffixes, Tail),
    append(Prefix, FlatSuffixes, Injected),
    append(Injected, Tail, NewBody).
rewrite_positions([_Goal | Rest], Pos, FirstPos, Selected, Prefix, FlatSuffixes, NewBody) :-
    member(Pos, Selected),
    !,
    Next is Pos + 1,
    rewrite_positions(Rest, Next, FirstPos, Selected, Prefix, FlatSuffixes, NewBody).
rewrite_positions([Goal | Rest], Pos, FirstPos, Selected, Prefix, FlatSuffixes, [Goal | Tail]) :-
    Next is Pos + 1,
    rewrite_positions(Rest, Next, FirstPos, Selected, Prefix, FlatSuffixes, Tail).

shared_subgoal_report([Goal | _], Pred) :-
    predicate_from_goal(Goal, Pred).

skip_reason(_ProgramIR, none, none) :- !.
skip_reason(ProgramIR, group(Members), Reason) :-
    (   common_prefix_and_suffixes(Members, Prefix, _)
    ->  safe_prefix(Prefix, ProgramIR, [], SafeReason),
        (SafeReason == ok -> Reason = none ; Reason = SafeReason)
    ;   Reason = no_common_dependency
    ).

predicate_from_head(Head, Name/Arity) :-
    callable(Head),
    functor(Head, Name, Arity).

predicate_from_goal(Goal, Name/Arity) :-
    callable(Goal),
    functor(Goal, Name, Arity).
