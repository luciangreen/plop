:- module(common_dependency_hoist, [hoist_common_dependencies/4]).

:- use_module(safety, [has_side_effects/1, has_cut/1]).

hoist_common_dependencies(ProgramIR, _Graph, OptimisedIR, Report) :-
    hoist_clauses(ProgramIR, ProgramIR, OptimisedIR, [], Report0),
    sort(Report0, Report).

hoist_clauses(_, [], [], Report, Report).
hoist_clauses(ProgramIR, [Clause | Rest], [UpdatedClause | UpdatedRest], Report0, Report) :-
    hoist_clause(ProgramIR, Clause, UpdatedClause, ClauseItems),
    append(ClauseItems, Report0, Report1),
    hoist_clauses(ProgramIR, Rest, UpdatedRest, Report1, Report).

hoist_clause(ProgramIR, ir_clause(Id, Head, Body, Meta), UpdatedClause, Items) :-
    predicate_from_head(Head, Pred),
    find_template_expansions(Body, ProgramIR, 1, Expansions),
    select_best_group(Expansions, BestGroup),
    (   BestGroup = group(GroupMembers),
        GroupMembers = [first_member(_, _, FirstExpanded) | _],
        common_prefix_and_suffixes(GroupMembers, Prefix, Suffixes, PrefixReason),
        Prefix \= [],
        safe_shared_prefix(Prefix, ProgramIR, [], SafetyReason),
        PrefixReason == ok,
        SafetyReason == ok,
        rewrite_clause_body_with_group(Body, GroupMembers, Prefix, Suffixes, NewBody),
        NewBody \== Body
    ->  shared_subgoal_report_term(Prefix, SubgoalReport),
        length(GroupMembers, Count),
        UpdatedMeta = [hierarchical_splice_ready | Meta],
        UpdatedClause = ir_clause(Id, Head, NewBody, UpdatedMeta),
        Items = [common_dependency_hoisted(SubgoalReport, Count)]
    ;   skip_reason(Expansions, ProgramIR, Reason),
        (   Reason == none
        ->  UpdatedClause = ir_clause(Id, Head, Body, Meta),
            Items = []
        ;   UpdatedClause = ir_clause(Id, Head, Body, Meta),
            Items = [skipped_hierarchical_splice(Pred, Reason)]
        )
    ).

find_template_expansions([], _, _, []).
find_template_expansions([Goal | Rest], ProgramIR, Index, Expansions) :-
    find_template_expansions(Rest, ProgramIR, Index + 1, RestExpansions),
    (   expand_goal(Goal, ProgramIR, ExpandedBody)
    ->  Expansions = [member_expansion(Index, Goal, ExpandedBody) | RestExpansions]
    ;   Expansions = RestExpansions
    ).

expand_goal(Goal, ProgramIR, ExpandedBody) :-
    callable(Goal),
    predicate_from_goal(Goal, Pred),
    predicate_clauses(ProgramIR, Pred, [ir_clause(_, Head, Body, _)]),
    copy_term((Head, Body), (HeadCopy, BodyCopy)),
    Goal = HeadCopy,
    ExpandedBody = BodyCopy,
    ExpandedBody \= [].

predicate_clauses(ProgramIR, Pred, Clauses) :-
    include(clause_matches_predicate(Pred), ProgramIR, Clauses).

clause_matches_predicate(Pred, ir_clause(_, Head, _, _)) :-
    predicate_from_head(Head, Pred).

select_best_group(Expansions, group(BestMembers)) :-
    groups_by_first_goal(Expansions, Groups),
    include(group_has_two_or_more, Groups, CandidateGroups),
    CandidateGroups \= [],
    sort_groups_by_size_desc(CandidateGroups, [BestMembers | _]).

select_best_group(_, none).

group_has_two_or_more(Members) :-
    length(Members, L),
    L >= 2.

sort_groups_by_size_desc(Groups, Sorted) :-
    map_list_to_pairs(group_size_key, Groups, Pairs),
    keysort(Pairs, SortedPairsAsc),
    reverse(SortedPairsAsc, SortedPairsDesc),
    pairs_values(SortedPairsDesc, Sorted).

group_size_key(Group, Key) :-
    length(Group, L),
    Key is L.

groups_by_first_goal(Expansions, Groups) :-
    groups_by_first_goal(Expansions, [], Groups).

groups_by_first_goal([], Acc, Groups) :-
    findall(
        Members,
        member(group_bucket(_, Members), Acc),
        Groups
    ).
groups_by_first_goal([member_expansion(Index, Goal, ExpandedBody) | Rest], Acc0, Groups) :-
    ExpandedBody = [FirstGoal | _],
    canonical_term(FirstGoal, Key),
    add_group_member(Key, first_member(Index, Goal, ExpandedBody), Acc0, Acc1),
    groups_by_first_goal(Rest, Acc1, Groups).

add_group_member(Key, Member, [], [group_bucket(Key, [Member])]).
add_group_member(Key, Member, [group_bucket(Key, Members) | Rest], [group_bucket(Key, [Member | Members]) | Rest]) :- !.
add_group_member(Key, Member, [Bucket | Rest], [Bucket | UpdatedRest]) :-
    add_group_member(Key, Member, Rest, UpdatedRest).

canonical_term(Term, Canonical) :-
    copy_term(Term, Copy),
    numbervars(Copy, 0, _),
    Canonical = Copy.

common_prefix_and_suffixes(GroupMembers0, Prefix, Suffixes, Reason) :-
    sort_group_members(GroupMembers0, GroupMembers),
    GroupMembers = [first_member(_, _, FirstExpanded) | Rest],
    minimum_length([FirstExpanded | Rest], MinLen),
    MinLen > 0,
    longest_variant_prefix_length([FirstExpanded | Rest], MinLen, PrefixLen),
    PrefixLen > 0,
    take_n_goals(PrefixLen, FirstExpanded, Prefix, FirstSuffix),
    align_other_suffixes(Rest, Prefix, [FirstSuffix], Suffixes),
    Reason = ok,
    contiguous_group(GroupMembers),
    !.
common_prefix_and_suffixes(_, [], [], no_common_dependency).

sort_group_members(GroupMembers, Sorted) :-
    map_list_to_pairs(member_index_key, GroupMembers, Pairs),
    keysort(Pairs, SortedPairs),
    pairs_values(SortedPairs, Sorted).

member_index_key(first_member(Index, _, _), Index).

minimum_length(Bodies, MinLen) :-
    findall(L, (member(B, Bodies), length(B, L)), Lengths),
    min_list(Lengths, MinLen).

longest_variant_prefix_length(Bodies, MinLen, PrefixLen) :-
    longest_variant_prefix_length(Bodies, 1, MinLen, 0, PrefixLen).

longest_variant_prefix_length(_, Current, MinLen, Best, Best) :-
    Current > MinLen,
    !.
longest_variant_prefix_length(Bodies, Current, MinLen, _Best, PrefixLen) :-
    variant_prefix_holds(Bodies, Current),
    Next is Current + 1,
    longest_variant_prefix_length(Bodies, Next, MinLen, Current, PrefixLen).
longest_variant_prefix_length(_Bodies, _Current, _MinLen, Best, Best).

variant_prefix_holds([First | Rest], Pos) :-
    nth1(Pos, First, Goal),
    forall(
        member(Body, Rest),
        (
            nth1(Pos, Body, Other),
            Goal =@= Other
        )
    ).

take_n_goals(0, Goals, [], Goals) :- !.
take_n_goals(N, [G | Rest], [G | PrefixRest], Suffix) :-
    N1 is N - 1,
    take_n_goals(N1, Rest, PrefixRest, Suffix).

align_other_suffixes([], _Prefix, Acc, Suffixes) :-
    reverse(Acc, Suffixes).
align_other_suffixes([first_member(_, _, Expanded) | Rest], Prefix, Acc0, Suffixes) :-
    length(Prefix, PrefixLen),
    take_n_goals(PrefixLen, Expanded, CandidatePrefix, Suffix),
    unify_goal_lists(CandidatePrefix, Prefix),
    align_other_suffixes(Rest, Prefix, [Suffix | Acc0], Suffixes).

unify_goal_lists([], []).
unify_goal_lists([A | As], [B | Bs]) :-
    A = B,
    unify_goal_lists(As, Bs).

contiguous_group(GroupMembers) :-
    findall(Index, member(first_member(Index, _, _), GroupMembers), Indices0),
    sort(Indices0, Indices),
    Indices = [First | _],
    last(Indices, Last),
    length(Indices, Count),
    Last - First + 1 =:= Count.

safe_shared_prefix([], _, _, ok).
safe_shared_prefix([Goal | Rest], ProgramIR, Visiting, Reason) :-
    safe_goal(Goal, ProgramIR, Visiting, GoalReason),
    (   GoalReason == ok
    ->  safe_shared_prefix(Rest, ProgramIR, Visiting, Reason)
    ;   Reason = GoalReason
    ).

safe_goal(Goal, _ProgramIR, _Visiting, cut) :-
    has_cut(Goal),
    !.
safe_goal(Goal, _ProgramIR, _Visiting, side_effect) :-
    has_side_effects(Goal),
    !.
safe_goal(Goal, _ProgramIR, _Visiting, meta) :-
    meta_goal(Goal),
    !.
safe_goal(Goal, _ProgramIR, _Visiting, random) :-
    random_goal(Goal),
    !.
safe_goal(Goal, _ProgramIR, _Visiting, var_sensitive) :-
    var_sensitive_goal(Goal),
    !.
safe_goal(Goal, _ProgramIR, _Visiting, control_flow) :-
    control_flow_goal(Goal),
    !.
safe_goal(Goal, ProgramIR, Visiting, Reason) :-
    predicate_from_goal(Goal, Pred),
    predicate_clauses(ProgramIR, Pred, Clauses),
    Clauses \= [],
    !,
    (   member(Pred, Visiting)
    ->  Reason = recursive
    ;   Clauses = [_]
    ->  Clauses = [ir_clause(_, _, Body, _)],
        safe_shared_prefix(Body, ProgramIR, [Pred | Visiting], Reason)
    ;   Reason = nondeterministic
    ).
safe_goal(_Goal, _ProgramIR, _Visiting, ok).

meta_goal(Goal) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    member(Name/Arity, [call/1, call/2, call/3, call/4, once/1, maplist/2, maplist/3, maplist/4, findall/3, bagof/3, setof/3]).

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

rewrite_clause_body_with_group(Body, GroupMembers0, Prefix, Suffixes, NewBody) :-
    sort_group_members(GroupMembers0, GroupMembers),
    findall(Index, member(first_member(Index, _, _), GroupMembers), SelectedIndices),
    GroupMembers = [first_member(FirstIndex, _, _) | _],
    flatten(Suffixes, FlatSuffixes),
    rewrite_body_positions(Body, 1, FirstIndex, SelectedIndices, Prefix, FlatSuffixes, NewBody).

rewrite_body_positions([], _, _, _, _, _, []).
rewrite_body_positions([Goal | Rest], Pos, FirstIndex, Selected, Prefix, FlatSuffixes, NewBody) :-
    Pos =:= FirstIndex,
    member(Pos, Selected),
    !,
    NextPos is Pos + 1,
    rewrite_body_positions(Rest, NextPos, FirstIndex, Selected, Prefix, FlatSuffixes, Tail),
    append(Prefix, FlatSuffixes, Hoisted),
    append(Hoisted, Tail, NewBody).
rewrite_body_positions([_Goal | Rest], Pos, FirstIndex, Selected, Prefix, FlatSuffixes, NewBody) :-
    member(Pos, Selected),
    !,
    NextPos is Pos + 1,
    rewrite_body_positions(Rest, NextPos, FirstIndex, Selected, Prefix, FlatSuffixes, NewBody).
rewrite_body_positions([Goal | Rest], Pos, FirstIndex, Selected, Prefix, FlatSuffixes, [Goal | Tail]) :-
    NextPos is Pos + 1,
    rewrite_body_positions(Rest, NextPos, FirstIndex, Selected, Prefix, FlatSuffixes, Tail).

shared_subgoal_report_term([Goal | _], Pred) :-
    predicate_from_goal(Goal, Pred).

skip_reason(Expansions, ProgramIR, Reason) :-
    groups_by_first_goal(Expansions, Groups),
    include(group_has_two_or_more, Groups, CandidateGroups),
    (   CandidateGroups == []
    ->  Reason = none
    ;   sort_groups_by_size_desc(CandidateGroups, [BestMembers | _]),
        common_prefix_and_suffixes(BestMembers, Prefix, _Suffixes, PrefixReason),
        (   PrefixReason \== ok
        ->  Reason = PrefixReason
        ;   safe_shared_prefix(Prefix, ProgramIR, [], SafeReason),
            (SafeReason == ok -> Reason = none ; Reason = SafeReason)
        )
    ).

predicate_from_head(Head, Name/Arity) :-
    callable(Head),
    functor(Head, Name, Arity).

predicate_from_goal(Goal, Name/Arity) :-
    callable(Goal),
    functor(Goal, Name, Arity).
