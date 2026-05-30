:- module(loop_splice, [
    loop_splice_program/3,
    loop_splice_predicate/4,
    detect_spliced_templates/2
]).

:- use_module(safety, [has_side_effects/1, has_cut/1]).

loop_splice_program(ProgramIR, OptimisedIR, Report) :-
    splice_program_clauses(ProgramIR, ConvertedClauses, HelperClauses, ReportItems),
    append(ConvertedClauses, HelperClauses, OptimisedIR),
    sort(ReportItems, Report).

loop_splice_predicate(_Predicate, ProgramIR, OptimisedIR, Report) :-
    loop_splice_program(ProgramIR, OptimisedIR, Report).

splice_program_clauses([], [], [], []).
splice_program_clauses([Clause | Rest], [ConvertedClause | ConvertedRest], Helpers, Report) :-
    splice_clause(Clause, ConvertedClause, ClauseHelpers, ClauseReport),
    splice_program_clauses(Rest, ConvertedRest, RestHelpers, RestReport),
    append(ClauseHelpers, RestHelpers, Helpers),
    append(ClauseReport, RestReport, Report).

splice_clause(ir_clause(Id, Head, Body, Meta), ResultClause, Helpers, Report) :-
    collect_splice_groups(Body, Groups),
    member(group(List, Entries), Groups),
    length(Entries, Count),
    Count >= 2,
    shared_prefix_for_entries(Entries, SharedPrefix),
    SharedPrefix \== [],
    all_entries_safe(Entries),
    !,
    build_splice_helper(Head, Id, List, Entries, SharedPrefix, SpliceCall, Reverses, Helpers),
    remove_spliced_findalls(Body, Entries, RemainingGoals),
    append(RemainingGoals, [SpliceCall | Reverses], NewBody),
    ResultClause = ir_clause(Id, Head, NewBody, Meta),
    functor(Head, Name, Arity),
    Report = [nd_splice_converted(Name/Arity)].
splice_clause(Clause, Clause, [], []).

detect_spliced_templates(Body, Templates) :-
    collect_splice_groups(Body, Groups),
    member(group(_List, Entries), Groups),
    length(Entries, Count),
    Count >= 2,
    !,
    findall(findall(Template, Generator, Output), member(entry(Template, Generator, Output, _, _, _), Entries), Templates).
detect_spliced_templates(_, []).

collect_splice_groups(Body, Groups) :-
    findall(
        entry(Template, Generator, Output, X, List, RestGoals),
        (
            member(findall(Template, Generator, Output), Body),
            split_member_generator(Generator, X, List, RestGoals)
        ),
        Entries
    ),
    group_entries_by_list(Entries, Groups).

group_entries_by_list([], []).
group_entries_by_list([Entry | Rest], [group(List, [Entry | SameList]) | Groups]) :-
    Entry = entry(_, _, _, _, List, _),
    include(entry_same_list(List), Rest, SameList),
    exclude(entry_same_list(List), Rest, Remaining),
    group_entries_by_list(Remaining, Groups).

entry_same_list(List, entry(_, _, _, _, OtherList, _)) :-
    List == OtherList.

shared_prefix_for_entries([entry(_, _, _, _, _, GoalsA), entry(_, _, _, _, _, GoalsB) | Rest], Prefix) :-
    shared_prefix(GoalsA, GoalsB, Prefix0),
    foldl(trim_shared_prefix, Rest, Prefix0, Prefix).

trim_shared_prefix(entry(_, _, _, _, _, Goals), CurrentPrefix, Prefix) :-
    shared_prefix(CurrentPrefix, Goals, Prefix).

shared_prefix([GoalA | RestA], [GoalB | RestB], [GoalA | PrefixRest]) :-
    GoalA =@= GoalB,
    !,
    shared_prefix(RestA, RestB, PrefixRest).
shared_prefix(_, _, []).

all_entries_safe([]).
all_entries_safe([entry(_, Generator, _, _, _, _) | Rest]) :-
    \+ generator_unsafe(Generator),
    all_entries_safe(Rest).

generator_unsafe((A, B)) :-
    (generator_unsafe(A) ; generator_unsafe(B)),
    !.
generator_unsafe((A ; B)) :-
    (generator_unsafe(A) ; generator_unsafe(B)),
    !.
generator_unsafe(Goal) :-
    has_cut(Goal),
    !.
generator_unsafe(Goal) :-
    callable(Goal),
    has_side_effects(Goal),
    !.
generator_unsafe(Goal) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    member(Name/Arity, [call/1, call/2, call/3, call/4, once/1]).

build_splice_helper(Head, Id, List, Entries, SharedPrefix, SpliceCall, Reverses, [BaseClause, StepClause]) :-
    functor(Head, PredicateName, _),
    atomic_list_concat([loop_splice, PredicateName, Id], '_', HelperName),
    build_accumulator_pairs(Entries, PairSpecs, Reverses),
    pair_head_arguments(PairSpecs, BaseArguments),
    BaseHead =.. [HelperName, [] | BaseArguments],
    BaseClause = ir_clause(base(HelperName), BaseHead, [], []),
    pair_step_arguments(PairSpecs, StepArguments),
    first_entry_variable(Entries, X),
    StepHead =.. [HelperName, [X | Xs] | StepArguments],
    build_success_goals(PairSpecs, SuccessGoals),
    success_and_failure_terms(SharedPrefix, SuccessGoals, PairSpecs, Xs, HelperName, BranchTerm),
    StepClause = ir_clause(step(HelperName), StepHead, [BranchTerm], []),
    build_call_arguments(List, PairSpecs, CallArguments),
    SpliceCall =.. [HelperName | CallArguments].

build_accumulator_pairs([], [], []).
build_accumulator_pairs([entry(Template, _Generator, Output, _X, _List, RestGoals) | Rest],
                        [pair(AccIn, AccNext, AccOut, Template, RestGoals) | PairRest],
                        [reverse(AccOut, Output) | ReverseRest]) :-
    build_accumulator_pairs(Rest, PairRest, ReverseRest).

pair_head_arguments([], []).
pair_head_arguments([pair(AccIn, _AccNext, AccOut, _Template, _RestGoals) | Rest], [AccIn, AccIn | ArgsRest]) :-
    AccOut = AccIn,
    pair_head_arguments(Rest, ArgsRest).

pair_step_arguments([], []).
pair_step_arguments([pair(AccIn, _AccNext, AccOut, _Template, _RestGoals) | Rest], [AccIn, AccOut | ArgsRest]) :-
    pair_step_arguments(Rest, ArgsRest).

first_entry_variable([entry(_, _, _, X, _, _) | _], X).

build_success_goals([], []).
build_success_goals([pair(AccIn, AccNext, _AccOut, Template, RestGoals) | Rest], Goals) :-
    build_template_goal(RestGoals, Template, AccIn, AccNext, Goal),
    build_success_goals(Rest, RestGoalsList),
    append([Goal], RestGoalsList, Goals).

build_template_goal([], Template, AccIn, AccNext, (AccNext = [Template | AccIn])).
build_template_goal(RestGoals, Template, AccIn, AccNext, Goal) :-
    goals_to_term(RestGoals, RestTerm),
    Goal = (RestTerm -> AccNext = [Template | AccIn] ; AccNext = AccIn).

success_and_failure_terms(SharedPrefix, SuccessGoals, PairSpecs, Xs, HelperName, BranchTerm) :-
    build_recursive_call(PairSpecs, Xs, HelperName, SuccessRecCall),
    append(SuccessGoals, [SuccessRecCall], SuccessBodyGoals),
    goals_to_term(SuccessBodyGoals, SuccessBody),
    build_failure_goals(PairSpecs, FailureGoals),
    build_recursive_call(PairSpecs, Xs, HelperName, FailureRecCall),
    append(FailureGoals, [FailureRecCall], FailureBodyGoals),
    goals_to_term(FailureBodyGoals, FailureBody),
    goals_to_term(SharedPrefix, SharedPrefixTerm),
    BranchTerm = (SharedPrefixTerm -> SuccessBody ; FailureBody).

build_failure_goals([], []).
build_failure_goals([pair(AccIn, AccNext, _AccOut, _Template, _RestGoals) | Rest], [AccNext = AccIn | GoalsRest]) :-
    build_failure_goals(Rest, GoalsRest).

build_recursive_call(PairSpecs, Xs, HelperName, RecCall) :-
    recursive_call_arguments(PairSpecs, RecursiveArgs),
    RecCall =.. [HelperName, Xs | RecursiveArgs].

recursive_call_arguments([], []).
recursive_call_arguments([pair(_AccIn, AccNext, AccOut, _Template, _RestGoals) | Rest], [AccNext, AccOut | ArgsRest]) :-
    recursive_call_arguments(Rest, ArgsRest).

build_call_arguments(List, PairSpecs, [List | Args]) :-
    initial_call_arguments(PairSpecs, Args).

initial_call_arguments([], []).
initial_call_arguments([pair(_AccIn, _AccNext, AccOut, _Template, _RestGoals) | Rest], [[], AccOut | ArgsRest]) :-
    initial_call_arguments(Rest, ArgsRest).

remove_spliced_findalls(Body, Entries, RemainingGoals) :-
    findall(
        Goal,
        (
            member(Goal, Body),
            \+ goal_is_spliced_entry(Goal, Entries)
        ),
        RemainingGoals
    ).

goal_is_spliced_entry(findall(Template, Generator, Output), Entries) :-
    member(entry(Template, Generator, Output, _, _, _), Entries),
    !.

split_member_generator(Generator, X, List, RestGoals) :-
    split_goals(Generator, [member(X, List) | RestGoals]),
    RestGoals \== [].

split_goals((A, B), Goals) :-
    !,
    split_goals(A, LeftGoals),
    split_goals(B, RightGoals),
    append(LeftGoals, RightGoals, Goals).
split_goals(true, []) :-
    !.
split_goals(Goal, [Goal]).

goals_to_term([], true).
goals_to_term([Goal], Goal) :-
    !.
goals_to_term([Goal | Rest], (Goal, RestTerm)) :-
    goals_to_term(Rest, RestTerm).
