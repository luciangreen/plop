:- module(nd_classify, [
    nd_classify_program/3,
    nd_classify_predicate/4,
    nd_goal_class/3,
    nd_body_class/4,
    can_convert_1_to_1/3
]).

:- use_module(safety, [has_side_effects/1, has_cut/1, classify_goal_safety/2]).
:- use_module(mnn_signature, [mnn_signature/2, mnn_lookup_class/2]).

:- dynamic nd_decl/2.

% -----------------------------------------------------------------------
% Declaration directive handlers.
% The following term_expansion clauses let users write:
%   :- pure myPred/2.
%   :- expensive myPred/2.
%   :- memo_safe myPred/2.
%   :- no_hoist myPred/2.
%   :- no_loop_convert myPred/2.
%   :- output_template myPred/2.
%   :- enumerator myPred/2.
%   :- deterministic myPred/2.
%   :- nondet myPred/2.
%   :- mnn_signature myPred/2, Signature.
% These are translated to nd_decl/2 facts at load time.
% -----------------------------------------------------------------------
nd_decl_keyword(pure).
nd_decl_keyword(deterministic).
nd_decl_keyword(nondet).
nd_decl_keyword(expensive).
nd_decl_keyword(memo_safe).
nd_decl_keyword(no_hoist).
nd_decl_keyword(no_loop_convert).
nd_decl_keyword(output_template).
nd_decl_keyword(enumerator).

user:term_expansion((:- Decl), []) :-
    compound(Decl),
    Decl =.. [Keyword, Pred],
    nd_decl_keyword(Keyword),
    !,
    assertz(nd_decl(Pred, Keyword)).

user:term_expansion((:- mnn_signature(Pred, Sig)), []) :-
    !,
    assertz(nd_decl(Pred, mnn_signature(Sig))).

declare_nd(Pred, Decl) :-
    retractall(nd_decl(Pred, Decl)),
    assertz(nd_decl(Pred, Decl)).

nd_classify_program(ProgramIR, ClassifiedIR, Report) :-
    all_predicates(ProgramIR, Predicates),
    findall(
        nd_classified(Predicate, Class, Reasons),
        (
            member(Predicate, Predicates),
            nd_classify_predicate(Predicate, ProgramIR, Class, Reasons)
        ),
        ClassifyReport
    ),
    mnn_signature_report(Predicates, ProgramIR, MNNReport),
    append(ClassifyReport, MNNReport, Report),
    annotate_program(ProgramIR, ClassifyReport, ClassifiedIR).

mnn_signature_report([], _, []).
mnn_signature_report([Pred | Rest], ProgramIR, [Item | RestItems]) :-
    clauses_for_predicate(Pred, ProgramIR, Clauses),
    (   Clauses == []
    ->  Item = mnn_signature_unknown(Pred)
    ;   Clauses = [Clause | _],
        mnn_signature(Clause, Sig),
        (   mnn_lookup_class(Sig, _Class)
        ->  Item = mnn_signature_matched(Pred, Sig)
        ;   Item = mnn_signature_unknown(Pred)
        )
    ),
    mnn_signature_report(Rest, ProgramIR, RestItems).

annotate_program([], _, []).
annotate_program([ir_clause(Id, Head, Body, Meta) | Rest], Report, [ir_clause(Id, Head, Body, [nd_class(Class) | Meta]) | AnnotatedRest]) :-
    functor(Head, Name, Arity),
    member(nd_classified(Name/Arity, Class, _), Report),
    !,
    annotate_program(Rest, Report, AnnotatedRest).
annotate_program([Clause | Rest], Report, [Clause | AnnotatedRest]) :-
    annotate_program(Rest, Report, AnnotatedRest).

nd_classify_predicate(Predicate, ProgramIR, Class, Reasons) :-
    clauses_for_predicate(Predicate, ProgramIR, Clauses),
    (   Clauses == []
    ->  Class = deterministic,
        Reasons = [not_defined_in_program]
    ;   classify_clauses(Clauses, ProgramIR, Class, Reasons)
    ).

classify_clauses(Clauses, ProgramIR, Class, Reasons) :-
    (   any_clause_matches(body_contains_unsafe_construct, Clauses)
    ->  Class = unsafe_nondeterminism,
        Reasons = [contains_cut_or_unsafe_goal]
    ;   any_clause_matches(body_contains_interpreter_construct, Clauses)
    ->  Class = requires_interpreter_construct,
        Reasons = [contains_meta_call]
    ;   clauses_match_splice_pattern(Clauses)
    ->  Class = splice_compatible,
        Reasons = [repeated_expensive_shared_template]
    ;   clauses_match_fold_pattern(Clauses)
    ->  Class = fold_compatible,
        Reasons = [findall_member_aggregation]
    ;   clauses_match_flatmap_pattern(Clauses)
    ->  Class = flatmap_compatible,
        Reasons = [nested_member_enumerators]
    ;   clauses_match_filter_pattern(Clauses)
    ->  Class = filter_compatible,
        Reasons = [findall_member_condition]
    ;   clauses_match_map_pattern(Clauses)
    ->  Class = map_compatible,
        Reasons = [findall_member_template]
    ;   clauses_have_memo_safe_expensive(Clauses)
    ->  Class = memo_safe_expensive_dependency,
        Reasons = [contains_memo_safe_expensive_subgoal]
    ;   clauses_have_hoistable_expensive(Clauses)
    ->  Class = hoistable_expensive_dependency,
        Reasons = [contains_hoistable_expensive_subgoal]
    ;   clauses_have_enumerator_call(Clauses)
    ->  Class = enumerator,
        Reasons = [generates_multiple_solutions]
    ;   all_clauses_deterministic(Clauses, ProgramIR)
    ->  Class = deterministic,
        Reasons = [no_choicepoints]
    ;   Class = unknown_cost_dependency,
        Reasons = [requires_declarations]
    ).

any_clause_matches(Predicate, Clauses) :-
    member(ir_clause(_, _, Body, _), Clauses),
    call(Predicate, Body),
    !.

body_contains_unsafe_construct(Body) :-
    member(Goal, Body),
    goal_contains_unsafe_construct(Goal),
    !.

body_contains_interpreter_construct(Body) :-
    member(Goal, Body),
    goal_contains_interpreter_construct(Goal),
    !.

goal_contains_unsafe_construct(findall(_, Generator, _)) :-
    generator_contains_unsafe_construct(Generator),
    !.
goal_contains_unsafe_construct(bagof(_, Generator, _)) :-
    generator_contains_unsafe_construct(Generator),
    !.
goal_contains_unsafe_construct(setof(_, Generator, _)) :-
    generator_contains_unsafe_construct(Generator),
    !.
goal_contains_unsafe_construct(Goal) :-
    has_cut(Goal),
    !.
goal_contains_unsafe_construct(Goal) :-
    unsafe_effect_goal(Goal),
    !.

generator_contains_unsafe_construct((A, B)) :-
    (generator_contains_unsafe_construct(A) ; generator_contains_unsafe_construct(B)),
    !.
generator_contains_unsafe_construct((A ; B)) :-
    (generator_contains_unsafe_construct(A) ; generator_contains_unsafe_construct(B)),
    !.
generator_contains_unsafe_construct(Goal) :-
    goal_contains_unsafe_construct(Goal).

goal_contains_interpreter_construct(findall(_, Generator, _)) :-
    generator_contains_interpreter_construct(Generator),
    !.
goal_contains_interpreter_construct(bagof(_, Generator, _)) :-
    generator_contains_interpreter_construct(Generator),
    !.
goal_contains_interpreter_construct(setof(_, Generator, _)) :-
    generator_contains_interpreter_construct(Generator),
    !.
goal_contains_interpreter_construct(Goal) :-
    meta_call_goal(Goal),
    !.

generator_contains_interpreter_construct((A, B)) :-
    (generator_contains_interpreter_construct(A) ; generator_contains_interpreter_construct(B)),
    !.
generator_contains_interpreter_construct((A ; B)) :-
    (generator_contains_interpreter_construct(A) ; generator_contains_interpreter_construct(B)),
    !.
generator_contains_interpreter_construct(Goal) :-
    goal_contains_interpreter_construct(Goal).

unsafe_effect_goal(Goal) :-
    callable(Goal),
    \+ is_findall_goal(Goal),
    has_side_effects(Goal).
unsafe_effect_goal(Goal) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    member(Name/Arity, [random/1, random/3, var/1, nonvar/1]).

meta_call_goal(Goal) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    member(Name/Arity, [
        call/1, call/2, call/3, call/4, call/5,
        once/1, ignore/1, forall/2,
        maplist/2, maplist/3, maplist/4
    ]).

nd_body_class(Body, _Context, Class, DependencyGraph) :-
    build_simple_dep_graph(Body, DependencyGraph),
    (   body_contains_unsafe_construct(Body)
    ->  Class = unsafe_nondeterminism
    ;   body_contains_interpreter_construct(Body)
    ->  Class = requires_interpreter_construct
    ;   body_has_splice_pattern(Body)
    ->  Class = splice_compatible
    ;   body_has_fold_pattern(Body)
    ->  Class = fold_compatible
    ;   body_has_flatmap_pattern(Body)
    ->  Class = flatmap_compatible
    ;   body_has_filter_pattern(Body)
    ->  Class = filter_compatible
    ;   body_has_map_pattern(Body)
    ->  Class = map_compatible
    ;   body_has_memo_safe_expensive(Body)
    ->  Class = memo_safe_expensive_dependency
    ;   body_has_hoistable_expensive(Body)
    ->  Class = hoistable_expensive_dependency
    ;   body_has_enumerator(Body)
    ->  Class = enumerator
    ;   body_is_deterministic(Body)
    ->  Class = deterministic
    ;   Class = unknown_cost_dependency
    ).

nd_goal_class(Goal, _Context, Class) :-
    (   goal_contains_unsafe_construct(Goal)
    ->  Class = unsafe_nondeterminism
    ;   goal_contains_interpreter_construct(Goal)
    ->  Class = requires_interpreter_construct
    ;   is_findall_goal(Goal),
        Goal =.. [_Functor, _Template, Generator, _Output],
        generator_pattern(Generator, PatternClass)
    ->  Class = PatternClass
    ;   member_call(Goal)
    ->  Class = enumerator
    ;   known_deterministic_goal(Goal)
    ->  Class = deterministic
    ;   Class = unknown_cost_dependency
    ).

can_convert_1_to_1(Predicate, ProgramIR, Decision) :-
    nd_classify_predicate(Predicate, ProgramIR, Class, Reasons),
    class_decision(Class, Reasons, Decision).

class_decision(unsafe_nondeterminism, Reasons, no(unsafe_nd(Reasons))) :- !.
class_decision(requires_interpreter_construct, _Reasons, no(meta_call_required)) :- !.
class_decision(deterministic, _Reasons, yes(deterministic, no_transform_needed)) :- !.
class_decision(map_compatible, _Reasons, yes(map_compatible, transform_findall_to_accumulator_loop)) :- !.
class_decision(fold_compatible, _Reasons, yes(fold_compatible, transform_findall_to_fold_loop)) :- !.
class_decision(flatmap_compatible, _Reasons, yes(flatmap_compatible, transform_to_nested_loops)) :- !.
class_decision(filter_compatible, _Reasons, yes(filter_compatible, transform_findall_to_filter_loop)) :- !.
class_decision(splice_compatible, _Reasons, yes(splice_compatible, transform_to_spliced_template_loop)) :- !.
class_decision(dependent_nested_loop, _Reasons, yes(dependent_nested_loop, transform_to_nested_dependent_loops)) :- !.
class_decision(hoistable_expensive_dependency, _Reasons,
               yes(hoistable_expensive_dependency, hoist_expensive_subgoals)) :- !.
class_decision(memo_safe_expensive_dependency, _Reasons,
               yes(memo_safe_expensive_dependency, memoise_expensive_subgoals)) :- !.
class_decision(enumerator, _Reasons,
               unknown(enumerator_may_produce_multiple_answers,
                       [':- deterministic Pred/Arity.', ':- enumerator Pred/Arity.'])) :- !.
class_decision(unknown_cost_dependency, _Reasons,
               unknown(unknown_cost_dependency,
                       [':- expensive Pred/Arity.', ':- memo_safe Pred/Arity.'])) :- !.
class_decision(_Class, _Reasons, unknown(classification_incomplete, [])).

all_predicates(ProgramIR, Predicates) :-
    findall(
        Name/Arity,
        (
            member(ir_clause(_, Head, _, _), ProgramIR),
            functor(Head, Name, Arity)
        ),
        Predicates0
    ),
    sort(Predicates0, Predicates).

clauses_for_predicate(Name/Arity, ProgramIR, Clauses) :-
    include(matches_predicate(Name/Arity), ProgramIR, Clauses).

matches_predicate(Name/Arity, ir_clause(_, Head, _, _)) :-
    functor(Head, Name, Arity).

all_clauses_deterministic([], _).
all_clauses_deterministic([ir_clause(_, _, Body, _) | Rest], _ProgramIR) :-
    body_is_deterministic(Body),
    all_clauses_deterministic(Rest, _ProgramIR).

clauses_match_map_pattern(Clauses) :-
    member(ir_clause(_, _, Body, _), Clauses),
    body_has_map_pattern(Body),
    !.

clauses_match_fold_pattern(Clauses) :-
    member(ir_clause(_, _, Body, _), Clauses),
    body_has_fold_pattern(Body),
    !.

clauses_match_flatmap_pattern(Clauses) :-
    member(ir_clause(_, _, Body, _), Clauses),
    body_has_flatmap_pattern(Body),
    !.

clauses_match_filter_pattern(Clauses) :-
    member(ir_clause(_, _, Body, _), Clauses),
    body_has_filter_pattern(Body),
    !.

clauses_match_splice_pattern(Clauses) :-
    member(ir_clause(_, _, Body, _), Clauses),
    body_has_splice_pattern(Body),
    !.

clauses_have_enumerator_call(Clauses) :-
    member(ir_clause(_, _, Body, _), Clauses),
    body_has_enumerator(Body),
    !.

clauses_have_hoistable_expensive(Clauses) :-
    member(ir_clause(_, _, Body, _), Clauses),
    body_has_hoistable_expensive(Body),
    !.

clauses_have_memo_safe_expensive(Clauses) :-
    member(ir_clause(_, _, Body, _), Clauses),
    body_has_memo_safe_expensive(Body),
    !.

body_has_hoistable_expensive(Body) :-
    member(Goal, Body),
    is_expensive_heuristic(Goal),
    \+ goal_contains_unsafe_construct(Goal),
    \+ has_cut(Goal),
    \+ has_side_effects(Goal),
    !.

body_has_memo_safe_expensive(Body) :-
    member(Goal, Body),
    callable(Goal),
    functor(Goal, Name, Arity),
    nd_decl(Name/Arity, memo_safe),
    !.

%% expensive_predicate_name/1
%  Well-known expensive predicate names used as a heuristic when no explicit
%  :- expensive/1 declaration is present. Extend as needed.
expensive_predicate_name(expensive).
expensive_predicate_name(costly).
expensive_predicate_name(heavy).
expensive_predicate_name(slow).
expensive_predicate_name(compute).
expensive_predicate_name(big_computation).
expensive_predicate_name(matrix_multiply).
expensive_predicate_name(solve).
expensive_predicate_name(search).
expensive_predicate_name(db_query).
expensive_predicate_name(file_read).
expensive_predicate_name(network_call).

is_expensive_heuristic(Goal) :-
    callable(Goal),
    functor(Goal, Name, _),
    expensive_predicate_name(Name).

body_has_map_pattern(Body) :-
    member(findall(_, Generator, _), Body),
    generator_pattern(Generator, map_compatible).

body_has_fold_pattern(Body) :-
    member(findall(_, Generator, _), Body),
    generator_starts_with_member(Generator),
    member(sum_list(_, _), Body).

body_has_flatmap_pattern(Body) :-
    member(findall(_, Generator, _), Body),
    generator_pattern(Generator, flatmap_compatible).

body_has_filter_pattern(Body) :-
    member(findall(_, Generator, _), Body),
    generator_pattern(Generator, filter_compatible).

body_has_splice_pattern(Body) :-
    findall(entry(List, RestGoals), (
        member(findall(_, Generator, _), Body),
        split_member_generator(Generator, _X, List, RestGoals)
    ), Entries),
    Entries = [_, _ | _],
    shared_splice_entries(Entries).

shared_splice_entries(Entries) :-
    member(entry(List, RestA), Entries),
    member(entry(List2, RestB), Entries),
    List == List2,
    RestA \== [],
    RestB \== [],
    shared_prefix(RestA, RestB, Prefix),
    Prefix \== [],
    !.

body_has_enumerator(Body) :-
    member(Goal, Body),
    member_call(Goal).

body_is_deterministic([]).
body_is_deterministic([Goal | Rest]) :-
    \+ member_call(Goal),
    \+ is_findall_goal(Goal),
    \+ goal_contains_unsafe_construct(Goal),
    \+ goal_contains_interpreter_construct(Goal),
    body_is_deterministic(Rest).

generator_pattern(Generator, flatmap_compatible) :-
    split_goals(Generator, [First, _Middle, Third | _]),
    member_call(First),
    member_call(Third),
    !.
generator_pattern(Generator, filter_compatible) :-
    split_goals(Generator, [First, Second | _]),
    member_call(First),
    is_condition_goal(Second),
    !.
generator_pattern(Generator, map_compatible) :-
    generator_starts_with_member(Generator),
    !.

generator_starts_with_member(Generator) :-
    split_goals(Generator, [First | _]),
    member_call(First).

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

shared_prefix([GoalA | RestA], [GoalB | RestB], [GoalA | PrefixRest]) :-
    GoalA =@= GoalB,
    !,
    shared_prefix(RestA, RestB, PrefixRest).
shared_prefix(_, _, []).

build_simple_dep_graph(Body, Graph) :-
    findall(
        depends(GoalIndex, DependencyIndex),
        (
            nth0(GoalIndex, Body, Goal),
            nth0(DependencyIndex, Body, DependencyGoal),
            DependencyIndex < GoalIndex,
            term_variables(Goal, GoalVars),
            term_variables(DependencyGoal, DependencyVars),
            shares_variable(GoalVars, DependencyVars)
        ),
        Graph
    ).

shares_variable(VarsA, VarsB) :-
    member(VarA, VarsA),
    member(VarB, VarsB),
    VarA == VarB,
    !.

known_deterministic_goal(Goal) :-
    classify_goal_safety(Goal, safe),
    \+ member_call(Goal),
    \+ is_findall_goal(Goal),
    \+ meta_call_goal(Goal).

is_condition_goal(Goal) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    (   Arity =:= 1,
        Name == '\\+'
    ;   Arity =:= 2,
        member(Name, ['>', '<', '>=', '=<', '=:=', '=\\=', '==', '\\=='])
    ).

member_call(member(_, _)).
member_call(between(_, _, _)).
member_call(nth0(_, _, _)).
member_call(nth1(_, _, _)).

is_findall_goal(findall(_, _, _)).
is_findall_goal(bagof(_, _, _)).
is_findall_goal(setof(_, _, _)).
