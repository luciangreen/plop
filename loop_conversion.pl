:- module(loop_conversion, [convert_deterministic_loops/3]).

% Stage 11 — Deterministic Loop Conversion.
%
% Converts safe `findall/3` enumeration patterns into deterministic helper
% loops. Supported enumerators:
%   - member/2
%   - between/3
%   - nth0/3
%   - nth1/3
%
% Example conversion:
%   findall(Y, (member(X, L), process(X, Y)), Ys)
% becomes:
%   loop_member_...(L, Ys)
% with generated deterministic helper clauses.

convert_deterministic_loops(ProgramIR, OptimisedIR, Report) :-
    convert_clauses(ProgramIR, OptimisedClauses, HelperClauses, [], ReportRaw),
    append(OptimisedClauses, HelperClauses, OptimisedIR),
    sort(ReportRaw, Report).

convert_clauses([], [], [], Report, Report).
convert_clauses([Clause | Rest], [ConvertedClause | ConvertedRest], HelpersOut, Report0, Report) :-
    convert_clause(Clause, ConvertedClause, HelpersHere, Item),
    (   nonvar(Item)
    ->  Report1 = [Item | Report0]
    ;   Report1 = Report0
    ),
    convert_clauses(Rest, ConvertedRest, HelpersRest, Report1, Report),
    append(HelpersHere, HelpersRest, HelpersOut).

convert_clause(
    ir_clause(Id, Head, Body, Meta),
    ir_clause(Id, Head, ConvertedBody, Meta),
    HelperClauses,
    ReportItem
) :-
    (   rewrite_findall_to_loop(Head, Id, Body, ConvertedBody, HelperClauses)
    ->  predicate_from_head(Head, Pred),
        ReportItem = loop_converted(Pred)
    ;   ConvertedBody = Body,
        HelperClauses = []
    ).

rewrite_findall_to_loop(Head, Id, Body, ConvertedBody, HelperClauses) :-
    append(Prefix, [Goal | Suffix], Body),
    convert_findall_goal(Head, Id, Goal, ReplacementGoal, HelperClauses),
    !,
    append(Prefix, [ReplacementGoal | Suffix], ConvertedBody).

convert_findall_goal(Head, Id, findall(Y, Generator, Ys), Replacement, HelperClauses) :-
    var(Y),
    var(Ys),
    generator_map_goal(Generator, Enumerator, X, SourceA, SourceB, MapGoal),
    allowed_map_vars(Enumerator, X, Y, SourceB, AllowedVars),
    map_goal_safe(MapGoal, AllowedVars),
    helper_name(Head, Id, Enumerator, HelperName),
    build_helper(
        Enumerator,
        HelperName,
        X,
        Y,
        SourceA,
        SourceB,
        MapGoal,
        Replacement,
        HelperClauses
    ).

generator_map_goal((member(X, List), Goal), member, X, List, _, Goal).
generator_map_goal((between(Start, End, X), Goal), between, X, Start, End, Goal).
generator_map_goal((nth0(Index, List, X), Goal), nth0, X, List, Index, Goal).
generator_map_goal((nth1(Index, List, X), Goal), nth1, X, List, Index, Goal).

allowed_map_vars(member, X, Y, _, [X, Y]).
allowed_map_vars(between, X, Y, _, [X, Y]).
allowed_map_vars(nth0, X, Y, Index, [Index, X, Y]).
allowed_map_vars(nth1, X, Y, Index, [Index, X, Y]).

build_helper(member, HelperName, X, Y, List, _, MapGoal, Replacement, [BaseClause, StepClause]) :-
    copy_term((X, Y, MapGoal), (HX, HY, HGoal)),
    Replacement =.. [HelperName, List, Ys],
    BaseHead =.. [HelperName, [], []],
    StepHead =.. [HelperName, [HX | Xs], [HY | Ys]],
    StepCall =.. [HelperName, Xs, Ys],
    BaseClause = ir_clause(base(HelperName), BaseHead, [], []),
    StepClause = ir_clause(step(HelperName), StepHead, [HGoal, StepCall], []).
build_helper(between, HelperName, X, Y, Start, End, MapGoal, Replacement, [BaseClause, StepClause]) :-
    copy_term((X, Y, MapGoal), (HX, HY, HGoal)),
    Replacement =.. [HelperName, Start, End, Ys],
    BaseHead =.. [HelperName, Cur, Last, []],
    StepHead =.. [HelperName, Cur, Last, [HY | Ys]],
    StepCall =.. [HelperName, Next, Last, Ys],
    BaseClause = ir_clause(base(HelperName), BaseHead, [Cur > Last], []),
    StepClause = ir_clause(
        step(HelperName),
        StepHead,
        [Cur =< Last, HX = Cur, HGoal, Next is Cur + 1, StepCall],
        []
    ).
build_helper(nth0, HelperName, X, Y, List, IndexVar, MapGoal, Replacement, [BaseClause, StepClause]) :-
    copy_term((IndexVar, X, Y, MapGoal), (HIndex, HX, HY, HGoal)),
    Replacement =.. [HelperName, List, 0, Ys],
    BaseHead =.. [HelperName, [], _, []],
    StepHead =.. [HelperName, [HX | Xs], Index, [HY | Ys]],
    StepCall =.. [HelperName, Xs, NextIndex, Ys],
    BaseClause = ir_clause(base(HelperName), BaseHead, [], []),
    StepClause = ir_clause(
        step(HelperName),
        StepHead,
        [HIndex = Index, HGoal, NextIndex is Index + 1, StepCall],
        []
    ).
build_helper(nth1, HelperName, X, Y, List, IndexVar, MapGoal, Replacement, [BaseClause, StepClause]) :-
    copy_term((IndexVar, X, Y, MapGoal), (HIndex, HX, HY, HGoal)),
    Replacement =.. [HelperName, List, 1, Ys],
    BaseHead =.. [HelperName, [], _, []],
    StepHead =.. [HelperName, [HX | Xs], Index, [HY | Ys]],
    StepCall =.. [HelperName, Xs, NextIndex, Ys],
    BaseClause = ir_clause(base(HelperName), BaseHead, [], []),
    StepClause = ir_clause(
        step(HelperName),
        StepHead,
        [HIndex = Index, HGoal, NextIndex is Index + 1, StepCall],
        []
    ).

predicate_from_head(Head, Name/Arity) :-
    functor(Head, Name, Arity).

helper_name(Head, Id, Enumerator, HelperName) :-
    predicate_from_head(Head, PredName/_),
    atomic_list_concat([loop, Enumerator, PredName, Id], '_', HelperName).

map_goal_safe(Goal, AllowedVars) :-
    callable(Goal),
    \+ unsafe_goal(Goal),
    term_variables(Goal, Vars),
    all_vars_allowed(Vars, AllowedVars).

all_vars_allowed([], _).
all_vars_allowed([Var | Rest], AllowedVars) :-
    member_var_eq(Var, AllowedVars),
    all_vars_allowed(Rest, AllowedVars).

member_var_eq(Var, [Candidate | _]) :-
    Var == Candidate,
    !.
member_var_eq(Var, [_ | Rest]) :-
    member_var_eq(Var, Rest).

unsafe_goal(Goal) :-
    (   var(Goal)
    ;   Goal = (_,_)
    ;   Goal = (_;_)
    ;   Goal = (_->_)
    ;   Goal = (_*->_)
    ;   Goal = !
    ;   callable(Goal),
        functor(Goal, Name, Arity),
        unsafe_predicate(Name/Arity)
    ),
    !.

unsafe_predicate(Pred) :-
    member(Pred, [call/1, call/2, call/3, call/4, once/1, ignore/1,
                  findall/3, bagof/3, setof/3, maplist/2, maplist/3,
                  maplist/4, forall/2]).
unsafe_predicate(Pred) :-
    member(Pred, [write/1, writeln/1, print/1, format/2, format/3, read/1,
                  read_term/2, read_term/3, open/3, close/1, close/2, nl/0,
                  put_char/1, get_char/1, get_code/1, see/1, tell/1]).
