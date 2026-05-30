:- module(nd_to_loop, [
    nd_to_loop_program/3,
    nd_to_loop_predicate/4,
    convert_findall_to_loop/3,
    convert_map_to_loop/3,
    convert_fold_to_loop/3,
    convert_flatmap_to_nested_loop/3,
    convert_splice_templates/3
]).

% Stage 19b — Nondeterminism-to-Determinism Loop Converter.
%
% Takes classified IR from nd_classify and rewrites findall/member patterns
% into deterministic helper loops, accumulator folds, nested loops, or
% spliced template loops.
%
% Supported transformations:
%   map_compatible    -> accumulator loop with reverse/2
%   fold_compatible   -> accumulator fold loop (no reverse needed)
%   flatmap_compatible -> nested accumulator loops
%   splice_compatible  -> single shared-loop with multiple accumulators
%
% Safety rules:
%   - No transformation when body contains cut, IO, random, var-sensitive logic.
%   - Meta-calls (call/N) are blocked unless declared safe.
%   - Disjunction is blocked unless it can be converted to a tagged branch.

:- use_module(nd_classify, [nd_classify_predicate/4, can_convert_1_to_1/3]).
:- use_module(safety, [has_side_effects/1, has_cut/1]).

%% nd_to_loop_program(+ProgramIR, -OptimisedIR, -Report) is det.
nd_to_loop_program(ProgramIR, OptimisedIR, Report) :-
    convert_nd_clauses(ProgramIR, ProgramIR, ConvertedClauses, HelperClauses, [], ReportRaw),
    append(ConvertedClauses, HelperClauses, OptimisedIR),
    sort(ReportRaw, Report).

convert_nd_clauses([], _, [], [], Report, Report).
convert_nd_clauses([Clause | Rest], ProgramIR, [Conv | ConvRest], HelpersOut, Report0, Report) :-
    convert_nd_clause(Clause, ProgramIR, Conv, HelpersHere, Item),
    (   nonvar(Item) -> Report1 = [Item | Report0] ; Report1 = Report0 ),
    convert_nd_clauses(Rest, ProgramIR, ConvRest, HelpersRest, Report1, Report),
    append(HelpersHere, HelpersRest, HelpersOut).

convert_nd_clause(Clause, ProgramIR, ConvClause, Helpers, Item) :-
    Clause = ir_clause(Id, Head, Body, Meta),
    (   rewrite_findall_body(Head, Id, Body, ProgramIR, ConvBody, Helpers)
    ->  ConvClause = ir_clause(Id, Head, ConvBody, Meta),
        functor(Head, Name, Arity),
        Item = nd_loop_converted(Name/Arity)
    ;   ConvClause = Clause,
        Helpers = []
    ).

rewrite_findall_body(Head, Id, Body, ProgramIR, ConvBody, Helpers) :-
    append(Prefix, [Goal | Suffix], Body),
    convert_findall_goal(Head, Id, Goal, ProgramIR, Replacement, Helpers),
    !,
    append(Prefix, [Replacement | Suffix], ConvBody).

convert_findall_goal(Head, Id, findall(Template, Generator, Out),
                     ProgramIR, Replacement, Helpers) :-
    classify_generator(Generator, Template, Pattern),
    \+ generator_unsafe(Generator),
    build_nd_loop(Pattern, Head, Id, Template, Generator, Out, ProgramIR,
                  Replacement, Helpers).

%% nd_to_loop_predicate(+Predicate, +ProgramIR, -OptimisedIR, -Report) is det.
nd_to_loop_predicate(Pred, ProgramIR, OptimisedIR, Report) :-
    can_convert_1_to_1(Pred, ProgramIR, Decision),
    (   Decision = yes(_, _)
    ->  nd_to_loop_program(ProgramIR, OptimisedIR, Report)
    ;   Decision = no(Reason)
    ->  OptimisedIR = ProgramIR,
        Report = [skipped_nd_conversion(Pred, Reason)]
    ;   Decision = unknown(Reason, Decls)
    ->  OptimisedIR = ProgramIR,
        Report = [nd_conversion_unknown(Pred, Reason, Decls)]
    ).

%% convert_findall_to_loop(+Clause, -LoopClause, -Report) is det.
%
% Convert a single clause's findall/member/template pattern to a loop call.
% LoopClause will call a helper; helper clauses are embedded in Report.
convert_findall_to_loop(Clause, LoopClause, Report) :-
    Clause = ir_clause(Id, Head, Body, Meta),
    (   member(findall(Template, (member(X, List), MapGoal), Out), Body),
        var(Out),
        \+ generator_unsafe(MapGoal),
        helper_name(Head, Id, member, HelperName),
        map_helper_name(HelperName, Head, Id, member, List, Template, X,
                        MapGoal, Out, CallGoal, BaseClause, StepClause)
    ->  replace_findall_in_body(Body,
            findall(Template, (member(X, List), MapGoal), Out),
            [CallGoal, reverse(Out0, Out)], Body1),
        LoopClause = ir_clause(Id, Head, Body1, Meta),
        functor(Head, Name, Arity),
        Report = [nd_map_converted(Name/Arity), BaseClause, StepClause]
    ;   LoopClause = Clause,
        Report = []
    ).

%% convert_map_to_loop(+Clause, -LoopClause, -Report) is det.
convert_map_to_loop(Clause, LoopClause, Report) :-
    convert_findall_to_loop(Clause, LoopClause, Report).

%% convert_fold_to_loop(+Clause, -LoopClause, -Report) is det.
%
% Converts findall/member/value + sum_list into a fold loop.
convert_fold_to_loop(Clause, LoopClause, Report) :-
    Clause = ir_clause(Id, Head, Body, Meta),
    (   member(findall(V, (member(X, List), ScoreGoal), Vs), Body),
        member(sum_list(Vs, Total), Body),
        var(Vs), var(Total), var(V),
        \+ generator_unsafe(ScoreGoal),
        helper_name(Head, Id, fold, HelperName),
        copy_term(X-V-ScoreGoal, HX-HV-HGoal),
        BaseHead  =.. [HelperName, [], Acc, Acc],
        StepHead  =.. [HelperName, [HX|Xs], Acc0, TotalOut],
        Acc1Expr  =.. [is, Acc1, Acc0 + HV],
        RecCall   =.. [HelperName, Xs, Acc1, TotalOut],
        StepBody  = [HGoal, Acc1Expr, RecCall],
        BaseClause = ir_clause(base(HelperName), BaseHead, [], []),
        StepClause = ir_clause(step(HelperName), StepHead, StepBody, []),
        CallGoal  =.. [HelperName, List, 0, Total]
    ->  delete_goals(Body,
            [findall(V,(member(X,List),ScoreGoal),Vs), sum_list(Vs,Total)],
            Body1),
        Body2 = [CallGoal | Body1],
        LoopClause = ir_clause(Id, Head, Body2, Meta),
        functor(Head, Name, Arity),
        Report = [nd_fold_converted(Name/Arity), BaseClause, StepClause]
    ;   LoopClause = Clause,
        Report = []
    ).

%% convert_flatmap_to_nested_loop(+Clause, -LoopClause, -Report) is det.
%
% Converts nested-member findall into nested deterministic loops.
convert_flatmap_to_nested_loop(Clause, LoopClause, Report) :-
    Clause = ir_clause(Id, Head, Body, Meta),
    (   member(findall(Z, (member(X, Xs), ExpGoal, member(Y, A), TrGoal), Out), Body),
        var(Z), var(Out),
        \+ generator_unsafe(ExpGoal),
        \+ generator_unsafe(TrGoal),
        outer_helper_name(Head, Id, OuterName),
        inner_helper_name(Head, Id, InnerName),
        copy_term(X-ExpGoal, HX-HExp),
        copy_term(X-Y-Z-TrGoal, IX-IY-IZ-ITr),
        OuterBase = ir_clause(base(OuterName),
            (OuterBase_H =.. [OuterName, [], Acc, Acc], OuterBase_H),
            [], []),
        OuterStep_H =.. [OuterName, [HX|XXs], Acc0, OutFin],
        InnerCall   =.. [InnerName, IX, A, Acc0, Acc1],
        OuterRec    =.. [OuterName, XXs, Acc1, OutFin],
        OuterBase2  =.. [OuterName, [], Acc2, Acc2],
        OuterBase_Clause = ir_clause(base(OuterName), OuterBase2, [], []),
        OuterStep_Clause = ir_clause(step(OuterName), OuterStep_H,
                               [HExp, InnerCall, OuterRec], []),
        InnerBase_H =.. [InnerName, _, [], Acc3, Acc3],
        InnerStep_H =.. [InnerName, IX2, [IY|Ys], Acc4, InFin],
        copy_term(IX-IY-IZ-ITr, IX2-IY2-IZ2-ITr2),
        InnerRec    =.. [InnerName, IX2, Ys, [IZ2|Acc4], InFin],
        InnerBase_Clause = ir_clause(base(InnerName), InnerBase_H, [], []),
        InnerStep_Clause = ir_clause(step(InnerName), InnerStep_H,
                               [ITr2, InnerRec], []),
        OuterCall   =.. [OuterName, Xs, [], Rev],
        ignore(IZ2 = IZ),  % ensure binding
        true
    ->  replace_findall_in_body(Body,
            findall(Z,(member(X,Xs),ExpGoal,member(Y,A),TrGoal),Out),
            [OuterCall, reverse(Rev, Out)], Body1),
        LoopClause = ir_clause(Id, Head, Body1, Meta),
        functor(Head, Name, Arity),
        Report = [nd_flatmap_converted(Name/Arity),
                  OuterBase_Clause, OuterStep_Clause,
                  InnerBase_Clause, InnerStep_Clause]
    ;   LoopClause = Clause,
        Report = []
    ).

%% convert_splice_templates(+Clause, -SplicedClause, -Report) is det.
%
% Converts multiple findall/member calls sharing the same expensive subgoal
% into a single shared-loop with multiple accumulator pairs.
convert_splice_templates(Clause, SplicedClause, Report) :-
    Clause = ir_clause(Id, Head, Body, Meta),
    findall(findall(T,G,O)-Idx, (
        nth0(Idx, Body, findall(T,G,O))
    ), Findalls),
    (   Findalls = [_,_|_],
        all_share_enumerator(Findalls, List, Pairs),
        \+ (member(_-G2-_, Pairs), generator_unsafe(G2))
    ->  splice_helper_name(Head, Id, SpliceName),
        build_splice_loop(SpliceName, List, Pairs, SpliceCall, SpliceDefs, Reverses),
        remove_findalls_from_body(Body, Findalls, Body1),
        SpliceGoals = [SpliceCall | Reverses],
        Body2 = SpliceGoals,
        append(Body1Prefix, _, Body1),
        append(Body1Prefix, Body2, Body3),
        LoopBody = Body3,
        LoopClause = ir_clause(Id, Head, LoopBody, Meta),
        functor(Head, Name, Arity),
        Report = [nd_splice_converted(Name/Arity) | SpliceDefs],
        SplicedClause = LoopClause
    ;   SplicedClause = Clause,
        Report = []
    ).

% -----------------------------------------------------------------------
% Generator classification
% -----------------------------------------------------------------------

classify_generator((member(X, List), Goal), Template, map(X, List, Goal, Template)).
classify_generator((member(X, List), Cond, Goal), Template,
                   filter(X, List, Cond, Goal, Template)) :-
    is_condition(Cond).
classify_generator((member(X, Xs), ExpGoal, member(Y, A), TrGoal), Template,
                   flatmap(X, Xs, ExpGoal, Y, A, TrGoal, Template)).
classify_generator(member(X, List), X, enumerator(X, List)).

is_condition(Goal) :-
    callable(Goal),
    functor(Goal, Name, _Arity),
    member(Name, ['>', '<', '>=', '=<', '=:=', '=\\=', '==', '\\==', '\\+']).

generator_unsafe(Goal) :-
    (   has_cut(Goal)
    ;   has_side_effects(Goal)
    ;   compound(Goal), Goal = (A, B),
        (generator_unsafe(A) ; generator_unsafe(B))
    ;   compound(Goal), Goal = (A ; B),
        (generator_unsafe(A) ; generator_unsafe(B))
    ).
generator_unsafe(Goal) :-
    callable(Goal),
    functor(Goal, Name, Arity),
    member(Name/Arity, [call/1, call/2, call/3, once/1, forall/2]).

% -----------------------------------------------------------------------
% Loop building
% -----------------------------------------------------------------------

build_nd_loop(map(X, List, MapGoal, Template), Head, Id, Template, _Gen, Out,
              _ProgramIR, Replacement, [BaseClause, StepClause]) :-
    helper_name(Head, Id, member, HelperName),
    copy_term(X-Template-MapGoal, HX-HT-HGoal),
    Replacement = (LoopCall, reverse(Rev, Out)),
    LoopCall =.. [HelperName, List, [], Rev],
    BaseHead =.. [HelperName, [], Acc, Acc],
    StepHead =.. [HelperName, [HX|Xs], Acc0, Res],
    StepRec  =.. [HelperName, Xs, [HT|Acc0], Res],
    BaseClause = ir_clause(base(HelperName), BaseHead, [], []),
    StepClause = ir_clause(step(HelperName), StepHead, [HGoal, StepRec], []).

build_nd_loop(flatmap(X, Xs, ExpGoal, Y, A, TrGoal, Template),
              Head, Id, Template, _Gen, Out,
              _ProgramIR, Replacement, [OutBase, OutStep, InBase, InStep]) :-
    outer_helper_name(Head, Id, OuterName),
    inner_helper_name(Head, Id, InnerName),
    copy_term(X-ExpGoal, HX-HExp),
    copy_term(X-Y-Template-TrGoal, IX-IY-IT-ITr),
    OutBase_H =.. [OuterName, [], Acc, Acc],
    OutStep_H =.. [OuterName, [HX|XXs], Acc0, OutFin],
    InCall    =.. [InnerName, IX, A, Acc0, Acc1],
    OutRec    =.. [OuterName, XXs, Acc1, OutFin],
    OutBase   = ir_clause(base(OuterName), OutBase_H, [], []),
    OutStep   = ir_clause(step(OuterName), OutStep_H, [HExp, InCall, OutRec], []),
    InBase_H  =.. [InnerName, _, [], Acc2, Acc2],
    InStep_H  =.. [InnerName, IX2, [IY|Ys], Acc3, InFin],
    copy_term(IX-IY-IT-ITr, IX2-IY2-IT2-ITr2),
    ignore(IY2 = IY), ignore(IT2 = IT),
    InRec     =.. [InnerName, IX2, Ys, [IT2|Acc3], InFin],
    InBase    = ir_clause(base(InnerName), InBase_H, [], []),
    InStep    = ir_clause(step(InnerName), InStep_H, [ITr2, InRec], []),
    LoopCall  =.. [OuterName, Xs, [], Rev],
    Replacement = (LoopCall, reverse(Rev, Out)).

build_nd_loop(filter(X, List, Cond, Goal, Template), Head, Id, Template, _Gen, Out,
              _ProgramIR, Replacement, [BaseClause, StepClause]) :-
    helper_name(Head, Id, filter, HelperName),
    copy_term(X-Template-Cond-Goal, HX-HT-HCond-HGoal),
    LoopCall =.. [HelperName, List, [], Rev],
    Replacement = (LoopCall, reverse(Rev, Out)),
    BaseHead =.. [HelperName, [], Acc, Acc],
    StepHead =.. [HelperName, [HX|Xs], Acc0, Res],
    StepRec  =.. [HelperName, Xs, [HT|Acc0], Res],
    StepRecSkip =.. [HelperName, Xs, Acc0, Res],
    BaseClause = ir_clause(base(HelperName), BaseHead, [], []),
    StepClause = ir_clause(step(HelperName), StepHead,
        [(HCond -> (HGoal, StepRec) ; StepRecSkip)], []).

build_nd_loop(enumerator(X, _List), _Head, _Id, _Template, _Gen, _Out,
              _ProgramIR, _, _) :-
    fail.  % enumerators need explicit declaration to convert

% -----------------------------------------------------------------------
% Splice helpers
% -----------------------------------------------------------------------

all_share_enumerator(Findalls, List, Pairs) :-
    Findalls = [findall(_T1,(member(_X1,List1),G1),Out1)-_ | Rest],
    List = List1,
    Pairs = [T1-G1-Out1 | RestPairs],
    all_same_list(Rest, List1, RestPairs).

all_same_list([], _, []).
all_same_list([findall(T,(member(_X,List),G),Out)-_ | Rest], List, [T-G-Out | Pairs]) :-
    all_same_list(Rest, List, Pairs).

build_splice_loop(SpliceName, List, Pairs, SpliceCall, [BaseClause, StepClause | Reverses], Reverses) :-
    length(Pairs, N),
    length(AccPairs, N),
    maplist(=[_-_], AccPairs),
    splice_acc_args(AccPairs, Pairs, AccIn, AccOut, StepGoals, RevGoals),
    append([List | AccIn], AccOut, BaseArgs),
    BaseHead =.. [SpliceName | BaseArgs],
    append([List0 | AccInS], AccOutS, StepArgs),
    StepHead_args = [[_|List0] | AccInS],
    append(StepHead_args, AccOutS, StepArgs2),
    StepHead =.. [SpliceName | StepArgs2],
    RecArgs  = [List0 | AccInS],
    append(RecArgs, AccOutS, RecArgsFull),
    RecCall  =.. [SpliceName | RecArgsFull],
    SpliceCall =.. [SpliceName, List | _SCallArgs],
    BaseClause = ir_clause(base(SpliceName), BaseHead, [], []),
    StepClause = ir_clause(step(SpliceName), StepHead, StepGoals, []),
    Reverses = RevGoals.

splice_acc_args([], [], [], [], [], []).
splice_acc_args([_|AccPairs], [T-G-Out|Pairs],
                [Acc0|AccIn], [Acc1|AccOut],
                [G, Acc1=[T|Acc0] | GoalRest],
                [reverse(AccOut_i, Out) | RevRest]) :-
    ignore(Acc0 = []), ignore(Acc1 = []),
    ignore(AccOut_i = Acc1),
    splice_acc_args(AccPairs, Pairs, AccIn, AccOut, GoalRest, RevRest).

remove_findalls_from_body(Body, Findalls, Rest) :-
    findall(Idx, member(_-Idx, Findalls), Idxs),
    findall(Goal, (nth0(I, Body, Goal), \+ member(I, Idxs)), Rest).

% -----------------------------------------------------------------------
% Naming helpers
% -----------------------------------------------------------------------

helper_name(Head, Id, Enumerator, HelperName) :-
    functor(Head, PredName, _),
    atomic_list_concat([nd_loop, Enumerator, PredName, Id], '_', HelperName).

outer_helper_name(Head, Id, Name) :-
    functor(Head, PredName, _),
    atomic_list_concat([nd_outer, PredName, Id], '_', Name).

inner_helper_name(Head, Id, Name) :-
    functor(Head, PredName, _),
    atomic_list_concat([nd_inner, PredName, Id], '_', Name).

splice_helper_name(Head, Id, Name) :-
    functor(Head, PredName, _),
    atomic_list_concat([nd_splice, PredName, Id], '_', Name).

map_helper_name(HelperName, _Head, _Id, _Enum, List, Template, X, MapGoal, Out,
                CallGoal, BaseClause, StepClause) :-
    copy_term(X-Template-MapGoal, HX-HT-HGoal),
    Rev = _Rev,
    CallGoal  =.. [HelperName, List, [], Rev],
    ignore(Out = Rev),
    BaseHead  =.. [HelperName, [], Acc, Acc],
    StepHead  =.. [HelperName, [HX|Xs], Acc0, Res],
    StepRec   =.. [HelperName, Xs, [HT|Acc0], Res],
    BaseClause = ir_clause(base(HelperName), BaseHead, [], []),
    StepClause = ir_clause(step(HelperName), StepHead, [HGoal, StepRec], []).

% -----------------------------------------------------------------------
% Utility: replace and delete goals in body
% -----------------------------------------------------------------------

replace_findall_in_body(Body, OldGoal, NewGoals, NewBody) :-
    append(Prefix, [OldGoal | Suffix], Body),
    !,
    append(Prefix, NewGoals, Temp),
    append(Temp, Suffix, NewBody).

delete_goals(Body, [], Body).
delete_goals(Body, [G|Gs], Result) :-
    (   select(G, Body, Body1) -> true ; Body1 = Body ),
    delete_goals(Body1, Gs, Result).
