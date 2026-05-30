:- module(nd_to_loop, [
    nd_to_loop_program/3,
    nd_to_loop_predicate/4,
    convert_findall_to_loop/3,
    convert_map_to_loop/3,
    convert_fold_to_loop/3,
    convert_flatmap_to_nested_loop/3,
    convert_splice_templates/3
]).

:- use_module(nd_classify, [can_convert_1_to_1/3]).
:- use_module(loop_splice, [loop_splice_program/3]).
:- use_module(safety, [has_side_effects/1, has_cut/1]).

nd_to_loop_program(ProgramIR, OptimisedIR, Report) :-
    convert_program_clauses(ProgramIR, ConvertedClauses, HelperClauses, ReportItems),
    append(ConvertedClauses, HelperClauses, OptimisedIR),
    sort(ReportItems, Report).

nd_to_loop_predicate(Predicate, ProgramIR, OptimisedIR, Report) :-
    can_convert_1_to_1(Predicate, ProgramIR, Decision),
    (   Decision = yes(_, _)
    ->  nd_to_loop_program(ProgramIR, OptimisedIR, Report)
    ;   Decision = no(unsafe_nd(Reasons))
    ->  OptimisedIR = ProgramIR,
        Report = [unsafe_nd_conversion(Predicate, Reasons)]
    ;   Decision = no(Reason)
    ->  OptimisedIR = ProgramIR,
        Report = [skipped_nd_conversion(Predicate, Reason)]
    ;   Decision = unknown(Reason, RequiredDeclarations)
    ->  OptimisedIR = ProgramIR,
        Report = [nd_conversion_unknown(Predicate, Reason, RequiredDeclarations)]
    ).

convert_program_clauses([], [], [], []).
convert_program_clauses([Clause | Rest], [ConvertedClause | ConvertedRest], Helpers, Report) :-
    convert_clause(Clause, ConvertedClause, ClauseHelpers, ClauseReport),
    convert_program_clauses(Rest, ConvertedRest, RestHelpers, RestReport),
    append(ClauseHelpers, RestHelpers, Helpers),
    append(ClauseReport, RestReport, Report).

convert_clause(Clause, ConvertedClause, Helpers, Report) :-
    convert_splice_clause(Clause, ConvertedClause, Helpers, Report),
    !.
convert_clause(Clause, ConvertedClause, Helpers, Report) :-
    convert_fold_clause(Clause, ConvertedClause, Helpers, Report),
    !.
convert_clause(Clause, ConvertedClause, Helpers, Report) :-
    convert_flatmap_clause(Clause, ConvertedClause, Helpers, Report),
    !.
convert_clause(Clause, ConvertedClause, Helpers, Report) :-
    convert_map_clause(Clause, ConvertedClause, Helpers, Report),
    !.
convert_clause(Clause, Clause, [], []).

convert_findall_to_loop(Clause, LoopClause, Report) :-
    convert_map_to_loop(Clause, LoopClause, Report).

convert_map_to_loop(Clause, LoopClause, Report) :-
    (   convert_map_clause(Clause, LoopClause, Helpers, [Item])
    ->  Report = [Item | Helpers]
    ;   LoopClause = Clause,
        Report = []
    ).

convert_fold_to_loop(Clause, LoopClause, Report) :-
    (   convert_fold_clause(Clause, LoopClause, Helpers, [Item])
    ->  Report = [Item | Helpers]
    ;   LoopClause = Clause,
        Report = []
    ).

convert_flatmap_to_nested_loop(Clause, LoopClause, Report) :-
    (   convert_flatmap_clause(Clause, LoopClause, Helpers, [Item])
    ->  Report = [Item | Helpers]
    ;   LoopClause = Clause,
        Report = []
    ).

convert_splice_templates(Clause, SplicedClause, Report) :-
    (   convert_splice_clause(Clause, SplicedClause, Helpers, Items)
    ->  append(Items, Helpers, Report)
    ;   SplicedClause = Clause,
        Report = []
    ).

convert_splice_clause(Clause, ConvertedClause, Helpers, Report) :-
    loop_splice_program([Clause], ConvertedProgram, Report),
    ConvertedProgram = [ConvertedClause | Helpers],
    ConvertedProgram \== [Clause],
    Report \== [].

convert_map_clause(ir_clause(Id, Head, Body, Meta), ir_clause(Id, Head, NewBody, Meta), [BaseClause, StepClause], [nd_map_converted(Predicate)]) :-
    select(findall(Template, Generator, Output), Body, RemainingGoals),
    map_generator(Generator, X, List, Goal),
    \+ generator_unsafe(Goal),
    helper_name(Head, Id, map, HelperName),
    copy_term(X-Template-Goal, HX-HT-HGoal),
    BaseHead =.. [HelperName, [], Acc, Acc],
    StepHead =.. [HelperName, [HX | Xs], Acc0, Result],
    RecCall =.. [HelperName, Xs, [HT | Acc0], Result],
    BaseClause = ir_clause(base(HelperName), BaseHead, [], []),
    StepClause = ir_clause(step(HelperName), StepHead, [HGoal, RecCall], []),
    LoopCall =.. [HelperName, List, [], ReverseOutput],
    NewBody = [LoopCall, reverse(ReverseOutput, Output) | RemainingGoals],
    predicate_indicator(Head, Predicate).

convert_fold_clause(ir_clause(Id, Head, Body, Meta), ir_clause(Id, Head, NewBody, Meta), [BaseClause, StepClause], [nd_fold_converted(Predicate)]) :-
    select(findall(Value, Generator, Values), Body, BodyWithoutFindall),
    select(sum_list(Values, Total), BodyWithoutFindall, RemainingGoals),
    fold_generator(Generator, X, List, Goal),
    \+ generator_unsafe(Goal),
    helper_name(Head, Id, fold, HelperName),
    copy_term(X-Value-Goal, HX-HValue-HGoal),
    BaseHead =.. [HelperName, [], Acc, Acc],
    StepHead =.. [HelperName, [HX | Xs], Acc0, Result],
    AccStep = (Acc1 is Acc0 + HValue),
    RecCall =.. [HelperName, Xs, Acc1, Result],
    BaseClause = ir_clause(base(HelperName), BaseHead, [], []),
    StepClause = ir_clause(step(HelperName), StepHead, [HGoal, AccStep, RecCall], []),
    LoopCall =.. [HelperName, List, 0, Total],
    NewBody = [LoopCall | RemainingGoals],
    predicate_indicator(Head, Predicate).

convert_flatmap_clause(ir_clause(Id, Head, Body, Meta), ir_clause(Id, Head, NewBody, Meta),
                       [OuterBase, OuterStep, InnerBase, InnerStep], [nd_flatmap_converted(Predicate)]) :-
    select(findall(Template, Generator, Output), Body, RemainingGoals),
    flatmap_generator(Generator, X, OuterList, OuterGoal, Y, InnerList, InnerGoal),
    \+ generator_unsafe(OuterGoal),
    \+ generator_unsafe(InnerGoal),
    outer_helper_name(Head, Id, OuterName),
    inner_helper_name(Head, Id, InnerName),
    copy_term(X-InnerList-OuterGoal, HX-HInnerList-HOuterGoal),
    copy_term(X-Y-Template-InnerGoal, IX-IY-ITemplate-HInnerGoal),
    OuterBaseHead =.. [OuterName, [], Acc, Acc],
    OuterStepHead =.. [OuterName, [HX | Xs], Acc0, Result],
    InnerCall =.. [InnerName, HX, HInnerList, Acc0, Acc1],
    OuterRecCall =.. [OuterName, Xs, Acc1, Result],
    OuterBase = ir_clause(base(OuterName), OuterBaseHead, [], []),
    OuterStep = ir_clause(step(OuterName), OuterStepHead, [HOuterGoal, InnerCall, OuterRecCall], []),
    InnerBaseHead =.. [InnerName, _OuterX, [], AccInner, AccInner],
    InnerStepHead =.. [InnerName, IX, [IY | Ys], AccInner0, ResultInner],
    RecInnerCall =.. [InnerName, IX, Ys, [ITemplate | AccInner0], ResultInner],
    InnerBase = ir_clause(base(InnerName), InnerBaseHead, [], []),
    InnerStep = ir_clause(step(InnerName), InnerStepHead, [HInnerGoal, RecInnerCall], []),
    OuterCall =.. [OuterName, OuterList, [], ReverseOutput],
    NewBody = [OuterCall, reverse(ReverseOutput, Output) | RemainingGoals],
    predicate_indicator(Head, Predicate).

predicate_indicator(Head, Name/Arity) :-
    functor(Head, Name, Arity).

map_generator((member(X, List), Goal), X, List, Goal).

fold_generator((member(X, List), Goal), X, List, Goal).

flatmap_generator((member(X, OuterList), OuterGoal, member(Y, InnerList), InnerGoal),
                  X, OuterList, OuterGoal, Y, InnerList, InnerGoal).

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
    member(Name/Arity, [call/1, call/2, call/3, call/4, once/1, forall/2]).

helper_name(Head, Id, Kind, HelperName) :-
    functor(Head, PredicateName, _),
    atomic_list_concat([nd_loop, Kind, PredicateName, Id], '_', HelperName).

outer_helper_name(Head, Id, HelperName) :-
    functor(Head, PredicateName, _),
    atomic_list_concat([nd_outer, PredicateName, Id], '_', HelperName).

inner_helper_name(Head, Id, HelperName) :-
    functor(Head, PredicateName, _),
    atomic_list_concat([nd_inner, PredicateName, Id], '_', HelperName).
