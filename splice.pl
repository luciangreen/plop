:- module(splice, [splice_program/3]).

% splice_program(+ProgramIR, -OptimisedIR, -Report)
%
% Stage 10 — Shortcut and Splicing Optimisation.
%
% Detects arithmetic variables assigned by a single `Var is Expr` goal that
% are used exactly once in the remaining body goals and do not appear in the
% clause head.  Such variables are spliced inline: the assignment goal is
% removed and Expr is substituted for Var at its single use site.
%
% Example:
%   A is X+1, Y is A*2  -->  Y is (X+1)*2
%
% Unsafe cases that are never rewritten:
%   - the variable appears more than once (multi-use),
%   - the variable appears in the clause head (would change the interface),
%   - the variable appears before the assignment in the body.

splice_program(ProgramIR, OptimisedIR, Report) :-
    splice_clauses(ProgramIR, OptimisedIR, [], ReportRaw),
    sort(ReportRaw, Report).

splice_clauses([], [], Report, Report).
splice_clauses([Clause | Rest], [SplicedClause | SplicedRest], Report0, Report) :-
    splice_clause(Clause, SplicedClause, Item),
    (   nonvar(Item)
    ->  Report1 = [Item | Report0]
    ;   Report1 = Report0
    ),
    splice_clauses(Rest, SplicedRest, Report1, Report).

splice_clause(ir_clause(Id, Head, Body, Meta), ir_clause(Id, Head, SplicedBody, Meta), ReportItem) :-
    splice_body_fully(Head, Body, SplicedBody),
    (   SplicedBody \== Body
    ->  predicate_from_head(Head, Pred),
        ReportItem = spliced(Pred)
    ;   true
    ).

% Repeatedly apply splice_once until no further splicing is possible.
splice_body_fully(Head, Body, Final) :-
    (   splice_once(Head, Body, Body1)
    ->  splice_body_fully(Head, Body1, Final)
    ;   Final = Body
    ).

% splice_once(+Head, +Body, -SplicedBody)
%
% Find the first eligible `Var is Expr` goal and inline it.  Eligible means:
%   - Var is an uninstantiated variable,
%   - Var does not appear anywhere before the assignment in the body,
%   - Var does not appear in the clause head,
%   - Var appears exactly once in the body goals that follow the assignment.
splice_once(Head, Body, SplicedBody) :-
    append(Prefix, [VarIs | Suffix], Body),
    VarIs = (Var is Expr),
    var(Var),
    occurrences_in_goals(Var, Prefix, 0),
    \+ term_contains_var(Var, Head),
    occurrences_in_goals(Var, Suffix, 1),
    !,
    substitute_in_goals(Var, Expr, Suffix, SplicedSuffix),
    append(Prefix, SplicedSuffix, SplicedBody).

predicate_from_head(Head, Name/Arity) :-
    functor(Head, Name, Arity).

% substitute_in_goals(+Var, +Expr, +Goals, -SubstGoals)
%
% Replace the unique occurrence of Var in Goals with Expr.
% Processing stops after the first goal in which the substitution was made.
substitute_in_goals(_, _, [], []).
substitute_in_goals(Var, Expr, [Goal | Rest], [SubstGoal | SubstRest]) :-
    substitute_term(Var, Expr, Goal, SubstGoal),
    (   SubstGoal == Goal
    ->  substitute_in_goals(Var, Expr, Rest, SubstRest)
    ;   SubstRest = Rest
    ).

% substitute_term(+Var, +Expr, +Term, -SubstTerm)
%
% Replace one occurrence of Var in Term with Expr.
substitute_term(Var, Expr, Term, SubstTerm) :-
    (   var(Term)
    ->  (Term == Var -> SubstTerm = Expr ; SubstTerm = Term)
    ;   atomic(Term)
    ->  SubstTerm = Term
    ;   Term =.. [F | Args],
        substitute_terms(Var, Expr, Args, SubstArgs),
        SubstTerm =.. [F | SubstArgs]
    ).

substitute_terms(_, _, [], []).
substitute_terms(Var, Expr, [Term | Rest], [SubstTerm | SubstRest]) :-
    substitute_term(Var, Expr, Term, SubstTerm),
    substitute_terms(Var, Expr, Rest, SubstRest).

% term_contains_var(+Var, +Term)
%
% True if Term syntactically contains the variable Var (identity check).
term_contains_var(Var, Term) :-
    (   var(Term)
    ->  Var == Term
    ;   compound(Term),
        Term =.. [_ | Args],
        member(Arg, Args),
        term_contains_var(Var, Arg)
    ).

% occurrences_in_goals(+Var, +Goals, -Count)
occurrences_in_goals(_, [], 0).
occurrences_in_goals(Var, [Goal | Rest], Count) :-
    occurrences_in_term(Var, Goal, N1),
    occurrences_in_goals(Var, Rest, N2),
    Count is N1 + N2.

occurrences_in_term(Var, Term, Count) :-
    (   var(Term)
    ->  (Term == Var -> Count = 1 ; Count = 0)
    ;   atomic(Term)
    ->  Count = 0
    ;   Term =.. [_ | Args],
        occurrences_in_terms(Var, Args, Count)
    ).

occurrences_in_terms(_, [], 0).
occurrences_in_terms(Var, [Term | Rest], Count) :-
    occurrences_in_term(Var, Term, N1),
    occurrences_in_terms(Var, Rest, N2),
    Count is N1 + N2.
