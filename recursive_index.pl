:- module(recursive_index, [optimise_recursive_index_loops/3, needed_subterms/3]).

:- use_module(subterm_address, [subterm_with_address/3]).

% Report items keep the extracted value as a variable so callers can see
% which output position is recovered from the discovered address.
optimise_recursive_index_loops(ProgramIR, ProgramIR, Report) :-
    findall(
        recursive_index_mapping(Pred, addr(Address, Value)),
        recursive_index_candidate(ProgramIR, Pred, Address, Value),
        ReportRaw
    ),
    sort(ReportRaw, Report).

needed_subterms(Term, Addresses, Values) :-
    needed_subterms_(Addresses, Term, Values).

needed_subterms_([], _, []).
needed_subterms_([Address | RestAddresses], Term, [Value | RestValues]) :-
    subterm_with_address(Term, Address, Value),
    needed_subterms_(RestAddresses, Term, RestValues).

% Combines one recursive descent step with one base-case extraction to
% produce a concrete address candidate for recursive traversal patterns.
recursive_index_candidate(ProgramIR, Pred, Address, Value) :-
    member(RecursiveClause, ProgramIR),
    recursive_index_step(RecursiveClause, Pred, StepAddress, Value),
    member(BaseClause, ProgramIR),
    BaseClause \== RecursiveClause,
    recursive_index_base(BaseClause, Pred, BaseAddress, Value),
    append(StepAddress, BaseAddress, Address).

% Matches recursive clauses that descend through the first argument while
% passing the remaining arguments through unchanged.
recursive_index_step(ir_clause(_, Head, [RecursiveGoal], _), Name/Arity, StepAddress, Value) :-
    functor(Head, Name, Arity),
    Arity >= 2,
    Head =.. [Name, Root | HeadTail],
    RecursiveGoal =.. [Name, Child | GoalTail],
    preserved_recursive_tail(HeadTail, GoalTail),
    member(Value, HeadTail),
    var(Value),
    Root \== Child,
    unique_variable_address(Root, Child, StepAddress),
    StepAddress \= [].

% Matches base clauses that recover an output variable from a unique
% address inside the first argument without further recursion.
recursive_index_base(ir_clause(_, Head, [], _), Name/Arity, BaseAddress, Value) :-
    functor(Head, Name, Arity),
    Arity >= 2,
    Head =.. [Name, Root | HeadTail],
    member(Value, HeadTail),
    % Only variable outputs can be propagated safely through the report.
    var(Value),
    Root \== Value,
    unique_variable_address(Root, Value, BaseAddress),
    BaseAddress \= [].

preserved_recursive_tail([], []).
preserved_recursive_tail([HeadArg | HeadRest], [GoalArg | GoalRest]) :-
    HeadArg == GoalArg,
    preserved_recursive_tail(HeadRest, GoalRest).

% Finds the single address at which Var occurs in Term; fails when the
% variable does not appear exactly once.
unique_variable_address(Term, Var, Address) :-
    findall(Path, variable_address(Term, Var, [], Path), Paths),
    single_address(Paths, Address).

% Recursive index candidates only keep variables that resolve to one
% concrete address; zero or multiple matches are rejected.
single_address([Address], Address).

variable_address(Term, Var, Path, Path) :-
    var(Term),
    Term == Var.
variable_address(Term, Var, Path0, Path) :-
    compound(Term),
    arg(Index, Term, Child),
    append(Path0, [Index], Path1),
    variable_address(Child, Var, Path1, Path).
