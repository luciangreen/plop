:- module(recursive_index, [optimise_recursive_index_loops/3, needed_subterms/3]).

:- use_module(subterm_address, [subterm_with_address/3]).

optimise_recursive_index_loops(ProgramIR, ProgramIR, Report) :-
    findall(
        recursive_index_mapping(Pred, addr(Address, Value)),
        recursive_index_candidate(ProgramIR, Pred, Address, Value),
        ReportRaw
    ),
    sort(ReportRaw, Report).

needed_subterms(Term, Addresses, Values) :-
    same_length(Addresses, Values),
    needed_subterms_(Addresses, Term, Values).

needed_subterms_([], _, []).
needed_subterms_([Address | RestAddresses], Term, [Value | RestValues]) :-
    subterm_with_address(Term, Address, Value),
    needed_subterms_(RestAddresses, Term, RestValues).

recursive_index_candidate(ProgramIR, Pred, Address, Value) :-
    member(RecursiveClause, ProgramIR),
    recursive_index_step(RecursiveClause, Pred, StepAddress, Value),
    member(BaseClause, ProgramIR),
    BaseClause \== RecursiveClause,
    recursive_index_base(BaseClause, Pred, BaseAddress, Value),
    append(StepAddress, BaseAddress, Address).

recursive_index_step(ir_clause(_, Head, [RecursiveGoal], _), Name/2, StepAddress, Value) :-
    Head =.. [Name, Root, Value],
    var(Value),
    RecursiveGoal =.. [Name, Child, Value],
    unique_variable_address(Root, Child, StepAddress),
    StepAddress \= [].

recursive_index_base(ir_clause(_, Head, [], _), Name/2, BaseAddress, Value) :-
    Head =.. [Name, Root, Value],
    var(Value),
    unique_variable_address(Root, Value, BaseAddress),
    BaseAddress \= [].

unique_variable_address(Term, Var, Address) :-
    findall(Path, variable_address(Term, Var, [], Path), Paths),
    Paths = [Address].

variable_address(Term, Var, Path, Path) :-
    var(Term),
    Term == Var.
variable_address(Term, Var, Path0, Path) :-
    compound(Term),
    arg(Index, Term, Child),
    append(Path0, [Index], Path1),
    variable_address(Child, Var, Path1, Path).
