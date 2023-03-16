From elpi Require Import elpi.
From record_expansion Extra Dependency "register.elpi" as register.
From record_expansion Extra Dependency "expand.elpi" as expand.

Elpi Db record.expand.db lp:{{

% the predicate to accumulate information about the record types to expand
pred expand-record
  o:inductive,      % record type
  o:int,            % number of type parameters
  o:constructor,    % record constructor
  o:term,           % record constructor type
  o:list constant.  % projections
:name "expand-record:start"
expand-record _ _ _ _ _ :- fail.

pred expand-projection
  o:constant,       % projection
  o:constructor,    % record constructor
  o:int,            % number of type parameters
  o:int.            % index of the term
:name "expand-projection:start"
expand-projection _ _ _ _ :- fail.

pred expand-constant i:constant, o:term.
:name "expand-constant:start"
expand-constant _ _ :- fail.

}}.

Elpi Command record.register.
Elpi Accumulate Db record.expand.db.
Elpi Accumulate File register.
Elpi Typecheck.

Elpi Command record.expand.
Elpi Accumulate Db record.expand.db.
Elpi Accumulate File expand.
Elpi Typecheck.

Module Example1.

Record r := { T : Type; T' := T; op : T' -> T -> T }.

Elpi record.register r.

Elpi Query lp:{{ expand-fun `In` {{ r -> r }} _ A }}.
Elpi Query lp:{{ expand-term _ {{ r -> r }} {{ fun x : r => x }} [] A }}.
Elpi Query lp:{{ expand-term _ {{ r -> Type }} {{ fun x : r => T x }} [] A }}.

Definition r_id (x : r) := x.

Elpi record.expand r_id "expanded_".
Print expanded_r_id.
Print expanded_r_id1.
Elpi Query lp:{{ {{:gref r_id}} = const C, expand-constant C Out }}.

End Example1.

Module Example2.

Record r1 := { T : Type; op : T -> T -> bool }.

Record r2 := { r2_r1 : r1; refl : forall x, op r2_r1 x x = true }.

Elpi record.register r1.
Elpi record.register r2.

Elpi Query lp:{{ expand-fun _ {{ r2 }} _ A }}.

End Example2.
