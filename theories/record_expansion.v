From elpi Require Import elpi.
From record_expansion Extra Dependency
  "record_expansion.elpi" as record_expansion.

(**
   This file sketches a procedure to translate a term abstracted over
   a specific record to a term abstracted over the components of that record.

   Example:

     Record r := mk { proj1 : T1; proj2 : T2 }.
     Definition f (x : r) := Body(proj1 x,proj2 x).

   Is expanded to:

     Definition f1 v1 v2 := Body(v1,v2).

   And recursively, if g uses f, then g1 must use f1...

   The idea is to take "f", replace "(x : r)" with as many abstractions as
   needed in order to write "mk v1 v2", then replace "x" with "mk v1 v2", finally
   fire iota reductions such as "proj1 (mk v1 v2) = v1" to obtain "f1".
   
   Then record a global replacement "f x = f1 v2 v2" whenever "x = mk v1 v2".

*)

Elpi Db record.expand.db lp:{{
  % This data base will contain all the expansions performed previously.
  % For example, if f was expandded to f1 we would have this clause:

  % copy (app[f, R | L]) (app[f1, V1, V2 | L1]) :-
  %   copy R (app[k, V1, V2]), std.map L copy L1.

}}.

Elpi Command record.expand.
Elpi Accumulate Db record.expand.db.
Elpi Accumulate File record_expansion.
Elpi Typecheck.

Record r := { T :> Type; X := T; op : T -> X -> bool }.

Definition f b (t : r) (q := negb b) := fix rec (l1 l2 : list t) :=
  match l1, l2 with
  | nil, nil => b
  | cons x xs, cons y ys => andb (op _ x y) (rec xs ys)
  | _, _ => q
  end.

Elpi record.expand r f "expanded_".
Print f.
Print expanded_f.

(* so that we can see the new "copy" clause *)
Elpi Print record.expand.

Definition g t l s h := (forall x y, op t x y = false) /\ f true t l s = h.

Elpi record.expand r g "expanded_".
Print expanded_g.
