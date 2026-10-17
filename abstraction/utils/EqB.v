(* Computational (Boolean) equality on a type. *)
Class EqB (A: Type) := eqb: A -> A -> bool.

Declare Scope eqb_scope.
Infix "=?" := eqb (at level 70): eqb_scope.
Open Scope eqb_scope.
