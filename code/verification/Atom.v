From Stdlib Require Import Arith.

(* Atoms are propositional symbols mapped to the naturals. *)
Definition Atom: Type := nat.

Definition eqb := Nat.eqb.

Declare Scope atom_scope.
Infix "=?" := eqb (at level 70): atom_scope.
Open Scope atom_scope.

Lemma eqb_refl: forall (p: Atom), p =? p = true.
Proof. apply Nat.eqb_refl. Qed.

Lemma eqb_sym: forall (p1 p2: Atom), (p1 =? p2) = (p2 =? p1).
Proof. apply Nat.eqb_sym. Qed.

Lemma eqb_eq: forall (p1 p2: Atom), p1 =? p2 = true <-> p1 = p2.
Proof. apply Nat.eqb_eq. Qed.
