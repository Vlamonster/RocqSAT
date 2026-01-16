From Equations Require Import Equations.
From Stdlib Require Import Arith Bool.
From RocqSAT Require Import Atom.

(* Literals are either positive or negated variants of atoms. *)
Inductive Lit: Type :=
| Pos (p: Atom)
| Neg (p: Atom).

Equations eqb (l1 l2: Lit): bool :=
eqb (Pos p1) (Pos p2) := p1 =? p2;
eqb (Neg p1) (Neg p2) := p1 =? p2;
eqb _        _        := false.

Equations extract (l: Lit): Atom :=
extract (Pos p) := p;
extract (Neg p) := p.

Declare Scope lit_scope.
Infix "=?" := eqb (at level 70): lit_scope.
Open Scope lit_scope.

Lemma eqb_refl: forall (l: Lit), l =? l = true.
Proof. destruct l; simp eqb; apply eqb_refl. Qed.

Lemma eqb_sym: forall (l1 l2: Lit), (l1 =? l2) = (l2 =? l1).
Proof. destruct l1, l2; simp eqb; try reflexivity; now apply eqb_sym. Qed.

Lemma eqb_eq: forall (l1 l2: Lit), l1 =? l2 = true <-> l1 = l2.
Proof. destruct l1, l2; split; try simp eqb; try rewrite eqb_eq; congruence. Qed.

Lemma eqb_neq: forall (l1 l2: Lit), l1 =? l2 = false <-> l1 <> l2.
Proof. 
  intros. rewrite <- not_iff_compat.
  - now rewrite not_true_iff_false.
  - apply eqb_eq.
Qed.
