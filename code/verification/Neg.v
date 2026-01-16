From Equations Require Import Equations.
From RocqSAT Require Import Lit.

(* Negates a literal (i.e. Pos becomes Neg and Neg becomes Pos). *)
Equations neg (l: Lit): Lit :=
neg (Pos p) := Neg p;
neg (Neg p) := Pos p.

Declare Scope neg_scope.
Notation "¬ l" := (neg l) (at level 65, right associativity, format "'[' ¬ ']' l"): neg_scope.
Open Scope neg_scope.

Lemma self_neq_neg: forall (l: Lit), l <> ¬l.
Proof. intros. apply eqb_neq. now funelim (l =? ¬l). Qed.

Lemma self_neqb_neg: forall (l: Lit), l =? ¬l = false.
Proof. intros. now funelim (l =? ¬l). Qed.

Lemma involutive: forall (l: Lit), ¬¬l = l.
Proof. intros. now funelim (¬l). Qed.

Lemma eqb_compat: forall (l1 l2: Lit), (l1 =? l2) = (¬l1 =? ¬l2).
Proof. now destruct l1, l2. Qed.

Lemma eq_compat: forall (l1 l2: Lit), l1 = l2 <-> ¬l1 = ¬l2.
Proof. intros. repeat rewrite <- eqb_eq. now rewrite eqb_compat. Qed.
