From Equations Require Import Equations.
From Stdlib Require Import Arith Bool Lia Structures.Orders.
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

Lemma eqb_refl: forall (l: Lit), (l =? l) = true.
Proof. destruct l; simp eqb; apply eqb_refl. Qed.

Lemma eqb_sym: forall (l1 l2: Lit), (l1 =? l2) = (l2 =? l1).
Proof. destruct l1, l2; simp eqb; try reflexivity; now apply eqb_sym. Qed.

Lemma eqb_eq: forall (l1 l2: Lit), (l1 =? l2) = true <-> l1 = l2.
Proof. destruct l1, l2; split; try simp eqb; try rewrite eqb_eq; congruence. Qed.

Lemma eqb_neq: forall (l1 l2: Lit), (l1 =? l2) = false <-> l1 <> l2.
Proof. 
  intros. rewrite <- not_iff_compat.
  - now rewrite not_true_iff_false.
  - apply eqb_eq.
Qed.

Definition eq_dec: forall (l1 l2: Lit), {l1 = l2} + {l1 <> l2}.
Proof.
  destruct l1 as [p1|p1], l2 as [p2|p2].
  - destruct (eq_dec p1 p2).
    + left. congruence.
    + right. congruence.
  - right. now unfold not.
  - right. now unfold not.
  - destruct (eq_dec p1 p2).
    + left. congruence.
    + right. congruence.
Qed.

Module Lit_as_OT <: OrderedType.
(* Parameter t : Type.
Parameter eq : t -> t -> Prop.
Parameter eq_equiv : RelationClasses.Equivalence eq.
Parameter lt : t -> t -> Prop.
Parameter lt_strorder : RelationClasses.StrictOrder lt.
Parameter lt_compat :
Morphisms.Proper
(Morphisms.respectful eq (Morphisms.respectful eq iff)) lt.
Parameter compare : t -> t -> comparison.
Parameter compare_spec :
forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
Parameter eq_dec : forall x y : t, {eq x y} + {~ eq x y}. *)

  Definition t := Lit.

  Definition eq := @eq Lit.

  Lemma eq_equiv: Equivalence eq.
  Proof. constructor; congruence. Qed.

  Definition lt (l1 l2: Lit): Prop :=
  match l1, l2 with
  | Pos p1, Pos p2 => p1 < p2
  | Neg p1, Neg p2 => p1 < p2
  | Pos _, Neg _ => True
  | Neg _, Pos _ => False
  end.

  Declare Scope lit_order_scope.
  Infix "<" := lt (at level 70): lit_order_scope.
  Open Scope lit_order_scope.

  Lemma lt_strorder: StrictOrder lt.
  Proof.
    constructor. 
    - intros l Hlt. destruct l as [p|p]; now apply (Nat.lt_irrefl p).
    - intros l1 l2 l3. destruct l1, l2, l3; simpl in *; lia.
  Qed.

  Lemma lt_compat: Proper (eq ==> eq ==> iff) lt.
  Proof. now intros ? ? -> ? ? ->. Qed.

  Definition compare (l1 l2: Lit): comparison :=
  match l1, l2 with
  | Pos p1, Pos p2 => Nat.compare p1 p2
  | Neg p1, Neg p2 => Nat.compare p1 p2
  | Pos _, Neg _ => Lt
  | Neg _, Pos _ => Gt
  end.

  Lemma compare_spec: forall (l1 l2: Lit), CompareSpec (l1 = l2) (l1 < l2) (l2 < l1) (compare l1 l2).
  Proof.
    destruct l1 as [p1|p1], l2 as [p2|p2]. 
    - destruct (Nat.compare p1 p2) eqn:Hcomp.
      + simpl. rewrite Hcomp. apply CompEq. apply Nat.compare_eq_iff in Hcomp. congruence.
      + simpl. rewrite Hcomp. apply CompLt. now apply Nat.compare_lt_iff.
      + simpl. rewrite Hcomp. apply CompGt. now apply Nat.compare_gt_iff.
    - now apply CompLt.
    - now apply CompGt.
    - destruct (Nat.compare p1 p2) eqn:Hcomp.
      + simpl. rewrite Hcomp. apply CompEq. apply Nat.compare_eq_iff in Hcomp. congruence.
      + simpl. rewrite Hcomp. apply CompLt. now apply Nat.compare_lt_iff.
      + simpl. rewrite Hcomp. apply CompGt. now apply Nat.compare_gt_iff.
   Qed.

  Definition eq_dec := eq_dec.
End Lit_as_OT.
