From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import Structures.Orders.

From Equations Require Import Equations.

From RocqSAT Require Import Atom.

Module Lit.
  Module Definitions.
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
  End Definitions.

  Include Definitions.

  Module Lemmas.
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
  End Lemmas.

  Include Lemmas.
End Lit.

Export Lit.Definitions.

Module LitOrderType <: OrderedType.
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

  Definition eq_dec := Lit.eq_dec.
End LitOrderType.

Module Neg.
  Module Definitions.
    (* Negates a literal (i.e. Pos becomes Neg and Neg becomes Pos). *)
    Equations neg (l: Lit): Lit :=
    neg (Pos p) := Neg p;
    neg (Neg p) := Pos p.

    Declare Scope neg_scope.
    Notation "¬ l" := (neg l) (at level 65, right associativity, format "'[' ¬ ']' l"): neg_scope.
    Open Scope neg_scope.
  End Definitions.

  Include Definitions.

  Module Lemmas.
    Lemma self_neq_neg: forall (l: Lit), l <> ¬l.
    Proof. intros. apply Lit.eqb_neq. now funelim (l =? ¬l). Qed.

    Lemma self_neqb_neg: forall (l: Lit), (l =? ¬l) = false.
    Proof. intros. now funelim (l =? ¬l). Qed.

    Lemma involutive: forall (l: Lit), ¬¬l = l.
    Proof. intros. now funelim (¬l). Qed.

    Lemma eqb_compat: forall (l1 l2: Lit), (l1 =? l2) = (¬l1 =? ¬l2).
    Proof. now destruct l1, l2. Qed.

    Lemma eq_compat: forall (l1 l2: Lit), l1 = l2 <-> ¬l1 = ¬l2.
    Proof. intros. repeat rewrite <- Lit.eqb_eq. now rewrite eqb_compat. Qed.
  End Lemmas.

  Include Lemmas.
End Neg.

Export Neg.Definitions.
