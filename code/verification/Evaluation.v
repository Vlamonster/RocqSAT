From Equations Require Import Equations.
From Stdlib Require Import List.
Import ListNotations.
From RocqSAT Require Import Lit Neg Clause CNF.

(* An annotation on a literal (Lit * Ann) describing how its value was assigned. *)
Inductive Ann: Type :=
| dec
| prop.

(* A partial assignment for annoted literals. See below for evaluation. *)
Definition PA: Type := list (Lit * Ann).

Declare Scope pa_scope.
Notation "m ++a n" := (n ++ m) (at level 55, left associativity): pa_scope.
Notation "m ++d l" := ((l, dec) :: m) (at level 55, left associativity): pa_scope.
Notation "m ++p l" := ((l, prop) :: m) (at level 55, left associativity): pa_scope.
Open Scope pa_scope.

(* The first instance of `l` or `¬l` determines the value. *)
Equations l_eval (m: PA) (l: Lit): option bool :=
l_eval [] _ := None;
l_eval ((l', _) :: m) l with l =? l', l =? ¬l' :=
  | true, _    := Some true
  | _   , true := Some false
  | _   , _    := l_eval m l.

Equations c_eval (m: PA) (c: Clause): option bool :=
c_eval m [] := Some false;
c_eval m (l :: c) with l_eval m l, c_eval m c :=
  | Some true , _          := Some true
  | _         , Some true  := Some true
  | Some false, Some false := Some false
  | _         , _          := None.

Equations f_eval (m: PA) (f: CNF): option bool :=
f_eval m [] := Some true;
f_eval m (c :: f) with c_eval m c, f_eval m f :=
  | Some true , r          := r
  | Some false, _          := Some false
  | _         , Some false := Some false
  | None      , _          := None.

Definition Def (m: PA) (l: Lit): Prop := exists (b: bool), l_eval m l = Some b.
Definition Undef (m: PA) (l: Lit): Prop := l_eval m l = None.

Lemma def_undef: forall (m: PA) (l: Lit), Def m l <-> ~ Undef m l.
Proof. 
  unfold Def, Undef. intros. destruct (l_eval m l).
  - intuition.
    + discriminate.
    + exists b. reflexivity.
  - intuition. destruct H. discriminate.
Qed.

Module EvalExamples.
  Example example_l_eval_1: l_eval ([] ++p Pos 1) (Pos 1) = Some true.
  Proof. reflexivity. Qed.

  Example example_l_eval_2: l_eval ([] ++p Pos 1) (Neg 1) = Some false.
  Proof. reflexivity. Qed.

  Example example_l_eval_3: l_eval ([] ++p Pos 1) (Pos 2) = None.
  Proof. reflexivity. Qed.

  Example example_c_eval_1: c_eval [] [Pos 1; Pos 2] = None.
  Proof. reflexivity. Qed.

  Example example_c_eval_2: c_eval ([] ++p Pos 1) [Pos 1; Pos 2] = Some true.
  Proof. reflexivity. Qed.

  Example example_c_eval_3: c_eval ([] ++p Neg 1 ++p Neg 2) [Pos 1; Pos 2] = Some false.
  Proof. reflexivity. Qed.
End EvalExamples.

Lemma undef_neg_iff: forall (m: PA) (l: Lit), Undef m l <-> Undef m (¬l).
Proof.
  unfold Undef. intros. funelim (l_eval m l).
  - intuition.
  - intuition.
    + discriminate.
    + apply eqb_eq in Heq. subst. simp l_eval in H. rewrite eqb_refl in H. 
      rewrite eqb_sym in H. rewrite Neg.self_neqb_neg in H. discriminate.
  - intuition.
    + discriminate.
    + apply eqb_eq in Heq. subst. simp neg in H. rewrite Neg.involutive in H.
      simp l_eval in H. rewrite eqb_refl in H. rewrite Neg.self_neqb_neg in H. discriminate.
  - intuition.
    + simp l_eval. rewrite <- Neg.eqb_compat. rewrite Heq0. rewrite Neg.eqb_compat in Heq.
      rewrite Neg.involutive in Heq. now rewrite Heq.
    + autorewrite with l_eval in H. rewrite <- Neg.eqb_compat in H. rewrite Heq0 in H.
      rewrite Neg.eqb_compat in Heq. rewrite Neg.involutive in Heq. rewrite Heq in H. simpl in H. 
      apply H1. apply H.
Qed.

Lemma l_eval_some_iff: forall (m: PA) (l: Lit), 
  (exists (b: bool), l_eval m l = Some b) <-> exists (a: Ann), In (l, a) m \/ In (¬l, a) m.
Proof. 
  intros. split.
  - intros [b H]. funelim (l_eval m l).
    + congruence.
    + rewrite eqb_eq in Heq. subst l'. exists a. left. now left.
    + rewrite eqb_eq in Heq. subst. exists a. right. rewrite involutive. now left.
    + rewrite H0 in Heqcall. apply H in Heqcall as [a' [G|G]].
      * exists a'. left. now right.
      * exists a'. right. now right.
  - intros [a [H|H]].
    + funelim (l_eval m l).
      * inversion H.
      * now exists true.
      * now exists false.
      * apply (H a0). inversion H0.
        -- injection H1 as <- <-. now rewrite eqb_refl in Heq0.
        -- assumption.
    + funelim (l_eval m l).
      * inversion H.
      * now exists true.
      * now exists false.
      * apply (H a0). inversion H0.
        -- injection H1 as -> ->. rewrite involutive in Heq. now rewrite eqb_refl in Heq.
        -- assumption.
Qed.

Lemma c_eval_none__l_eval_none: forall (m: PA) (c: Clause), 
  c_eval m c = None -> exists (l: Lit), In l c /\ l_eval m l = None.
Proof. 
  induction c. intros.
  - discriminate.
  - intros. destruct (l_eval m a) eqn:G1.
    + destruct b.
      * simp c_eval in H. rewrite G1 in H. simpl in H. discriminate.
      * simp c_eval in H. rewrite G1 in H. simpl in H. destruct (c_eval m c) eqn:G2.
        -- destruct b; discriminate.
        -- apply IHc in H. destruct H. destruct H. exists x. split.
          ++ now right.
          ++ assumption.
    + exists a. split.
      * now left.
      * assumption.
Qed.

Lemma c_eval_false__l_eval_false: forall (m: PA) (c: Clause),
  c_eval m c = Some false -> forall (l: Lit), In l c -> l_eval m l = Some false.
Proof. 
  induction c.
  - intros. contradiction.
  - intros. simp c_eval in H. destruct (l_eval m a) eqn:G1.
    + destruct b.
      * simpl in H. discriminate.
      * simpl in H. destruct (c_eval m c) eqn:G2.
        -- destruct b.
          ++ discriminate.
          ++ inversion H0.
            ** subst. assumption.
            ** apply (IHc H l H1).
        -- discriminate.
    + simpl in H. destruct (c_eval m c) eqn:G2.
      * destruct b; discriminate.
      * discriminate.
Qed.

Lemma undef_remove_false__undef: forall (m: PA) (c: Clause) (l: Lit),
  c_eval m c = None -> c_eval m (l_remove c l) = Some false -> Undef m l.
Proof.
  unfold Undef. intros. 
  pose proof (c_eval_none__l_eval_none m c H).
  pose proof (c_eval_false__l_eval_false m (l_remove c l) H0).
  destruct H1. destruct H1. destruct (x =? l) eqn:G.
  - now apply eqb_eq in G as ->.
  - pose proof (H2 x). assert (In x (l_remove c l)).
    + simp l_remove. rewrite filter_In. split.
      * assumption.
      * rewrite eqb_sym. now rewrite G.
    + apply H4 in H5. congruence. 
Qed.
