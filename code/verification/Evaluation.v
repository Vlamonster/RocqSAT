From Equations Require Import Equations.
From Stdlib Require Import List Bool.
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

Equations m_eval (m m': PA): option bool :=
m_eval m [] := Some true;
m_eval m ((l, _) :: m') with l_eval m l, m_eval m m' :=
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

Definition NoDecisions (m: PA): Prop := ~ exists (l: Lit), In (l, dec) m.
Definition Conflicting (m: PA) (c: Clause): Prop := c_eval m c = Some false.

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

Lemma l_eval_neg_none_iff: forall (m: PA) (l: Lit), l_eval m l = None <-> l_eval m (¬l) = None.
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

Lemma l_eval_neg_some_iff: forall (m: PA) (l: Lit) (b: bool),
  l_eval m l = Some b <-> l_eval m (¬l) = Some (negb b).
Proof.
  intros. split.
  - intros. funelim (l_eval m l).
    + congruence.
    + rewrite eqb_eq in Heq. subst l'. rewrite H in Heqcall. injection Heqcall as <-.
      simp l_eval. rewrite eqb_refl. rewrite eqb_compat. rewrite involutive. now rewrite self_neqb_neg.
    + rewrite eqb_eq in Heq. subst l. rewrite H in Heqcall. injection Heqcall as <-.
      rewrite involutive. simp l_eval. rewrite eqb_refl. now rewrite self_neqb_neg.
    + simp l_eval. rewrite <- eqb_compat. rewrite Heq0. rewrite eqb_compat. rewrite involutive.
      rewrite Heq. simpl. apply H. congruence.
  - intros. funelim (l_eval m l).
    + discriminate.
    + rewrite eqb_eq in Heq. subst l'. simp l_eval in H. rewrite eqb_refl in H. rewrite eqb_compat in H.
      rewrite involutive in H. rewrite self_neqb_neg in H. simpl in H. injection H. intros.
      symmetry in H0. apply negb_false_iff in H0. congruence.
    + rewrite eqb_eq in Heq. subst l. rewrite involutive in H. simp l_eval in H. rewrite eqb_refl in H.
      rewrite self_neqb_neg in H. simpl in H. injection H. intros. symmetry in H0.
      apply negb_true_iff in H0. congruence.
    + apply H. simp l_eval in H0. rewrite <- eqb_compat in H0. rewrite Heq0 in H0.
      rewrite eqb_compat in H0. rewrite involutive in H0. now rewrite Heq in H0.
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
      * contradiction.
      * now exists true.
      * now exists false.
      * apply (H a0). destruct H0.
        -- injection H0 as <- <-. now rewrite eqb_refl in Heq0.
        -- assumption.
    + funelim (l_eval m l).
      * contradiction.
      * now exists true.
      * now exists false.
      * apply (H a0). destruct H0.
        -- injection H0 as -> ->. rewrite involutive in Heq. now rewrite eqb_refl in Heq.
        -- assumption.
Qed.

Lemma l_eval_false_in: forall (m: PA) (l: Lit),
  l_eval m l = Some false -> exists (a: Ann), In (¬l, a) m.
Proof.
  intros. funelim (l_eval m l); try congruence.
  - rewrite eqb_eq in Heq. subst l. exists a. rewrite involutive. now left.
  - rewrite H0 in Heqcall. apply H in Heqcall.
    + destruct Heqcall as [a' Hin]. exists a'. now right.
    + reflexivity.
    + reflexivity.
Qed.

Lemma c_eval_true_iff: forall (m: PA) (c: Clause),
  c_eval m c = Some true <-> exists (l: Lit), In l c /\ l_eval m l = Some true.
Proof.
  intros. split.
  - intros. funelim (c_eval m c); try congruence.
    + exists l. split.
      * now left.
      * assumption.
    + apply Hind in Heq as [l' [Hin' Hl']].
      * exists l'. split.
        -- now right.
        -- assumption.
      * reflexivity.
      * reflexivity.
    + apply Hind in Heq as [l' [Hin' Hl']].
      * exists l'. split.
        -- now right.
        -- assumption.
      * reflexivity.
      * reflexivity.
  - intros. funelim (c_eval m c); try congruence.
    + now destruct H.
    + destruct H as [l' [[Heq'|Hin'] Hl']].
      * congruence.
      * assert (c_eval m c = Some true).
        -- apply Hind. now exists l'.
        -- congruence.
    + destruct H as [l' [[Heq'|Hin'] Hl']].
      * congruence.
      * assert (c_eval m c = Some true).
        -- apply Hind. now exists l'.
        -- congruence.
    + destruct H as [l' [[Heq'|Hin'] Hl']].
      * congruence.
      * assert (c_eval m c = Some true).
        -- apply Hind. now exists l'.
        -- congruence.
    + destruct H as [l' [[Heq'|Hin'] Hl']].
      * congruence.
      * assert (c_eval m c = Some true).
        -- apply Hind. now exists l'.
        -- congruence.
Qed.

Lemma c_eval_false_iff: forall (m: PA) (c: Clause),
  c_eval m c = Some false <-> forall (l: Lit), In l c -> l_eval m l = Some false.
Proof.
  intros. split.
  - intros. funelim (c_eval m c); try congruence.
    + contradiction.
    + destruct H0.
      * congruence.
      * now apply (Hind m c).
  - intros. funelim (c_eval m c); try congruence.
    + pose proof (H _ (in_eq _ _)). congruence.
    + assert (c_eval m c = Some false).
      * apply Hind. intros. apply H. now right.
      * congruence.
    + assert (c_eval m c = Some false).
      * apply Hind. intros. apply H. now right.
      * congruence.
    + assert (c_eval m c = Some false).
      * apply Hind. intros. apply H. now right.
      * congruence.
    + pose proof (H _ (in_eq _ _)). congruence.
    + pose proof (H _ (in_eq _ _)). congruence.
Qed.

Lemma c_eval_none_iff: forall (m: PA) (c: Clause),
  c_eval m c = None <-> 
    (~ exists (l: Lit), In l c /\ l_eval m l = Some true) /\
       exists (l: Lit), In l c /\ l_eval m l = None.
Proof.
  unfold not. intros. induction c as [|l c IH].
  - split.
    + intros. discriminate.
    + intros [H H']. now destruct H'.
  - split.
    + intros Hc. split.
      * intros [l' [[Heq|Hin'] Hl']].
        -- subst l'. assert (c_eval m (l :: c) = Some true).
          ++ apply c_eval_true_iff. exists l. split.
            ** now left.
            ** assumption.
          ++ congruence.
        -- assert (c_eval m (l :: c) = Some true).
          ++ apply c_eval_true_iff. exists l'. split.
            ** now right.
            ** assumption.
          ++ congruence.
      * simp c_eval in Hc. destruct (l_eval m l) as [[|]|] eqn:Hl.
        -- discriminate.
        -- destruct (c_eval m c) as [[|]|] eqn:Hc'; try easy.
           simpl in Hc. apply IH in Hc as [_ [l' [Hin' Hl']]].
           exists l'. split.
          ++ now right.
          ++ assumption.
        -- exists l. split.
          ++ now left.
          ++ assumption.
    + intros [H H']. destruct (l_eval m l) as [[|]|] eqn:Hl.
      * exfalso. apply H. exists l. split.
        -- now left.
        -- assumption.
      * simp c_eval. rewrite Hl. simpl. destruct (c_eval m c) as [[|]|] eqn:Hc'; try easy.
        -- rewrite c_eval_true_iff in Hc'. destruct Hc' as [l' [Hin' Hl']].
           exfalso. apply H. exists l'. split.
          ++ now right.
          ++ assumption.
        -- rewrite c_eval_false_iff in Hc'. destruct H' as [l' [[Heq|Hin'] Hl']].
          ++ congruence.
          ++ apply Hc' in Hin'. congruence.
      * simp c_eval. rewrite Hl. simpl. destruct (c_eval m c) as [[|]|] eqn:Hc'; try easy.
        rewrite c_eval_true_iff in Hc'. destruct Hc' as [l' [Hin' Hl']].
        exfalso. apply H. exists l'. split.
        -- now right.
        -- assumption.
Qed.

Lemma undef_remove_false__undef: forall (m: PA) (c: Clause) (l: Lit),
  c_eval m c = None -> c_eval m (l_remove c l) = Some false -> Undef m l.
Proof.
  unfold Undef. intros. 
  apply c_eval_none_iff in H as [_ [l' [Hin' Hl']]].
  rewrite (c_eval_false_iff m (l_remove c l)) in H0.
  destruct (l =? l') eqn:G.
  - rewrite eqb_eq in G. congruence.
  - assert (In l' (l_remove c l)).
    + rewrite eqb_neq in G. now apply l_remove_in_iff.
    + apply H0 in H. congruence.
Qed.

Lemma c_eval_remove_false_l: forall (m: PA) (c: Clause) (l: Lit),
  c_eval m (l_remove c l) = Some false -> l_eval m l = Some false -> c_eval m c = Some false.
Proof.
  intros m c l Hc Hl. apply c_eval_false_iff. intros l' Hin. rewrite c_eval_false_iff in Hc.
  destruct (l =? l') eqn:Heq.
  - rewrite eqb_eq in Heq. congruence.
  - rewrite eqb_neq in Heq. apply Hc. now apply l_remove_in_iff.
Qed.

Lemma c_eval_remove_none_l: forall (m: PA) (c: Clause) (l: Lit),
  In l c -> c_eval m (l_remove c l) = Some false -> l_eval m l = None -> c_eval m c = None.
Proof.
  intros m c l Hin Hc Hl. rewrite c_eval_false_iff in Hc. apply c_eval_none_iff. split.
  - unfold not. intros [l' [Hin' Hl']]. destruct (l =? l') eqn:Heq.
    + rewrite eqb_eq in Heq. congruence.
    + rewrite eqb_neq in Heq. assert (In l' (l_remove c l)).
      * now apply l_remove_in_iff.
      * apply Hc in H. congruence.
  - now exists l.
Qed.

Lemma f_eval_false_iff: forall (m: PA) (f: CNF),
  f_eval m f = Some false <-> exists (c: Clause), In c f /\ Conflicting m c.
Proof.
  unfold Conflicting. intros. split.
  - intros. funelim (f_eval m f); try congruence.
    + rewrite H in Heqcall. apply Hind in Heqcall.
      * destruct Heqcall as [c' G]. exists c'. auto with *.
      * reflexivity.
      * reflexivity.
    + exists c. auto with *.
    + apply Hind in Heq.
      * destruct Heq as [c' G]. exists c'. auto with *.
      * reflexivity.
      * reflexivity.
  - intros. funelim (f_eval m f); try congruence.
    + now destruct H.
    + destruct H as [c' [[<-|Hc_in_f] H]].
      * congruence.
      * assert (f_eval m f = Some false).
        -- apply Hind. exists c'. intuition.
        -- congruence.
    + destruct H as [c' [[<-|Hc_in_f] H]].
      * congruence.
      * assert (f_eval m f = Some false).
        -- apply Hind. exists c'. intuition.
        -- congruence.
    + destruct H as [c' [[<-|Hc_in_f] H]].
      * congruence.
      * assert (f_eval m f = Some false).
        -- apply Hind. exists c'. intuition.
        -- congruence.
Qed.

Lemma f_eval_true_iff: forall (m: PA) (f: CNF),
  f_eval m f = Some true <-> forall (c: Clause), In c f -> c_eval m c = Some true.
Proof.
  intros. split.
  - intros. funelim (f_eval m f); try congruence.
    + contradiction.
    + destruct H0.
      * congruence.
      * eapply Hind.
        -- now rewrite Heqcall.
        -- apply H0.
        -- reflexivity.
        -- reflexivity.
  - intros. funelim (f_eval m f).
    + reflexivity.
    + apply Hind. intros. apply H. now right.
    + assert (c_eval m c = Some true).
      * apply H. now left.
      * congruence.
    + assert (c_eval m c = Some true).
      * apply H. now left.
      * congruence.
    + assert (c_eval m c = Some true).
      * apply H. now left.
      * congruence.
    + assert (c_eval m c = Some true).
      * apply H. now left.
      * congruence.
Qed.

Lemma m_eval_true_iff: forall (m m': PA),
  m_eval m m' = Some true <-> forall (l: Lit) (a: Ann), In (l, a) m' -> l_eval m l = Some true.
Proof.
  intros. split.
  - intros. funelim (m_eval m m'); try congruence.
    + contradiction.
    + destruct H0.
      * congruence.
      * eapply Hind.
        -- now rewrite Heqcall.
        -- apply H0.
        -- reflexivity.
        -- reflexivity.
  - intros. funelim (m_eval m m').
    + reflexivity.
    + apply Hind. intros. apply (H l0 a0). now right.
    + assert (l_eval m l = Some true).
      * apply (H _ a). now left.
      * congruence.
    + assert (l_eval m l = Some true).
      * apply (H _ a). now left.
      * congruence.
    + assert (l_eval m l = Some true).
      * apply (H _ a). now left.
      * congruence.
    + assert (l_eval m l = Some true).
      * apply (H _ a). now left.
      * congruence.
Qed.

Lemma c_eval_nil: forall (c: Clause), c_eval [] c = Some false <-> c = [].
Proof.
  intros. split.
  - intros. funelim (c_eval [] c); try congruence. discriminate.
  - intros. now subst c.
Qed.

Lemma m_eval_transfer_l: forall (m m': PA) (l: Lit),
  m_eval m m' = Some true -> l_eval m' l = Some false -> l_eval m l = Some false.
Proof.
  intros. apply l_eval_neg_some_iff. simpl. rewrite m_eval_true_iff in H.
  apply l_eval_false_in in H0 as [a Hin]. now apply H in Hin.
Qed.

Lemma m_eval_transfer_c: forall (m m': PA) (c: Clause),
  m_eval m m' = Some true -> c_eval m' c = Some false -> c_eval m c = Some false.
Proof.
  intros. apply c_eval_false_iff. intros.
  rewrite c_eval_false_iff in H0. apply H0 in H1. 
  now apply (m_eval_transfer_l _ m').
Qed.
