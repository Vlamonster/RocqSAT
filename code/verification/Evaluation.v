From Stdlib Require Import List.
From Stdlib Require Import Bool.
Import ListNotations.

From Equations Require Import Equations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.

(* An annotation on a literal (Lit * Ann) describing how its value was assigned. *)
Inductive Ann: Type :=
| dec
| prop.

(* A partial assignment for annoted literals. See below for evaluation. *)
Definition PA: Type := list (Lit * Ann).

Declare Scope pa_scope.
Notation "m ++a n" := (n ++ m) (at level 54, left associativity): pa_scope.
Notation "m ++d l" := ((l, dec) :: m) (at level 54, left associativity): pa_scope.
Notation "m ++p l" := ((l, prop) :: m) (at level 54, left associativity): pa_scope.
Open Scope pa_scope.

(* The first instance of `l` or `¬l` determines the value. *)
Equations l_eval (m: PA) (l: Lit): option bool :=
l_eval [] _ := None;
l_eval ((l', _) :: m) l with l =? l', l =? ¬l' :=
  | true, _    := Some true
  | _   , true := Some false
  | _   , _    := l_eval m l.

Definition l_true (m: PA) (l: Lit): bool :=
match l_eval m l with
| Some true => true
| _ => false
end.

Definition l_false (m: PA) (l: Lit): bool :=
match l_eval m l with
| Some false => true
| _ => false
end.

Definition l_undef (m: PA) (l: Lit): bool :=
match l_eval m l with
| None => true
| _ => false
end.

Definition c_eval (m: PA) (c: Clause): option bool :=
if Clause.exists_ (l_true m) c then
  Some true
else if Clause.for_all (l_false m) c then
  Some false
else 
  None.

Definition c_true (m: PA) (c: Clause): bool :=
match c_eval m c with
| Some true => true
| _ => false
end.

Definition c_false (m: PA) (c: Clause): bool :=
match c_eval m c with
| Some false => true
| _ => false
end.

Definition c_undef (m: PA) (c: Clause): bool :=
match c_eval m c with
| None => true
| _ => false
end.

Definition f_eval (m: PA) (f: CNF): option bool :=
if CNF.for_all (c_true m) f then
  Some true
else if CNF.exists_ (c_false m) f then
  Some false
else 
  None.

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

(* Module EvalExamples.
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
End EvalExamples. *)

Lemma l_eval_neg_none_iff: forall (m: PA) (l: Lit), l_eval m l = None <-> l_eval m (¬l) = None.
Proof.
  unfold Undef. intros. funelim (l_eval m l).
  - intuition.
  - intuition.
    + discriminate.
    + apply Lit.eqb_eq in Heq. subst. simp l_eval in H. rewrite Lit.eqb_refl in H. 
      rewrite Lit.eqb_sym in H. rewrite Neg.self_neqb_neg in H. discriminate.
  - intuition.
    + discriminate.
    + apply Lit.eqb_eq in Heq. subst. simp neg in H. rewrite Neg.involutive in H.
      simp l_eval in H. rewrite Lit.eqb_refl in H. rewrite Neg.self_neqb_neg in H. discriminate.
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
    + rewrite Lit.eqb_eq in Heq. subst l'. rewrite H in Heqcall. injection Heqcall as <-.
      simp l_eval. rewrite Lit.eqb_refl. rewrite Neg.eqb_compat. rewrite Neg.involutive. now rewrite Neg.self_neqb_neg.
    + rewrite Lit.eqb_eq in Heq. subst l. rewrite H in Heqcall. injection Heqcall as <-.
      rewrite Neg.involutive. simp l_eval. rewrite Lit.eqb_refl. now rewrite Neg.self_neqb_neg.
    + simp l_eval. rewrite <- Neg.eqb_compat. rewrite Heq0. rewrite Neg.eqb_compat. rewrite Neg.involutive.
      rewrite Heq. simpl. apply H. congruence.
  - intros. funelim (l_eval m l).
    + discriminate.
    + rewrite Lit.eqb_eq in Heq. subst l'. simp l_eval in H. rewrite Lit.eqb_refl in H. rewrite Neg.eqb_compat in H.
      rewrite Neg.involutive in H. rewrite Neg.self_neqb_neg in H. simpl in H. injection H. intros.
      symmetry in H0. apply negb_false_iff in H0. congruence.
    + rewrite Lit.eqb_eq in Heq. subst l. rewrite Neg.involutive in H. simp l_eval in H. rewrite Lit.eqb_refl in H.
      rewrite Neg.self_neqb_neg in H. simpl in H. injection H. intros. symmetry in H0.
      apply negb_true_iff in H0. congruence.
    + apply H. simp l_eval in H0. rewrite <- Neg.eqb_compat in H0. rewrite Heq0 in H0.
      rewrite Neg.eqb_compat in H0. rewrite Neg.involutive in H0. now rewrite Heq in H0.
Qed.

Lemma l_eval_some_iff: forall (m: PA) (l: Lit), 
  (exists (b: bool), l_eval m l = Some b) <-> exists (a: Ann), In (l, a) m \/ In (¬l, a) m.
Proof. 
  intros. split.
  - intros [b H]. funelim (l_eval m l).
    + congruence.
    + rewrite Lit.eqb_eq in Heq. subst l'. exists a. left. now left.
    + rewrite Lit.eqb_eq in Heq. subst. exists a. right. rewrite Neg.involutive. now left.
    + rewrite H0 in Heqcall. apply H in Heqcall as [a' [G|G]].
      * exists a'. left. now right.
      * exists a'. right. now right.
  - intros [a [H|H]].
    + funelim (l_eval m l).
      * contradiction.
      * now exists true.
      * now exists false.
      * apply (H a0). destruct H0.
        -- injection H0 as <- <-. now rewrite Lit.eqb_refl in Heq0.
        -- assumption.
    + funelim (l_eval m l).
      * contradiction.
      * now exists true.
      * now exists false.
      * apply (H a0). destruct H0.
        -- injection H0 as -> ->. rewrite Neg.involutive in Heq. now rewrite Lit.eqb_refl in Heq.
        -- assumption.
Qed.

Lemma l_eval_false_in: forall (m: PA) (l: Lit),
  l_eval m l = Some false -> exists (a: Ann), In (¬l, a) m.
Proof.
  intros. funelim (l_eval m l); try congruence.
  - rewrite Lit.eqb_eq in Heq. subst l. exists a. rewrite Neg.involutive. now left.
  - rewrite H0 in Heqcall. apply H in Heqcall.
    + destruct Heqcall as [a' Hin]. exists a'. now right.
    + reflexivity.
    + reflexivity.
Qed.

Lemma c_eval_true_iff: forall (m: PA) (c: Clause),
  c_eval m c = Some true <-> exists (l: Lit), Clause.In l c /\ l_eval m l = Some true.
Proof.
  intros m c. split.
  - intros Hc. unfold c_eval in Hc. destruct (Clause.exists_ (l_true m) c) eqn:Hexists.
    + apply Clause.exists_spec in Hexists as [l [Hin Htrue]].
      * exists l. split.
        -- assumption.
        -- unfold l_true in Htrue. destruct (l_eval m l) as [[|]|]; easy.
      * now intros ? ? ->.
    + destruct (Clause.for_all (l_false m) c) eqn:Hforall; easy.
  - intros [l [Hin Hl]]. unfold c_eval. assert (Clause.exists_ (l_true m) c = true) as Hexists.
    + apply Clause.exists_spec.
      * now intros ? ? ->.
      * exists l. split.
        -- assumption.
        -- unfold l_true. now rewrite Hl.
    + now rewrite Hexists.
Qed.

Lemma c_eval_false_iff: forall (m: PA) (c: Clause),
  c_eval m c = Some false <-> forall (l: Lit), Clause.In l c -> l_eval m l = Some false.
Proof.
  intros m c. split.
  - intros Hc l Hin. unfold c_eval in Hc. destruct (Clause.exists_ (l_true m) c) eqn:Hexists.
    + discriminate.
    + destruct (Clause.for_all (l_false m) c) eqn:Hforall.
      * apply Clause.for_all_spec in Hforall.
        -- apply Hforall in Hin as Hfalse. unfold l_false in Hfalse. destruct (l_eval m l) as [[|]|]; easy.
        -- now intros ? ? ->.
      * discriminate.
  - intros Hforall. unfold c_eval. destruct (Clause.exists_ (l_true m) c) eqn:Hexists.
    + apply Clause.exists_spec in Hexists as [l [Hin Htrue]].
      * apply Hforall in Hin. unfold l_true in Htrue. now rewrite Hin in Htrue.
      * now intros ? ? ->.
    + assert (Clause.for_all (l_false m) c = true) as Hforall'.
      * apply Clause.for_all_spec.
        -- now intros ? ? ->.
        -- intros l Hin. apply Hforall in Hin as Hl. unfold l_false. destruct (l_eval m l) as [[|]|]; easy.
      * now rewrite Hforall'.
Qed.

Lemma c_eval_none_iff: forall (m: PA) (c: Clause),
  c_eval m c = None <-> 
    (~ exists (l: Lit), Clause.In l c /\ l_eval m l = Some true) /\
       exists (l: Lit), Clause.In l c /\ l_eval m l = None.
Proof.
  intros m c. split.
  - intros Hc. split.
    + unfold not. intros [l [Hin Hl]]. unfold c_eval in Hc. assert (Clause.exists_ (l_true m) c = true) as Hexists.
      * apply Clause.exists_spec.
        -- now intros ? ? ->.
        -- exists l. split.
          ++ assumption.
          ++ unfold l_true. destruct (l_eval m l) as [[|]|]; easy.
      * now rewrite Hexists in Hc.
    + unfold c_eval in Hc. destruct (Clause.exists_ (l_true m) c) eqn:Hexists.
      * discriminate.
      * destruct (Clause.for_all (l_false m) c) eqn:Hforall.
        -- discriminate.
        -- apply Clause.for_all_mem_4 in Hforall as [l [Hin Hfalse]].
          ++ exists l. unfold l_false in Hfalse. destruct (l_eval m l) as [[|]|] eqn:Hl.
            ** apply Clause.exists_mem_2 with (x:=l) in Hexists.
              --- unfold l_true in Hexists. now rewrite Hl in Hexists.
              --- now intros ? ? ->.
              --- assumption.
            ** discriminate.
            ** now apply Clause.mem_spec in Hin.
          ++ now intros ? ? ->.
  - intros [Hexists' [l [Hin Hl]]]. unfold c_eval. destruct (Clause.exists_ (l_true m) c) eqn:Hexists.
    + apply Clause.exists_spec in Hexists as [l' [Hin' Htrue']].
      * exfalso. apply Hexists'. exists l'. split.
        -- assumption.
        -- unfold l_true in Htrue'. destruct (l_eval m l') as [[|]|]; easy.
      * now intros ? ? ->.
    + destruct (Clause.for_all (l_false m) c) eqn:Hforall.
      * apply Clause.for_all_spec in Hforall.
        -- apply Hforall in Hin as Hfalse. unfold l_false in Hfalse. destruct (l_eval m l) as [[|]|]; easy.
        -- now intros ? ? ->.
      * reflexivity.
Qed.

(* Lemma undef_remove_false__undef: forall (m: PA) (c: Clause) (l: Lit),
  c_eval m c = None -> c_eval m (l_remove c l) = Some false -> Undef m l.
Proof.
  unfold Undef. intros. 
  apply c_eval_none_iff in H as [_ [l' [Hin' Hl']]].
  rewrite (c_eval_false_iff m (l_remove c l)) in H0.
  destruct (l =? l') eqn:G.
  - rewrite Lit.eqb_eq in G. congruence.
  - assert (In l' (l_remove c l)).
    + rewrite Lit.eqb_neq in G. now apply l_remove_in_iff.
    + apply H0 in H. congruence.
Qed.

Lemma c_eval_remove_false_l: forall (m: PA) (c: Clause) (l: Lit),
  c_eval m (l_remove c l) = Some false -> l_eval m l = Some false -> c_eval m c = Some false.
Proof.
  intros m c l Hc Hl. apply c_eval_false_iff. intros l' Hin. rewrite c_eval_false_iff in Hc.
  destruct (l =? l') eqn:Heq.
  - rewrite Lit.eqb_eq in Heq. congruence.
  - rewrite Lit.eqb_neq in Heq. apply Hc. now apply l_remove_in_iff.
Qed.

Lemma c_eval_remove_none_l: forall (m: PA) (c: Clause) (l: Lit),
  In l c -> c_eval m (l_remove c l) = Some false -> l_eval m l = None -> c_eval m c = None.
Proof.
  intros m c l Hin Hc Hl. rewrite c_eval_false_iff in Hc. apply c_eval_none_iff. split.
  - unfold not. intros [l' [Hin' Hl']]. destruct (l =? l') eqn:Heq.
    + rewrite Lit.eqb_eq in Heq. congruence.
    + rewrite Lit.eqb_neq in Heq. assert (In l' (l_remove c l)).
      * now apply l_remove_in_iff.
      * apply Hc in H. congruence.
  - now exists l.
Qed. *)

Lemma f_eval_true_iff: forall (m: PA) (f: CNF),
  f_eval m f = Some true <-> forall (c: Clause), CNF.In c f -> c_eval m c = Some true.
Proof.
  intros m f. split.
  - intros Hf c Hin. unfold f_eval in Hf. destruct (CNF.for_all (c_true m) f) eqn:Hforall.
    + apply CNF.for_all_spec in Hforall.
      * apply Hforall in Hin as Htrue. unfold c_true in Htrue. destruct (c_eval m c) as [[|]|]; easy.
      * intros c1 c2 Heq. unfold c_true. unfold c_eval. 
        rewrite (Clause.c_equal_exists _ c1 c2 Heq). now rewrite (Clause.c_equal_forall _ c1 c2 Heq).
    + destruct (CNF.exists_ (c_false m) f) eqn:Hexists.
      * discriminate.
      * discriminate.
  - intros Hforall. unfold f_eval. assert (CNF.for_all (c_true m) f = true) as Hforall'.
    + apply CNF.for_all_spec.
      * intros c1 c2 Heq. unfold c_true. unfold c_eval. 
        rewrite (Clause.c_equal_exists _ c1 c2 Heq). now rewrite (Clause.c_equal_forall _ c1 c2 Heq).
      * intros c Hin. apply Hforall in Hin as Hc. unfold c_true. destruct (c_eval m c) as [[|]|]; easy.
    + now rewrite Hforall'.
Qed.

Lemma f_eval_false_iff: forall (m: PA) (f: CNF),
  f_eval m f = Some false <-> exists (c: Clause), CNF.In c f /\ c_eval m c = Some false.
Proof.
  intros m f. split.
  - intros Hf. unfold f_eval in Hf. destruct (CNF.for_all (c_true m) f) eqn:Hforall.
    + discriminate.
    + destruct (CNF.exists_ (c_false m) f) eqn:Hexists.
      * apply CNF.exists_spec in Hexists as [c [Hin Hfalse]].
        -- exists c. split.
          ++ assumption.
          ++ unfold c_false in Hfalse. destruct (c_eval m c) as [[|]|]; easy.
        -- intros c1 c2 Heq. unfold c_false. unfold c_eval. 
           rewrite (Clause.c_equal_exists _ c1 c2 Heq). now rewrite (Clause.c_equal_forall _ c1 c2 Heq).
      * discriminate.
  - intros [c [Hin Hc]]. unfold f_eval. assert (CNF.for_all (c_true m) f = false) as Hforall.
    + apply CNF.for_all_mem_3 with (x:=c).
      * intros c1 c2 Heq. unfold c_true. unfold c_eval. 
        rewrite (Clause.c_equal_exists _ c1 c2 Heq). now rewrite (Clause.c_equal_forall _ c1 c2 Heq).
      * now apply CNF.mem_spec.
      * unfold c_true. destruct (c_eval m c) as [[|]|]; easy.
    + rewrite Hforall. assert (CNF.exists_ (c_false m) f = true) as Hexists.
      * apply CNF.exists_spec.
        -- intros c1 c2 Heq. unfold c_false. unfold c_eval. 
           rewrite (Clause.c_equal_exists _ c1 c2 Heq). now rewrite (Clause.c_equal_forall _ c1 c2 Heq).
        -- exists c. split.
          ++ assumption.
          ++ unfold c_false. destruct (c_eval m c) as [[|]|]; easy.
      * now rewrite Hexists.
Qed.

Lemma l_eval_false_extend: forall (m m': PA) (l: Lit),
  l_eval m l = Some false -> l_eval (m' ++a m) l = Some false.
Proof.
  intros. funelim (l_eval m l); try congruence.
  - simpl. simp l_eval. rewrite Heq. now rewrite Heq0.
  - simpl. simp l_eval. rewrite Heq. rewrite Heq0. simpl.
    apply H.
    + congruence.
    + reflexivity.
    + reflexivity.
Qed.

Lemma c_eval_false_extend: forall (m m': PA) (c: Clause),
  c_eval m c = Some false -> c_eval (m' ++a m) c = Some false.
Proof.
  intros m m' c Hc. rewrite c_eval_false_iff in *. intros l Hin. apply l_eval_false_extend. now apply Hc.
Qed.

Lemma f_eval_false_extend: forall (m m': PA) (f: CNF),
  f_eval m f = Some false -> f_eval (m' ++a m) f = Some false.
Proof.
  intros m m' f Hf. rewrite f_eval_false_iff in *. destruct Hf as [c [Hin Hc]].
  exists c. split.
  - assumption.
  - now apply c_eval_false_extend.
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

Lemma l_eval_true_extend: forall (m m': PA) (l: Lit),
  l_eval m' l = Some true -> m_eval m' m = Some true -> l_eval (m' ++a m) l = Some true.
Proof.
  induction m as [|[l a] m IH].
  - intros. assumption.
  - intros. simpl. simp l_eval. destruct (l0 =? l) eqn:G1, (l0 =? ¬l) eqn:G2.
    + reflexivity.
    + reflexivity.
    + simpl. rewrite Lit.eqb_eq in G2. subst l0. rewrite m_eval_true_iff in H0.
      assert (l_eval m' l = Some true).
      * apply (H0 _ a). now left.
      * apply l_eval_neg_some_iff in H1. simpl in H1. congruence.
    + simpl. apply IH.
      * assumption.
      * apply m_eval_true_iff. intros. rewrite m_eval_true_iff in H0. apply (H0 _ a0). now right.
Qed.

Lemma c_eval_true_extend: forall (m m': PA) (c: Clause),
  c_eval m' c = Some true -> m_eval m' m = Some true -> c_eval (m' ++a m) c = Some true.
Proof.
  intros m m' c Hc Hm. rewrite c_eval_true_iff in *. destruct Hc as [l [Hin Hl]].
  exists l. split.
  - assumption.
  - now apply l_eval_true_extend.
Qed.

Lemma f_eval_true_extend: forall (m m': PA) (f: CNF),
  f_eval m' f = Some true -> m_eval m' m = Some true -> f_eval (m' ++a m) f = Some true.
Proof.
  intros m m' f Hf Hm. rewrite f_eval_true_iff in *. intros c Hin.
  apply c_eval_true_extend.
  - now apply Hf.
  - assumption.
Qed.

Lemma l_eval_head: forall (m m': PA) (l: Lit),
  l_eval m l = Some true -> l_eval (m' ++a m) l = Some true.
Proof.
  induction m as [|[l' a] m IH].
  - intros. discriminate.
  - intros. simpl. simp l_eval. destruct (l =? ¬l') eqn:G1, (l =? l') eqn:G2; simpl.
    + reflexivity.
    + rewrite Lit.eqb_eq in G1. subst l. simp l_eval in H.
      rewrite Lit.eqb_refl in H. rewrite Neg.eqb_compat in H. rewrite Neg.involutive in H.
      rewrite Neg.self_neqb_neg in H. discriminate.
    + reflexivity.
    + apply IH. simp l_eval in H. rewrite G1 in H. now rewrite G2 in H.
Qed.

Lemma m_eval_head_refl: forall (m m' m'': PA) (l: Lit) (a: Ann),
  Undef m l -> m_eval m m'' = Some true -> m_eval ((l, a) :: m' ++a m) m'' = Some true.
Proof.
  intros. funelim (m_eval m m''); try congruence.
  - reflexivity.
  - apply (Hind m m'0 m' l0 a0) in H as G; try congruence.
    simp m_eval. rewrite G. simp l_eval.
    destruct (l =? ¬l0) eqn:G1, (l =? l0) eqn:G2; simpl.
    + reflexivity.
    + rewrite Lit.eqb_eq in G1. subst l. apply l_eval_neg_some_iff in Heq.
      rewrite Neg.involutive in Heq. simpl in Heq. congruence.
    + reflexivity.
    + apply (l_eval_head _ m'0) in Heq. now rewrite Heq.
Qed.
