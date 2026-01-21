From Equations Require Import Equations.
From Stdlib Require Import List.
Import ListNotations.
From RocqSAT Require Import Lit Neg Clause CNF Evaluation Trans WellFormed.

Equations c_totalize (m: PA) (c: Clause): PA :=
c_totalize m [] := m;
c_totalize m (l :: c) with l_eval m l :=
  | None := c_totalize (m ++d l) c
  | _    := c_totalize m c.

Equations f_totalize (m: PA) (f: CNF): PA :=
f_totalize m []       := m;
f_totalize m (c :: f) := f_totalize (c_totalize m c) f.

Lemma f_eval_cons: forall (m: PA) (f: CNF) (c: Clause),
  f_eval m (c :: f) = Some true -> 
  f_eval m f = Some true /\ c_eval m c = Some true.
Proof.
  intros. simp f_eval in H. destruct (c_eval m c) as [[|]|] eqn:Hc.
  - intuition.
  - discriminate.
  - now destruct (f_eval m f) as [[|]|].
Qed.

Lemma l_eval_extend_undef: forall (m: PA) (l l': Lit) (a: Ann) (b: bool),
  Undef m l' -> l_eval m l = Some b -> l_eval ((l', a) :: m) l = Some b.
Proof.
  unfold Undef. intros. simp l_eval. destruct (l =? ¬l') eqn:G1, (l =? l') eqn:G2.
  - exfalso. rewrite eqb_eq in G2. subst l'. now rewrite self_neqb_neg in G1.
  - exfalso. rewrite eqb_eq in G1. subst l. apply (undef_neg_iff m l') in H. congruence.
  - exfalso. rewrite eqb_eq in G2. subst l'. congruence.
  - assumption.
Qed.

Lemma c_eval_extend_undef: forall (m: PA) (c: Clause) (l: Lit) (a: Ann) (b: bool),
  Undef m l -> c_eval m c = Some b -> c_eval ((l, a) :: m) c = Some b.
Proof.
  unfold Undef. induction c as [|l c IH].
  - intros. assumption.
  - intros. simp c_eval in *. destruct (l_eval m l) as [[|]|] eqn:Hl.
    + now rewrite (l_eval_extend_undef m l l0 a true H Hl).
    + rewrite (l_eval_extend_undef m l l0 a false H Hl). simpl in *.
      destruct (c_eval m c) as [[|]|] eqn:Hc.
      * rewrite (IH l0 a b H H0). now injection H0 as <-.
      * rewrite (IH l0 a b H H0). now injection H0 as <-.
      * discriminate.
    + destruct (c_eval m c) as [[|]|] eqn:Hc.
      * simpl in H0. rewrite (IH l0 a b H H0). injection H0 as <-.
        now destruct (l_eval ((l0, a) :: m) l) as [[|]|].
      * discriminate.
      * discriminate.
Qed.

Lemma f_eval_extend_undef: forall (m: PA) (f: CNF) (l: Lit) (a: Ann) (b: bool),
  Undef m l -> f_eval m f = Some b -> f_eval ((l, a) :: m) f = Some b.
Proof.
  unfold Undef. induction f as [|c f IH].
  - intros. assumption.
  - intros. simp f_eval in *. destruct (c_eval m c) as [[|]|] eqn:Hc.
    + simpl in H0. rewrite (IH l a b H H0). 
      now rewrite (c_eval_extend_undef m c l a true H Hc).
    + simpl in H0. now rewrite (c_eval_extend_undef m c l a false H Hc).
    + simpl in H0. destruct (f_eval m f) as [[|]|] eqn:Hf.
      * discriminate.
      * rewrite (IH l a b H H0). 
        destruct ((c_eval ((l, a) :: m) c)) as [[|]|].
        -- reflexivity.
        -- assumption.
        -- now injection H0 as <-.
      * discriminate.
Qed.

Lemma c_totalize_l: forall (m: PA) (c: Clause) (l: Lit) (b: bool),
  l_eval m l = Some b -> l_eval (c_totalize m c) l = Some b.
Proof.
  intros. funelim (c_totalize m c).
  - assumption.
  - now apply H.
  - apply H. now apply l_eval_extend_undef.
Qed.

Lemma c_totalize_c: forall (m: PA) (c c': Clause) (b: bool),
  c_eval m c = Some b -> c_eval (c_totalize m c') c = Some b.
Proof.
  intros. funelim (c_totalize m c').
  - assumption.
  - now apply H.
  - apply H. now apply c_eval_extend_undef.
Qed.

Lemma c_totalize_f: forall (m: PA) (f: CNF) (c: Clause) (b: bool),
  f_eval m f = Some b -> f_eval (c_totalize m c) f = Some b.
Proof.
  intros. funelim (c_totalize m c).
  - assumption.
  - now apply H.
  - apply H. now apply f_eval_extend_undef.
Qed.

Lemma f_totalize_l: forall (m: PA) (f: CNF) (l: Lit) (b: bool),
  l_eval m l = Some b -> l_eval (f_totalize m f) l = Some b.
Proof.
  intros. funelim (f_totalize m f).
  - assumption.
  - apply H. now apply c_totalize_l.
Qed.

Lemma f_totalize_c: forall (m: PA) (f: CNF) (c: Clause) (b: bool),
  c_eval m c = Some b -> c_eval (f_totalize m f) c = Some b.
Proof.
  intros. funelim (f_totalize m f).
  - assumption.
  - apply H. now apply c_totalize_c.
Qed.

Lemma f_totalize_f: forall (m: PA) (f: CNF),
  f_eval m f = Some true -> f_eval (f_totalize m f) f = Some true.
Proof.
  intros. funelim (f_totalize m f).
  - reflexivity.
  - apply f_eval_cons in H0 as [Hf Hc]. simp f_eval.
    assert (c_eval (f_totalize (c_totalize m c) f) c = Some true).
    + apply f_totalize_c. now apply c_totalize_c.
    + rewrite H0. simpl. apply H.
      * now apply c_totalize_f.
      * reflexivity.
      * reflexivity.
Qed.

Lemma c_totalize_all_def: forall (m: PA) (c: Clause) (l: Lit),
  In l c -> Def (c_totalize m c) l.
Proof.
  unfold Def. intros m c. generalize dependent m. induction c as [|l' c IH].
  - now intros.
  - intros. destruct (l_eval m l) eqn:Hl.
    + exists b. now apply c_totalize_l.
    + destruct H as [->|H].
      * simp c_totalize. rewrite Hl. simpl.
        exists true. apply c_totalize_l. simp l_eval.
        rewrite self_neqb_neg. now rewrite eqb_refl.
      * simp c_totalize. destruct (l_eval m l').
        -- simpl. now apply IH.
        -- simpl. now apply IH.
Qed.

Lemma f_totalize_all_def: forall (m: PA) (f: CNF) (l: Lit),
  (exists (c: Clause), In l c /\ In c f) -> Def (f_totalize m f) l.
Proof.
  unfold Def. intros m f. generalize dependent m. induction f as [|c f IH].
  - intros. destruct H as [c [_ Hc_in_f]]. contradiction.
  - intros. destruct H as [c' [Hl_in_c Hc_in_f]].
    destruct (l_eval m l) eqn:Hl.
    + exists b. now apply f_totalize_l.
    + destruct Hc_in_f as [->|Hc_in_f].
      * simp f_totalize. apply (c_totalize_all_def m) in Hl_in_c.
        destruct Hl_in_c as [b Hdef]. exists b. now apply f_totalize_l.
      * simp f_totalize. apply IH. now exists c'.
Qed.

Equations convert_prop (m: PA): PA :=
convert_prop []            := [];
convert_prop ((l, _) :: m) := convert_prop m ++d l.

Lemma convert_prop_l: forall (m: PA) (l: Lit) (v: option bool),
  l_eval m l = v -> l_eval (convert_prop m) l = v.
Proof.
  intros. funelim (convert_prop m).
  - reflexivity.
  - simp l_eval. destruct (l0 =? l), (l0 =? ¬l).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + simpl. now apply H.
Qed.

Lemma convert_prop_c: forall (m: PA) (c: Clause),
  c_eval m c = Some true -> c_eval (convert_prop m) c = Some true.
Proof.
  intros. induction c as [|l c IH].
  - discriminate.
  - simp c_eval in *. destruct (l_eval m l) as [[|]|] eqn:Hl.
    + apply convert_prop_l in Hl. now rewrite Hl. 
    + simpl in H. destruct (c_eval m c) as [[|]|] eqn:Hc.
      * apply convert_prop_l in Hl. rewrite Hl.
        apply IH in H. now rewrite H.
      * discriminate.
      * discriminate.
    + simpl in H. destruct (c_eval m c) as [[|]|] eqn:Hc.
      * apply convert_prop_l in Hl. rewrite Hl.
        apply IH in H. now rewrite H.
      * discriminate.
      * discriminate.
Qed.

Lemma convert_prop_f: forall (m: PA) (f: CNF),
  f_eval m f = Some true -> f_eval (convert_prop m) f = Some true.
Proof.
  intros. induction f as [|c f IH].
  - reflexivity.
  - simp f_eval in H. destruct (c_eval m c) as [[|]|] eqn:Hc.
    + simpl in H. apply convert_prop_c in Hc. simp f_eval.
      rewrite Hc. apply IH in H. rewrite H. reflexivity.
    + discriminate.
    + now destruct (f_eval m f) as [[|]|].
Qed.

Lemma convert_prop_only_dec: forall (m: PA) (l: Lit) (a: Ann),
  In (l, a) (convert_prop m) -> a = dec.
Proof.
  intros. funelim (convert_prop m).
  - contradiction.
  - simp convert_prop in H0. destruct H0.
    + now injection H0 as <- <-.
    + now apply (H l0).
Qed.

Lemma convert_prop_all_def: forall (m: PA) (f: CNF) (l: Lit),
  (exists (c: Clause), In l c /\ In c f) -> 
  Def m l ->
  Def (convert_prop m) l.
Proof.
  unfold Def. intros. funelim (convert_prop m).
  - assumption.
  - simp l_eval. destruct (l0 =? ¬l) eqn:G1, (l0 =? l) eqn:G2.
    + simpl. now exists true.
    + simpl. now exists false.
    + simpl. now exists true.
    + simpl. apply (H f).
      * assumption.
      * simp l_eval in H1. rewrite G1 in H1. now rewrite G2 in H1.
Qed.

Equations bound (m: PA) (f: CNF): PA :=
bound [] f := [];
bound ((l, a) :: m) f with l_in_f f l :=
  | true  := (l, a) :: bound m f
  | false := bound m f.

Lemma c_eval_out_iff: forall (m: PA) (c: Clause) (l: Lit) (a: Ann),
  ~ In l c -> c_eval m c = Some true <-> c_eval ((l, a) :: m) c = Some true.
Admitted.

Lemma c_eval_in: forall (m: PA) (c: Clause) (l: Lit) (a: Ann),
  In l c -> c_eval ((l, a) :: m) c = Some true.
Admitted.

Lemma bound_c: forall (m: PA) (f: CNF) (c: Clause),
  In c f -> c_eval m c = Some true -> c_eval (bound m f) c = Some true.
Proof.
  intros. funelim (bound m f).
  - assumption.
  - destruct (existsb (eqb l) c) eqn:Hl_in_c.
    + apply c_eval_in. apply existsb_exists in Hl_in_c as [l' [Hl_in_c Hl_is_l']].
      rewrite eqb_eq in Hl_is_l'. now subst l'.
    + apply c_eval_out_iff in H1.
      * apply c_eval_out_iff.
        -- admit.
        -- apply H; easy.
      * admit.
  - apply H.
    + assumption.
    + apply c_eval_out_iff in H1.
      * assumption.
      * admit.
    + reflexivity.
    + reflexivity.
Admitted.

Lemma bound_f_aux: forall (m: PA) (f f': CNF),
  incl f f' -> f_eval m f = Some true -> f_eval (bound m f') f = Some true.
Proof.
  intros. induction f as [|c f IH].
  - assumption.
  - assert (f_eval (bound m f') f = Some true).
    + apply IH.
      * unfold incl. intros. apply H. now right.
      * now apply f_eval_cons in H0.
    + assert (c_eval (bound m f') c = Some true).
      * apply bound_c.
        -- apply H. now left.
        -- now apply f_eval_cons in H0.
      * simp f_eval. rewrite H1. now rewrite H2.
Qed.

Lemma bound_f: forall (m: PA) (f: CNF),
  f_eval m f = Some true -> f_eval (bound m f) f = Some true.
Proof. 
  intros. apply bound_f_aux.
  - apply incl_refl.
  - assumption.
Qed.

Lemma bound_bounded: forall (m: PA) (f: CNF), Bounded (bound m f) f.
Proof.
  unfold Bounded. intros. funelim (bound m f).
  - contradiction.
  - simp bound in H0. rewrite Heq in H0. simpl in H0. destruct H0.
    + injection H0 as <- <-. apply l_in_f_iff in Heq as [c [Hx_in_c Hc_in_f]].
      exists c. intuition.
    + now apply H in H0.
  - simp bound in H0. rewrite Heq in H0. simpl in H0. now apply H in H0.
Qed.

Lemma bound_incl: forall (m: PA) (f: CNF), incl (bound m f) m.
Proof.
  unfold incl. intros m f [l a] Hin. funelim (bound m f).
  - contradiction.
  - simp bound in Hin. rewrite Heq in Hin. simpl in Hin. destruct Hin.
    + injection H0 as <- <-. now left.
    + right. now apply H.
  - simp bound in Hin. rewrite Heq in Hin. simpl in Hin. right. now apply H.
Qed.

Lemma bound_all_def: forall (m: PA) (f: CNF) (l: Lit),
  (exists (c: Clause), In l c /\ In c f) -> 
  Def m l ->
  Def (bound m f) l.
Proof.
  unfold Def. intros. funelim (bound m f).
  - assumption.
  - simp l_eval. destruct (l0 =? ¬l) eqn:G1, (l0 =? l) eqn:G2.
    + simpl. now exists true.
    + simpl. now exists false.
    + simpl. now exists true.
    + simpl. apply H.
      * assumption.
      * simp l_eval in H1. rewrite G1 in H1. now rewrite G2 in H1.
  - apply H.
    + assumption.
    + destruct H0 as [c [Hl_in_c Hc_in_f]].
      assert (l_in_f f l0 = true).
      * apply l_in_f_iff. exists c. intuition.
      * simp l_eval in H1. destruct (l0 =? ¬l) eqn:G1, (l0 =? l) eqn:G2.
        -- simpl in H1. rewrite eqb_eq in G2. congruence.
        -- simpl in H1. rewrite eqb_eq in G1. subst l0.
           apply l_in_f_iff in H0 as [c' [Hx_in_c' Hc_in_f']].
           assert (l_in_f f l = true).
          ++ apply l_in_f_iff. exists c'. rewrite involutive in Hx_in_c'. intuition.
          ++ congruence.
        -- simpl in H1. rewrite eqb_eq in G2. congruence.
        -- assumption.
Qed.
