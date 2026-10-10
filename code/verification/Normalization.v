From Stdlib Require Import List.
From Stdlib Require Import Relations.
Import ListNotations.

From Equations Require Import Equations.

From RocqSAT Require Import Atom.
From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import Trans.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import Dedupe.

Definition l_totalize (m: PA) (l: Lit): PA :=
match l_eval m l with
| None => m ++d l
| _    => m
end.

Definition c_totalize (m: PA) (c: Clause): PA :=
Clause.fold (fun (l: Lit) (m': PA) => l_totalize m' l) c m.

Definition f_totalize (m: PA) (f: CNF): PA :=
CNF.fold (fun (c: Clause) (m': PA) => c_totalize m' c) f m.

Lemma l_eval_extend_undef: forall (m: PA) (l l': Lit) (a: Ann) (b: bool),
  Undef m l' -> l_eval m l = Some b -> l_eval ((l', a) :: m) l = Some b.
Proof.
  unfold Undef. intros. simp l_eval. destruct (l =? ¬l') eqn:G1, (l =? l') eqn:G2.
  - exfalso. rewrite Lit.eqb_eq in G2. subst l'. now rewrite Neg.self_neqb_neg in G1.
  - exfalso. rewrite Lit.eqb_eq in G1. subst l. apply (l_eval_neg_none_iff m l') in H. congruence.
  - exfalso. rewrite Lit.eqb_eq in G2. subst l'. congruence.
  - assumption.
Qed.

Lemma c_eval_extend_undef: forall (m: PA) (c: Clause) (l: Lit) (a: Ann) (b: bool),
  Undef m l -> c_eval m c = Some b -> c_eval ((l, a) :: m) c = Some b.
Proof.
  intros m c l a b Hundef Hc. destruct b.
  - rewrite c_eval_true_iff in *. destruct Hc as [l' [Hin Hl']].
    exists l'. split.
    + assumption.
    + now apply l_eval_extend_undef.
  - rewrite c_eval_false_iff in *. intros l' Hin. apply l_eval_extend_undef.
    + assumption.
    + now apply Hc.
Qed.

Lemma f_eval_extend_undef: forall (m: PA) (f: CNF) (l: Lit) (a: Ann) (b: bool),
  Undef m l -> f_eval m f = Some b -> f_eval ((l, a) :: m) f = Some b.
Proof.
  intros m f l a b Hundef Hf. destruct b.
  - rewrite f_eval_true_iff in *. intros c Hin. apply c_eval_extend_undef.
    + assumption.
    + now apply Hf.
  - rewrite f_eval_false_iff in *. destruct Hf as [c [Hin Hc]].
    exists c. split.
    + assumption.
    + now apply c_eval_extend_undef.
Qed.

Lemma m_eval_extend_undef: forall (m m': PA) (l: Lit) (a: Ann),
  Undef m l -> m_eval m m' = Some true -> m_eval ((l, a) :: m) m' = Some true.
Proof.
  unfold Undef. intros. apply m_eval_true_iff. intros.
  simp l_eval. destruct (l0 =? l) eqn:G1, (l0 =? ¬l) eqn:G2.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite Lit.eqb_eq in G2. subst l0. rewrite m_eval_true_iff in H0.
    apply H0 in H1. apply l_eval_neg_some_iff in H1. rewrite Neg.involutive in H1. congruence.
  - simpl. rewrite m_eval_true_iff in H0. now apply H0 in H1.
Qed.

Lemma l_totalize_l: forall (m: PA) (l l': Lit) (b: bool),
  l_eval m l' = Some b -> l_eval (l_totalize m l) l' = Some b.
Proof.
  intros. unfold l_totalize. destruct (l_eval m l) eqn:Hl.
  - assumption.
  - now apply l_eval_extend_undef.
Qed.

Lemma l_totalize_c: forall (m: PA) (c: Clause) (l: Lit) (b: bool),
  c_eval m c = Some b -> c_eval (l_totalize m l) c = Some b.
Proof.
  intros. unfold l_totalize. destruct (l_eval m l) eqn:Hl.
  - assumption.
  - now apply c_eval_extend_undef.
Qed.

Lemma l_totalize_f: forall (m: PA) (f: CNF) (l: Lit) (b: bool),
  f_eval m f = Some b -> f_eval (l_totalize m l) f = Some b.
Proof.
  intros. unfold l_totalize. destruct (l_eval m l) eqn:Hl.
  - assumption.
  - now apply f_eval_extend_undef.
Qed.

Lemma c_totalize_l: forall (m: PA) (c: Clause) (l: Lit) (b: bool),
  l_eval m l = Some b -> l_eval (c_totalize m c) l = Some b.
Proof.
  intros m c l b. unfold c_totalize. rewrite Clause.fold_spec. revert m.
  induction (Clause.elements c) as [|l' c' IH].
  - now intros.
  - intros. simpl. apply IH. now apply l_totalize_l.
Qed.

Lemma c_totalize_c: forall (m: PA) (c c': Clause) (b: bool),
  c_eval m c = Some b -> c_eval (c_totalize m c') c = Some b.
Proof.
  intros m c c' b. unfold c_totalize. rewrite Clause.fold_spec. revert m.
  induction (Clause.elements c') as [|l c'' IH].
  - now intros.
  - intros. simpl. apply IH. now apply l_totalize_c.
Qed.

Lemma c_totalize_f: forall (m: PA) (f: CNF) (c: Clause) (b: bool),
  f_eval m f = Some b -> f_eval (c_totalize m c) f = Some b.
Proof.
  intros m f c b. unfold c_totalize. rewrite Clause.fold_spec. revert m.
  induction (Clause.elements c) as [|l c' IH].
  - now intros.
  - intros. simpl. apply IH. now apply l_totalize_f.
Qed.

Lemma f_totalize_l: forall (m: PA) (f: CNF) (l: Lit) (b: bool),
  l_eval m l = Some b -> l_eval (f_totalize m f) l = Some b.
Proof.
  intros m f l b. unfold f_totalize. rewrite CNF.fold_spec. revert m.
  induction (CNF.elements f) as [|c f' IH].
  - now intros.
  - intros. simpl. apply IH. now apply c_totalize_l.
Qed.

Lemma f_totalize_c: forall (m: PA) (f: CNF) (c: Clause) (b: bool),
  c_eval m c = Some b -> c_eval (f_totalize m f) c = Some b.
Proof.
  intros m f c b. unfold f_totalize. rewrite CNF.fold_spec. revert m.
  induction (CNF.elements f) as [|c' f' IH].
  - now intros.
  - intros. simpl. apply IH. now apply c_totalize_c.
Qed.

Lemma f_totalize_f: forall (m: PA) (f: CNF),
  f_eval m f = Some true -> f_eval (f_totalize m f) f = Some true.
Proof.
  intros m f Hf. rewrite f_eval_true_iff in *. intros c Hin. apply f_totalize_c. now apply Hf.
Qed.

Lemma c_totalize_all_def: forall (m: PA) (c: Clause) (l: Lit),
  Clause.In l c -> Def (c_totalize m c) l.
Proof.
  intros m c l. unfold c_totalize. apply Clause.MP.fold_rec.
  - intros c' Hempty Hl_in_c'. now apply Hempty in Hl_in_c'.
  - intros l' m' c' c'' _ _ Hadd IH Hl_in_c''. apply Hadd in Hl_in_c'' as [->|Hl_in_c'].
    + unfold Def, l_totalize. destruct (l_eval m' l) eqn:Hl.
      * now exists b.
      * exists true. simp l_eval. rewrite Neg.self_neqb_neg. now rewrite Lit.eqb_refl.
    + apply IH in Hl_in_c' as [b Hl]. exists b. now apply l_totalize_l.
Qed.

Lemma f_totalize_all_def: forall (m: PA) (f: CNF) (l: Lit),
  (exists (c: Clause), Clause.In l c /\ CNF.In c f) -> Def (f_totalize m f) l.
Proof.
  intros m f l. unfold f_totalize. apply CNF.MP.fold_rec.
  - intros f' Hempty [c [_ Hc_in_f']]. now apply Hempty in Hc_in_f'.
  - intros c m' f' f'' _ _ Hadd IH [c' [Hl_in_c' Hc'_in_f'']].
    apply Hadd in Hc'_in_f'' as [Hequal|Hc'_in_f'].
    + apply Hequal in Hl_in_c'. now apply c_totalize_all_def.
    + destruct IH as [b Hl].
      * now exists c'.
      * exists b. now apply c_totalize_l.
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
  intros m c Hc. rewrite c_eval_true_iff in *. destruct Hc as [l [Hin Hl]].
  exists l. split.
  - assumption.
  - now apply convert_prop_l.
Qed.

Lemma convert_prop_f: forall (m: PA) (f: CNF),
  f_eval m f = Some true -> f_eval (convert_prop m) f = Some true.
Proof.
  intros m f Hf. rewrite f_eval_true_iff in *. intros c Hin. apply convert_prop_c. now apply Hf.
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
  (exists (c: Clause), Clause.In l c /\ CNF.In c f) -> 
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

Lemma bound_l: forall (m: PA) (f: CNF) (l: Lit),
  l_in_f f l = true -> l_eval m l = Some true -> l_eval (bound m f) l = Some true.
Proof.
  intros. funelim (l_eval m l); try congruence.
  - rewrite Lit.eqb_eq in Heq. subst l'. simp bound. rewrite H. simpl. simp l_eval.
    rewrite Lit.eqb_refl. now rewrite Neg.self_neqb_neg.
  - simp bound. destruct (l_in_f f l').
    + simpl. simp l_eval. rewrite Heq. rewrite Heq0. simpl. apply H; try easy. congruence.
    + simpl. apply H; try easy. congruence.
Qed.

Lemma bound_c: forall (m: PA) (f: CNF) (c: Clause),
  CNF.In c f -> c_eval m c = Some true -> c_eval (bound m f) c = Some true.
Proof.
  intros m f c Hc_in_f Hc. rewrite c_eval_true_iff in *. destruct Hc as [l [Hl_in_c Hl]].
  exists l. split.
  - assumption.
  - apply bound_l.
    + apply CNF.l_in_f_true_iff. exists c. split.
      * now left.
      * assumption.
    + assumption.
Qed.

Lemma bound_f: forall (m: PA) (f: CNF),
  f_eval m f = Some true -> f_eval (bound m f) f = Some true.
Proof.
  intros m f Hf. rewrite f_eval_true_iff in *. intros c Hc_in_f. apply bound_c.
  - assumption.
  - now apply Hf.
Qed.

Lemma bound_bounded: forall (m: PA) (f: CNF), Bounded (bound m f) f.
Proof.
  unfold Bounded. intros. funelim (bound m f).
  - contradiction.
  - simp bound in H0. rewrite Heq in H0. simpl in H0. destruct H0.
    + injection H0 as <- <-. apply CNF.l_in_f_true_iff in Heq as [c [Hx_in_c Hc_in_f]].
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

Lemma bound_only_dec: forall (m: PA) (f: CNF),
  (forall (l: Lit) (a: Ann), In (l, a) m -> a = dec) ->
  (forall (l: Lit) (a: Ann), In (l, a) (bound m f) -> a = dec).
Proof. intros. apply (H l). now apply bound_incl in H0. Qed.

Lemma bound_all_def: forall (m: PA) (f: CNF) (l: Lit),
  (exists (c: Clause), Clause.In l c /\ CNF.In c f) -> 
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
      * apply CNF.l_in_f_true_iff. exists c. intuition.
      * simp l_eval in H1. destruct (l0 =? ¬l) eqn:G1, (l0 =? l) eqn:G2.
        -- simpl in H1. rewrite Lit.eqb_eq in G2. congruence.
        -- simpl in H1. rewrite Lit.eqb_eq in G1. subst l0.
           apply CNF.l_in_f_true_iff in H0 as [c' [Hx_in_c' Hc_in_f']].
           assert (l_in_f f l = true).
          ++ apply CNF.l_in_f_true_iff. exists c'. rewrite Neg.involutive in Hx_in_c'. intuition.
          ++ congruence.
        -- simpl in H1. rewrite Lit.eqb_eq in G2. congruence.
        -- assumption.
Qed.

Equations eqb_by_atom (la la': Lit * Ann): bool :=
eqb_by_atom (l, _) (l', _) := extract l =? extract l'. 

Equations dedupe (m: PA): PA :=
dedupe m := dedupe_by eqb_by_atom m.

Lemma extract_neqb_iff: forall (l l': Lit),
  (l =? l') = false ->
  (l =? ¬l') = false ->
  (extract l =? extract l') = false.
Proof. intros. destruct l, l'; simp extract neg in *; now simpl in *. Qed.

Lemma dedupe_l_aux: forall (m: PA) (l l': Lit) (a: Ann),
  (l =? l') = false ->
  (l =? ¬l') = false ->
  l_eval m l = l_eval (filter (neqb_of eqb_by_atom (l', a)) m) l.
Proof.
  induction m as [|[l a] m IH].
  - intros. reflexivity.
  - intros. simp l_eval. destruct (l0 =? l) eqn:G1, (l0 =? ¬l) eqn:G2.
    + rewrite Lit.eqb_eq in G1. subst l0. now rewrite Neg.self_neqb_neg in G2.
    + rewrite Lit.eqb_eq in G1. subst l0. simpl. simp neqb_of.
      simp eqb_by_atom. assert ((extract l' =? extract l) = false).
      * rewrite Atom.eqb_sym. now apply extract_neqb_iff.
      * rewrite H1. simpl. simp l_eval. rewrite Lit.eqb_refl. now rewrite Neg.self_neqb_neg.
    + rewrite Lit.eqb_eq in G2. subst l0. simpl. simp neqb_of.
      simp eqb_by_atom. assert ((extract l' =? extract l) = false).
      * rewrite Atom.eqb_sym. rewrite <- Neg.eqb_compat in H0. rewrite Neg.eqb_compat in H. 
        rewrite Neg.involutive in H. now apply extract_neqb_iff.
      * rewrite H1. simpl. simp l_eval. rewrite Lit.eqb_refl. rewrite Lit.eqb_sym. now rewrite Neg.self_neqb_neg.
    + simpl. simp neqb_of. simp eqb_by_atom. destruct (negb (extract l' =? extract l)).
      * simp l_eval. rewrite G1. rewrite G2. simpl. now apply IH.
      * now apply IH.
Qed.

Lemma dedupe_l: forall (m: PA) (l: Lit) (v: option bool),
  l_eval m l = v -> l_eval (dedupe m) l = v.
Proof.
  intros. simp dedupe. funelim (dedupe_by eqb_by_atom m).
  - reflexivity.
  - destruct l. simp l_eval. destruct (l0 =? l) eqn:G1, (l0 =? ¬l) eqn:G2.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. apply H. symmetry. now apply dedupe_l_aux.
Qed.

Lemma dedupe_c: forall (m: PA) (c: Clause),
  c_eval m c = Some true -> c_eval (dedupe m) c = Some true.
Proof.
  intros m c Hc. rewrite c_eval_true_iff in *. destruct Hc as [l [Hin Hl]].
  exists l. split.
  - assumption.
  - now apply dedupe_l.
Qed.

Lemma dedupe_f: forall (m: PA) (f: CNF),
  f_eval m f = Some true -> f_eval (dedupe m) f = Some true.
Proof.
  intros m f Hf. rewrite f_eval_true_iff in *. intros c Hin. apply dedupe_c. now apply Hf.
Qed.

Lemma dedupe_all_def: forall (m: PA) (f: CNF) (l: Lit),
  (exists (c: Clause), Clause.In l c /\ CNF.In c f) -> 
  Def m l ->
  Def (dedupe m) l.
Proof. unfold Def. intros. destruct H0. apply dedupe_l in H0. now exists x. Qed.

Lemma dedupe_only_dec: forall (m: PA),
  (forall (l: Lit) (a: Ann), In (l, a) m -> a = dec) ->
  (forall (l: Lit) (a: Ann), In (l, a) (dedupe m) -> a = dec).
Proof. intros. apply (H l). simp dedupe in H0. now apply incl_dedupe in H0. Qed.

Lemma dedupe_bounded: forall (m: PA) (f: CNF),
  Bounded m f ->
  Bounded (dedupe m) f.
Proof. 
  unfold Bounded. intros. apply (H l a). simp dedupe in H0. now apply incl_dedupe in H0.
Qed.

Lemma dedupe_no_duplicates: forall (m: PA), NoDuplicates (dedupe m).
Proof.
  unfold NoDuplicates. intros. simp dedupe. funelim (dedupe_by eqb_by_atom m).
  - simpl. constructor.
  - simpl. constructor.
    + unfold not. intros. destruct l. apply in_map_iff in H0 as [x [Heq Hin]].
      apply in_map_iff in Hin as [x' [Heq' Hin']]. simpl in Heq. 
      apply incl_dedupe in Hin'. apply filter_In in Hin' as [_ G].
      destruct x'. simp neqb_of in G. simp eqb_by_atom in G. subst x. simpl in Heq.
      rewrite Heq in G. now rewrite Atom.eqb_refl in G.
    + assumption.
Qed.

Equations normalize (m: PA) (f: CNF): PA :=
normalize m f := dedupe (bound (convert_prop (f_totalize m f)) f).

Lemma normalize_f: forall (m: PA) (f: CNF),
  f_eval m f = Some true -> f_eval (normalize m f) f = Some true.
Proof.
  intros. simp normalize. 
  apply dedupe_f. apply bound_f. apply convert_prop_f. now apply f_totalize_f.
Qed.

Lemma normalize_all_def: forall (m: PA) (f: CNF) (l: Lit),
  (exists (c: Clause), Clause.In l c /\ CNF.In c f) -> Def (normalize m f) l.
Proof.
  intros. simp normalize.
  apply (dedupe_all_def _ f).
  - assumption.
  - apply bound_all_def.
    + assumption.
    + apply (convert_prop_all_def _ f).
      * assumption.
      * now apply f_totalize_all_def.
Qed.

Lemma normalize_only_dec: forall (m: PA) (f: CNF) (l: Lit) (a: Ann),
  In (l, a) (normalize m f) -> a = dec.
Proof.
  intros. simp normalize in H. 
  apply dedupe_only_dec in H.
  - assumption.
  - intros. apply bound_only_dec in H0.
    + assumption.
    + intros. now apply convert_prop_only_dec in H1.
Qed.

Lemma normalize_bounded: forall (m: PA) (f: CNF), Bounded (normalize m f) f.
Proof. intros. simp normalize. apply dedupe_bounded. apply bound_bounded. Qed.

Lemma normalize_no_duplicates: forall (m: PA) (f: CNF), NoDuplicates (normalize m f).
Proof. intros. simp normalize. apply dedupe_no_duplicates. Qed.

Lemma normalize_wf: forall (m: PA) (f: CNF), WellFormed (normalize m f) f.
Proof.
  unfold WellFormed. intros. split.
  - apply normalize_no_duplicates.
  - apply normalize_bounded.
Qed.

Lemma normalize_derivation_aux: forall (m: PA) (f: CNF),
  WellFormed m f ->
  (forall (l: Lit) (a: Ann), In (l, a) m -> a = dec) -> 
  exists (Hwf': WellFormed m f), 
    state [] f (initial_wf f) ==>* state m f Hwf'.
Proof.
  induction m as [|[l a] m IH].
  - intros. exists (initial_wf f). apply rt_refl.
  - intros. destruct a.
    + apply wf_cons__wf in H as H'. apply IH in H' as [Hwf' Htrans].
      * exists H. apply rt_trans with (y := state m f Hwf').
        -- assumption.
        -- apply rt_step. destruct H as [Hno_dup Hbounded].
           unfold Bounded in Hbounded.
           assert (In (l, dec) (m ++d l)).
          ++ now left.
          ++ apply Hbounded in H. destruct H as [c [Hc_in_f Hx_in_c]].
             apply nodup_cons__undef in Hno_dup as Hundef.
             apply (t_decide _ _ c _ _ _ Hx_in_c Hc_in_f Hundef).
      * intros. apply (H0 l0). now right.
    + assert (In (l, prop) (m ++p l)).
      * now left.
      * now apply H0 in H1.
Qed.

Lemma normalize_derivation: forall (m: PA) (f: CNF),
  exists (Hwf: WellFormed (normalize m f) f), 
    state [] f (initial_wf f) ==>* state (normalize m f) f Hwf.
Proof.
  intros. apply normalize_derivation_aux.
  - apply normalize_wf.
  - apply normalize_only_dec.
Qed.
