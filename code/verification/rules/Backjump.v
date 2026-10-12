From Stdlib Require Import Relations.

From Equations Require Import Equations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import Model.
From RocqSAT Require Import State.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import Entails.
From RocqSAT Require Import Measure.
From RocqSAT Require Import Rule.
From RocqSAT.rules Require Import Backtrack.

(* On a conflict, jump back before a decision and propagate l' with a clause c' that follows from the formula. *)
Inductive BackjumpStep: relation State :=
| r_backjump (m n: PA) (f: CNF) (c c': Clause) (l l': Lit):
  c ∈ f ->
  c_eval ⟨m; l ++ n⟩ c = Some false ->
  f ⊨ CNF.singleton c' ->
  l' ∈ c' ->
  c_eval m (Clause.remove l' c') = Some false ->
  Undef m l' ->
  l' ∈ f \/ ¬l' ∈ f ->
  BackjumpStep (state ⟨m; l ++ n⟩ f) (state ⟨m, l'⟩ f).

Lemma backjump_same_formula: PreservesFormula BackjumpStep.
Proof. intros m m' f f' Hstep. now inversion Hstep. Qed.

Lemma backjump_well_formed: PreservesWellFormed BackjumpStep.
Proof.
  intros m m' f f' Hstep [Hnodup Hbounded].
  inversion Hstep as [m_split n_split ? c_conflict c_bj l_split l_bj Hc_in_f Hconflict Hentailed Hl_in_c
    Hrest Hundef Hl_in_f]; subst.
  apply well_formed_cons.
  - split.
    + apply (nodup_app__nodup ⟨m_split; l_split⟩) in Hnodup. now apply nodup_cons__nodup in Hnodup.
    + apply (bounded_incl m_split) in Hbounded.
      * assumption.
      * intros l Hl. apply PA.in_app_iff. right. now right.
  - assumption.
  - assumption.
Qed.

Lemma backjump_entails: PreservesEntails BackjumpStep.
Proof.
  intros m m' f f' Hstep Hentails.
  inversion Hstep as [m_split n_split ? c_conflict c_bj l_split l_bj Hc_in_f Hconflict Hentailed Hl_in_c
    Hrest Hundef Hl_in_f]; subst.
  apply e_propagate.
  - intros m'' Hm''. apply model_unit_cnf_iff.
    apply model_union_iff in Hm'' as [Hf Hm]. apply Hentailed, model_singleton_iff in Hf.
    apply (units_transfer_c m'' m_split _ Hm) in Hrest.
    destruct (l_eval m'' l_bj) as [[|]|] eqn:Hl.
    + reflexivity.
    + rewrite (c_eval_remove_false _ _ _ Hrest Hl) in Hf. discriminate.
    + rewrite (c_eval_remove_none _ _ _ Hl_in_c Hrest Hl) in Hf. discriminate.
  - apply (entails_prefix f' m_split ⟨; l_split⟩). now apply entails_prefix in Hentails.
Qed.

Lemma backjump_state_lt: Decreasing BackjumpStep.
Proof.
  intros m f s' Hwf Hstep.
  inversion Hstep as [m_split n_split ? c_conflict c_bj l_split l_bj Hc_in_f Hconflict Hentailed Hl_in_c
    Hrest Hundef Hl_in_f]; subst.
  unfold StateLt, MR. simp state_measure. apply right_slex. apply left_slex.
  apply backjump_well_formed in Hstep. apply score_backtrack.
  - now apply Hstep.
  - assumption.
Qed.

Lemma backjump_model_final: ModelFinal BackjumpStep.
Proof.
  intros m f Heq Hall_def [s Hstep].
  inversion Hstep as [m_split n_split ? c_conflict c_bj l_split l_bj Hc_in_f Hconflict Hentailed Hl_in_c
    Hrest Hundef Hl_in_f]; subst.
  assert (f_eval ⟨m_split; l_split ++ n_split⟩ f = Some false).
  - apply f_eval_false_iff. now exists c_conflict.
  - congruence.
Qed.

(* If a model of f makes no literal of ¬l and the negations of m true, then m followed by l has no conflict: extending the model with m would make ¬l true (backtrack_neg). *)
Lemma backtrack_clause_aux: forall (m n: PA) (f: CNF) (l: Lit) (m': PA),
  NoDecisions n ->
  WellFormed (state ⟨m; l ++ n⟩ f) ->
  Entails f ⟨m; l ++ n⟩ ->
  f_eval ⟨m; l ++ n⟩ f = Some false ->
  Model m' f ->
  (forall (l': Lit), l' ∈ Clause.add (¬l) (neg_clause m) -> l_eval m' l' <> Some true) ->
  False.
Proof.
  intros m n f l m' Hno_dec [Hnodup _] Hentails Hconflict Hm' Hnot_true.
  apply (nodup_app__nodup ⟨m; l⟩) in Hnodup.
  apply nodup_cons__undef in Hnodup as Hundef. apply nodup_cons__nodup in Hnodup.
  assert (Hnegl: l_eval ⟨m' ++ m⟩ (¬l) = Some true).
  - apply model_unit_cnf_iff. apply (backtrack_neg m n f l Hno_dec Hentails Hconflict).
    apply model_union_iff. split.
    + apply f_eval_preserve with m'.
      * intros l' Hl'. destruct (l_eval m l') as [[|]|] eqn:Hm.
        -- now apply l_eval_app_some.
        -- exfalso. apply (Hnot_true l').
           ++ apply Clause.add_spec. right. apply neg_clause_spec. now apply l_eval_false_in.
           ++ assumption.
        -- now rewrite l_eval_app_undef.
      * assumption.
    + apply model_units_iff. intros l' Hin. apply l_eval_app_some. now apply nodup_in_true.
  - apply l_eval_neg_none_iff in Hundef. rewrite (l_eval_app_undef m' m (¬l) Hundef) in Hnegl.
    apply (Hnot_true (¬l)).
    + apply Clause.add_spec. now left.
    + assumption.
Qed.

(* A Backtrack step is a Backjump step with c' the clause of ¬l and the negations of the literals before l. *)
Lemma backtrack_backjump: forall (m: PA) (f: CNF) (s': State),
  WellFormed (state m f) -> Entails f m -> BacktrackStep (state m f) s' -> BackjumpStep (state m f) s'.
Proof.
  intros m f s' Hwf Hentails Hstep.
  inversion Hstep as [m_split n_split ? c_conflict l_split Hc_in_f Hconflict Hno_dec]; subst.
  pose proof Hwf as [Hnodup Hbounded].
  apply (nodup_app__nodup ⟨m_split; l_split⟩) in Hnodup as Hnodup_l.
  apply nodup_cons__undef in Hnodup_l as Hundef. apply nodup_cons__nodup in Hnodup_l.
  apply (r_backjump m_split n_split f c_conflict (Clause.add (¬l_split) (neg_clause m_split)) l_split).
  - assumption.
  - assumption.
  - intros m' Hm'. apply model_singleton_iff.
    destruct (c_eval m' (Clause.add (¬l_split) (neg_clause m_split))) as [[|]|] eqn:Hc.
    + reflexivity.
    + exfalso. apply (backtrack_clause_aux m_split n_split f l_split m' Hno_dec Hwf Hentails).
      * apply f_eval_false_iff. now exists c_conflict.
      * assumption.
      * intros l' Hl' Hl'_true. assert (c_eval m' (Clause.add (¬l_split) (neg_clause m_split)) = Some true).
        -- apply c_eval_true_iff. now exists l'.
        -- congruence.
    + exfalso. apply (backtrack_clause_aux m_split n_split f l_split m' Hno_dec Hwf Hentails).
      * apply f_eval_false_iff. now exists c_conflict.
      * assumption.
      * intros l' Hl' Hl'_true. assert (c_eval m' (Clause.add (¬l_split) (neg_clause m_split)) = Some true).
        -- apply c_eval_true_iff. now exists l'.
        -- congruence.
  - apply Clause.add_spec. now left.
  - apply c_eval_false_iff. intros l' Hl'. apply Clause.remove_spec in Hl' as [Hl' Hneq].
    apply Clause.add_spec in Hl' as [Heq|Hin].
    + contradiction.
    + apply l_eval_neg_some_iff. simpl. apply nodup_in_true.
      * assumption.
      * now apply neg_clause_spec.
  - now apply l_eval_neg_none_iff in Hundef.
  - assert (Hl_in_f: l_split ∈ f \/ ¬l_split ∈ f).
    + apply Hbounded. apply PA.in_app_iff. right. now left.
    + rewrite Neg.involutive. now apply or_comm.
Qed.

(* Conversely, if Backjump applies then Backtrack applies, flipping the most recent decision. *)
Lemma backjump_backtrack: forall (m: PA) (f: CNF) (s': State),
  BackjumpStep (state m f) s' -> exists (s'': State), BacktrackStep (state m f) s''.
Proof.
  intros m f s' Hstep.
  inversion Hstep as [m_split n_split ? c_conflict c_bj l_split l_bj Hc_in_f Hconflict Hentailed Hl_in_c
    Hrest Hundef Hl_in_f]; subst.
  destruct (split_last_decision ⟨m_split; l_split ++ n_split⟩) as [[m' l']|] eqn:Hsplit.
  - apply PA.split_last_decision_some_iff in Hsplit as [n' [Heq Hno_dec]]. rewrite Heq in *.
    exists (state ⟨m', (¬l')⟩ f). now apply (r_backtrack m' n' f c_conflict l').
  - exfalso. apply PA.split_last_decision_none_iff in Hsplit. clear - Hsplit.
    induction n_split as [|n IH l|n IH l]; simpl in Hsplit.
    + contradiction.
    + now apply IH.
    + contradiction.
Qed.

(* Backjump as a rule of the transition system. *)
Definition Backjump: Rule := {|
  step := BackjumpStep;
  rule_equivalence := preserves_formula_equivalence BackjumpStep backjump_same_formula;
  rule_well_formed := backjump_well_formed;
  rule_entails := backjump_entails;
  rule_decreasing := backjump_state_lt;
  rule_model_final := backjump_model_final
|}.
