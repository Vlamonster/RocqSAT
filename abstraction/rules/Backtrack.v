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

(* Backtrack by flipping the most recent decision literal. *)
Inductive BacktrackStep: relation State :=
| r_backtrack (m n: PA) (f: CNF) (c: Clause) (l: Lit):
  c ∈ f ->
  c_eval ⟨m; l ++ n⟩ c = Some false ->
  NoDecisions n ->
  BacktrackStep (state ⟨m; l ++ n⟩ f) (state ⟨m, (¬l)⟩ f).

Lemma backtrack_same_formula: PreservesFormula BacktrackStep.
Proof. intros m m' f f' Hstep. now inversion Hstep. Qed.

Lemma backtrack_well_formed: PreservesWellFormed BacktrackStep.
Proof.
  intros m m' f f' Hstep Hwf.
  inversion Hstep as [m_split n_split ? c_conflict l_split Hc_in_f Hconflict Hno_dec]; subst.
  unfold WellFormed in *. split.
  - destruct Hwf as [Hnodup _]. apply (nodup_app__nodup ⟨m_split; l_split⟩) in Hnodup.
    assert (Hnodup': NoDuplicates m_split).
    + now apply (nodup_cons__nodup) in Hnodup.
    + apply nodup_cons__undef in Hnodup as Hundef.
      apply l_eval_neg_none_iff in Hundef.
      now apply nodup_cons.
  - destruct Hwf as [_ Hbounded]. apply (bounded_incl ⟨m_split; l_split⟩) in Hbounded.
    + assert (Hbounded': Bounded m_split f').
      * apply (bounded_incl m_split) in Hbounded.
        -- assumption.
        -- intros l Hl. now right.
      * assert (l_split ∈ ⟨m_split; l_split⟩).
        -- now left.
        -- apply Hbounded in H as [Hl_in_f|Hnegl_in_f].
          ++ intros l' [<-|Hin].
            ** right. now rewrite Neg.involutive.
            ** now apply Hbounded'.
          ++ intros l' [<-|Hin].
            ** now left.
            ** now apply Hbounded'.
    + intros l Hl. apply PA.in_app_iff. now right.
Qed.

(* With a conflict after deciding l, no model of the formula and m makes l true. *)
Lemma backtrack_no_model: forall (m n: PA) (f: CNF) (l: Lit) (m': PA),
  NoDecisions n ->
  Entails f ⟨m; l ++ n⟩ ->
  f_eval ⟨m; l ++ n⟩ f = Some false ->
  Model m' (CNF.union f (units m)) -> l_eval m' l = Some true -> False.
Proof.
  intros m n f l m' Hno_dec Hentails Hconflict Hm' Hl.
  destruct (entails_extend f ⟨m; l⟩ n m' Hentails Hno_dec) as [m'' Hm''].
  - apply model_union_iff in Hm' as [Hf Hm]. apply model_union_iff. split.
    + assumption.
    + rewrite model_units_iff in *. intros l' [<-|Hin].
      * assumption.
      * now apply Hm.
  - apply model_union_iff in Hm'' as [Hf Htrail].
    apply (units_transfer_f m'' _ _ Htrail) in Hconflict. unfold Model in Hf. congruence.
Qed.

(* Hence the formula and m force ¬l. *)
Lemma backtrack_neg: forall (m n: PA) (f: CNF) (l: Lit),
  NoDecisions n ->
  Entails f ⟨m; l ++ n⟩ ->
  f_eval ⟨m; l ++ n⟩ f = Some false ->
  CNF.union f (units m) ⊨ unit_cnf (¬l).
Proof.
  intros m n f l Hno_dec Hentails Hconflict m' Hm'. apply model_unit_cnf_iff.
  destruct (l_eval m' l) as [[|]|] eqn:Hl.
  - exfalso. now apply (backtrack_no_model m n f l m').
  - now apply l_eval_neg_some_iff in Hl.
  - exfalso. apply (backtrack_no_model m n f l ⟨m', l⟩ Hno_dec Hentails Hconflict).
    + apply f_eval_preserve with m'.
      * intros l' Hl'. now apply l_eval_cons_undef.
      * assumption.
    + simpl. unfold l_eval_step. now rewrite Lit.eqb_refl.
Qed.

Lemma backtrack_entails: PreservesEntails BacktrackStep.
Proof.
  intros m m' f f' Hstep Hentails.
  inversion Hstep as [m_split n_split ? c_conflict l_split Hc_in_f Hconflict Hno_dec]; subst.
  apply e_propagate.
  - apply (backtrack_neg m_split n_split f' l_split).
    + assumption.
    + assumption.
    + apply f_eval_false_iff. now exists c_conflict.
  - apply (entails_prefix f' m_split ⟨; l_split⟩). now apply entails_prefix in Hentails.
Qed.

Lemma backtrack_state_lt: Decreasing BacktrackStep.
Proof.
  intros m f s' Hwf Hstep.
  inversion Hstep as [m_split n_split ? c_conflict l_split Hc_in_f Hconflict Hno_dec]; subst.
  unfold StateLt, MR. simp state_measure. apply right_slex. apply left_slex.
  apply backtrack_well_formed in Hstep. apply score_backtrack.
  - now apply Hstep.
  - assumption.
Qed.

Lemma backtrack_model_final: ModelFinal BacktrackStep.
Proof.
  intros m f Heq Hall_def [s Hstep].
  inversion Hstep as [m_split n_split ? c_conflict l_split Hc_in_f Hconflict Hno_dec]; subst.
  assert (f_eval ⟨m_split; l_split ++ n_split⟩ f = Some false).
  - apply f_eval_false_iff. now exists c_conflict.
  - congruence.
Qed.

(* Backtrack as a rule of the transition system. *)
Definition Backtrack: Rule := {|
  step := BacktrackStep;
  rule_equivalence := preserves_formula_equivalence BacktrackStep backtrack_same_formula;
  rule_well_formed := backtrack_well_formed;
  rule_entails := backtrack_entails;
  rule_decreasing := backtrack_state_lt;
  rule_model_final := backtrack_model_final
|}.
