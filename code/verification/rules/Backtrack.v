From Stdlib Require Import List.
From Stdlib Require Import Relations.
Import ListNotations.

From Equations Require Import Equations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import Model.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import State.
From RocqSAT Require Import Rule.
From RocqSAT.entailment Require Import Entails.
From RocqSAT Require Import Measure.

(* Backtrack by flipping the most recent decision literal. *)
Inductive BacktrackStep: relation State :=
| r_backtrack (m n: PA) (f: CNF) (c: Clause) (l: Lit):
  CNF.In c f ->
  c_eval (m ++d l ++a n) c = Some false ->
  NoDecisions n ->
  BacktrackStep (state (m ++d l ++a n) f) (state (m ++p (¬l)) f).

Lemma backtrack_keeps_formula: KeepsFormula BacktrackStep.
Proof. intros m m' f f' Hstep. now inversion Hstep. Qed.

Lemma backtrack_well_formed: PreservesWellFormed BacktrackStep.
Proof.
  intros m m' f f' Hstep Hwf.
  inversion Hstep as [m_split n_split ? c_conflict l_split Hc_in_f Hconflict Hno_dec]; subst.
  unfold WellFormed in *. split.
  - destruct Hwf as [Hnodup _]. apply (nodup_app__nodup (m_split ++d l_split)) in Hnodup.
    assert (Hnodup': NoDuplicates m_split).
    + now apply (nodup_cons__nodup) in Hnodup.
    + apply nodup_cons__undef in Hnodup as Hundef.
      apply l_eval_neg_none_iff in Hundef.
      apply (nodup_cons _ _ _ Hnodup' Hundef).
  - destruct Hwf as [_ Hbounded]. apply (bounded_incl (m_split ++d l_split)) in Hbounded.
    + assert (Hbounded': Bounded m_split f').
      * apply (bounded_incl m_split) in Hbounded.
        -- assumption.
        -- apply incl_tl. apply incl_refl.
      * assert (In (l_split, dec) (m_split ++d l_split)).
        -- now left.
        -- apply Hbounded in H as [c [Hc_in_f' [Hl_in_c|Hnegl_in_c]]].
          ++ intros l' a' Hin. destruct Hin.
            ** injection H as <- <-. exists c. rewrite Neg.involutive. intuition.
            ** now apply Hbounded' in H.
          ++ intros l' a' Hin. destruct Hin.
            ** injection H as <- <-. exists c. intuition.
            ** now apply Hbounded' in H.
    + apply incl_appr. apply incl_refl.
Qed.

(* With a conflict after deciding l, no model of the formula and m makes l true. *)
Lemma backtrack_no_model: forall (m n: PA) (f: CNF) (l: Lit) (m': PA),
  NoDecisions n ->
  Entails f (m ++d l ++a n) ->
  f_eval (m ++d l ++a n) f = Some false ->
  Model m' (CNF.union f (units m)) -> l_eval m' l = Some true -> False.
Proof.
  intros m n f l m' Hno_dec Hentails Hconflict Hm' Hl.
  destruct (entails_extend f (m ++d l) n m' Hentails Hno_dec) as [m'' Hm''].
  - apply model_union_iff in Hm' as [Hf Hm]. apply model_union_iff. split.
    + assumption.
    + rewrite model_units_iff in *. intros l' a' [Heq|Hin].
      * now injection Heq as <- <-.
      * now apply (Hm l' a').
  - apply model_union_iff in Hm'' as [Hf Htrail].
    apply (units_transfer_f m'' _ _ Htrail) in Hconflict. unfold Model in Hf. congruence.
Qed.

(* Hence the formula and m force ¬l. *)
Lemma backtrack_neg: forall (m n: PA) (f: CNF) (l: Lit),
  NoDecisions n ->
  Entails f (m ++d l ++a n) ->
  f_eval (m ++d l ++a n) f = Some false ->
  CNF.union f (units m) ⊨ unit_cnf (¬l).
Proof.
  intros m n f l Hno_dec Hentails Hconflict m' Hm'. apply model_unit_cnf_iff.
  destruct (l_eval m' l) as [[|]|] eqn:Hl.
  - exfalso. now apply (backtrack_no_model m n f l m').
  - now apply l_eval_neg_some_iff in Hl.
  - exfalso. apply (backtrack_no_model m n f l (m' ++p l) Hno_dec Hentails Hconflict).
    + now apply f_eval_extend_undef.
    + simp l_eval. rewrite Neg.self_neqb_neg. now rewrite Lit.eqb_refl.
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
  - apply (entails_prefix f' m_split [(l_split, dec)]). now apply entails_prefix in Hentails.
Qed.

Lemma backtrack_state_lt: Decreasing BacktrackStep.
Proof.
  intros m f s' Hwf Hstep.
  inversion Hstep as [m_split n_split ? c_conflict l_split Hc_in_f Hconflict Hno_dec]; subst.
  pose proof (backtrack_well_formed _ _ _ _ Hstep Hwf) as Hwf'.
  unfold StateLt. right. unfold MR. simp state_measure. apply left_slex.
  apply prefix_app.
  - assumption.
  - assumption.
Qed.

Lemma backtrack_model_final: ModelFinal BacktrackStep.
Proof.
  intros m f Heq Hall_def [s Hstep].
  inversion Hstep as [m_split n_split ? c_conflict l_split Hc_in_f Hconflict Hno_dec]; subst.
  assert (f_eval (m_split ++d l_split ++a n_split) f = Some false).
  - apply f_eval_false_iff. now exists c_conflict.
  - congruence.
Qed.

(* Backtrack as a rule of the transition system. *)
Definition Backtrack: Rule := {|
  step := BacktrackStep;
  rule_equivalence := keeps_formula_equivalence BacktrackStep backtrack_keeps_formula;
  rule_well_formed := backtrack_well_formed;
  rule_entails := backtrack_entails;
  rule_decreasing := backtrack_state_lt;
  rule_model_final := backtrack_model_final
|}.
