From Stdlib Require Import Relations.

From Equations Require Import Equations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import State.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import Entails.
From RocqSAT Require Import Measure.
From RocqSAT Require Import Rule.

(* Arbitrarily set an unassigned literal in the formula to true. *)
Inductive DecideStep: relation State :=
| r_decide (m: PA) (f: CNF) (c: Clause) (l: Lit):
  Clause.In l c \/ Clause.In (¬l) c ->
  CNF.In c f ->
  Undef m l ->
  DecideStep (state m f) (state (m ++d l) f).

Lemma decide_same_formula: PreservesFormula DecideStep.
Proof. intros m m' f f' Hstep. now inversion Hstep. Qed.

Lemma decide_well_formed: PreservesWellFormed DecideStep.
Proof.
  intros m m' f f' Hstep Hwf.
  inversion Hstep as [? ? c_decide l_decide Hx_in_c Hc_in_f Hundef]; subst.
  apply well_formed_cons.
  - assumption.
  - assumption.
  - apply CNF.l_in_f_true_iff. exists c_decide. intuition.
Qed.

Lemma decide_entails: PreservesEntails DecideStep.
Proof.
  intros m m' f f' Hstep Hentails.
  inversion Hstep as [? ? c_decide l_decide Hx_in_c Hc_in_f Hundef]; subst.
  now apply e_decide.
Qed.

Lemma decide_state_lt: Decreasing DecideStep.
Proof.
  intros m f s' Hwf Hstep.
  inversion Hstep as [? ? c_decide l_decide Hx_in_c Hc_in_f Hundef]; subst.
  apply decide_well_formed in Hstep. apply Hstep in Hwf.
  unfold StateLt. right. unfold MR. simp state_measure. rewrite score_dec.
  - apply right_slex. now apply total_decide.
  - assumption.
Qed.

Lemma decide_model_final: ModelFinal DecideStep.
Proof.
  intros m f Heq Hall_def [s Hstep].
  inversion Hstep as [? ? c_decide l_decide Hx_in_c Hc_in_f Hundef]; subst.
  destruct Hx_in_c as [Hl_in_c|Hnegl_in_c].
  - assert (Def m l_decide).
    + apply Hall_def. now exists c_decide.
    + now apply def_undef in H.
  - assert (Def m (¬l_decide)).
    + apply Hall_def. now exists c_decide.
    + apply def_undef in H. unfold Undef in H. now rewrite <- l_eval_neg_none_iff in H.
Qed.

(* Decide as a rule of the transition system. *)
Definition Decide: Rule := {|
  step := DecideStep;
  rule_equivalence := preserves_formula_equivalence DecideStep decide_same_formula;
  rule_well_formed := decide_well_formed;
  rule_entails := decide_entails;
  rule_decreasing := decide_state_lt;
  rule_model_final := decide_model_final
|}.
