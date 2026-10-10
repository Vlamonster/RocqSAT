From Stdlib Require Import Relations.

From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import State.
From RocqSAT Require Import Measure.
From RocqSAT Require Import Rule.

(* Fail if all literals are assigned and there is a conflict. *)
Inductive FailStep: relation State :=
| r_fail (m: PA) (f: CNF) (c: Clause):
  CNF.In c f ->
  c_eval m c = Some false ->
  NoDecisions m ->
  FailStep (state m f) fail.

Lemma fail_keeps_formula: KeepsFormula FailStep.
Proof. intros m m' f f' Hstep. inversion Hstep. Qed.

Lemma fail_well_formed: PreservesWellFormed FailStep.
Proof. intros m m' f f' Hstep. inversion Hstep. Qed.

Lemma fail_entails: PreservesEntails FailStep.
Proof. intros m m' f f' Hstep. inversion Hstep. Qed.

Lemma fail_state_lt: Decreasing FailStep.
Proof.
  intros m f s' _ Hstep. inversion Hstep; subst.
  unfold StateLt. now left.
Qed.

Lemma fail_model_final: ModelFinal FailStep.
Proof.
  intros m f Heq Hall_def [s Hstep].
  inversion Hstep as [? ? c_conflict Hc_in_f Hconflict Hno_dec]; subst.
  assert (f_eval m f = Some false).
  - apply f_eval_false_iff. now exists c_conflict.
  - congruence.
Qed.

(* Fail as a rule of the transition system. *)
Definition Fail: Rule := {|
  step := FailStep;
  rule_equivalence := keeps_formula_equivalence FailStep fail_keeps_formula;
  rule_well_formed := fail_well_formed;
  rule_entails := fail_entails;
  rule_decreasing := fail_state_lt;
  rule_model_final := fail_model_final
|}.
