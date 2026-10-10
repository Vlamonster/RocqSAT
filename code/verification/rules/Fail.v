From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import State.
From RocqSAT Require Import Rule.
From RocqSAT.entailment Require Import Entails.
From RocqSAT Require Import Measure.

(* Fail if all literals are assigned and there is a conflict. *)
Inductive Fail: Rule :=
| r_fail (m: PA) (f: CNF) (c: Clause) (Hwf: WellFormed m f):
  CNF.In c f ->
  c_eval m c = Some false ->
  NoDecisions m ->
  Fail (state m f Hwf) fail.

Lemma fail_keeps_formula: KeepsFormula Fail.
Proof. intros m m' f f' Hwf Hwf' Hstep. inversion Hstep. Qed.

Lemma fail_entails: PreservesEntails Fail.
Proof. intros m m' f f' Hwf Hwf' Hstep. inversion Hstep. Qed.

Lemma fail_state_lt: Decreasing Fail.
Proof.
  intros m f s' Hwf Hstep. inversion Hstep; subst.
  unfold StateLt. now left.
Qed.

Lemma fail_model_final: ModelFinal Fail.
Proof.
  intros m f Hwf Heq Hall_def [s Hstep].
  inversion Hstep as [? ? c_conflict ? Hc_in_f Hconflict Hno_dec]; subst.
  assert (f_eval m f = Some false).
  - apply f_eval_false_iff. now exists c_conflict.
  - congruence.
Qed.
