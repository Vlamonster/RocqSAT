From Stdlib Require Import Relations.

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
From RocqSAT.entailment Require Import Properties.
From RocqSAT Require Import Measure.

(* If a clause is false except for one unassigned literal, assign it to satisfy the clause. *)
Inductive Unit: Rule :=
| r_unit (m: PA) (f: CNF) (c: Clause) (l: Lit) (Hwf: WellFormed m f) (Hwf': WellFormed (m ++p l) f):
  Clause.In l c ->
  CNF.In c f ->
  c_eval m (Clause.remove l c) = Some false ->
  Undef m l ->
  Unit (state m f Hwf) (state (m ++p l) f Hwf').

Lemma unit_keeps_formula: KeepsFormula Unit.
Proof. intros m m' f f' Hwf Hwf' Hstep. now inversion Hstep. Qed.

Lemma unit_entails: PreservesEntails Unit.
Proof.
  intros m m' f f' Hwf Hwf' Hstep Hentails.
  inversion Hstep as [? ? c_unit l_unit ? ? Hl_in_c Hc_in_f Hconflict Hundef]; subst.
  apply e_propagate.
  - intros m'' Hm''. apply model_unit_cnf_iff.
    apply model_union_iff in Hm'' as [Hf Hm].
    apply (units_transfer_c m'' m _ Hm) in Hconflict.
    unfold Model in Hf. rewrite f_eval_true_iff in Hf. apply Hf in Hc_in_f.
    destruct (l_eval m'' l_unit) as [[|]|] eqn:Hl.
    + reflexivity.
    + rewrite (c_eval_remove_false_l _ _ _ Hconflict Hl) in Hc_in_f. discriminate.
    + rewrite (c_eval_remove_none_l _ _ _ Hl_in_c Hconflict Hl) in Hc_in_f. discriminate.
  - assumption.
Qed.

Lemma unit_state_lt: Decreasing Unit.
Proof.
  intros m f s' Hwf Hstep.
  inversion Hstep as [? ? c_unit l_unit ? Hwf' Hl_in_c Hc_in_f Hconflict Hundef]; subst.
  unfold StateLt. right. unfold MR. simp state_measure. apply left_slex.
  now apply prefix_prop.
Qed.

Lemma unit_model_final: ModelFinal Unit.
Proof.
  intros m f Hwf Heq Hall_def [s Hstep].
  inversion Hstep as [? ? c_unit l_unit ? Hwf' Hl_in_c Hc_in_f Hconflict Hundef]; subst.
  assert (Def m l_unit).
  - apply Hall_def. now exists c_unit.
  - now apply def_undef in H.
Qed.
