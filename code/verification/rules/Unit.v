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

(* If a clause is false except for one unassigned literal, assign it to satisfy the clause. *)
Inductive UnitStep: relation State :=
| r_unit (m: PA) (f: CNF) (c: Clause) (l: Lit):
  l ∈ c ->
  c ∈ f ->
  c_eval m (Clause.remove l c) = Some false ->
  Undef m l ->
  UnitStep (state m f) (state ⟨m, l⟩ f).

Lemma unit_same_formula: PreservesFormula UnitStep.
Proof. intros m m' f f' Hstep. now inversion Hstep. Qed.

Lemma unit_well_formed: PreservesWellFormed UnitStep.
Proof.
  intros m m' f f' Hstep Hwf.
  inversion Hstep as [? ? c_unit l_unit Hl_in_c Hc_in_f Hconflict Hundef]; subst.
  apply well_formed_cons.
  - assumption.
  - assumption.
  - left. now exists c_unit.
Qed.

Lemma unit_entails: PreservesEntails UnitStep.
Proof.
  intros m m' f f' Hstep Hentails.
  inversion Hstep as [? ? c_unit l_unit Hl_in_c Hc_in_f Hconflict Hundef]; subst.
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

Lemma unit_state_lt: Decreasing UnitStep.
Proof.
  intros m f s' Hwf Hstep.
  inversion Hstep as [? ? c_unit l_unit Hl_in_c Hc_in_f Hconflict Hundef]; subst.
  apply unit_well_formed in Hstep. apply Hstep in Hwf.
  unfold StateLt, MR. simp state_measure. apply right_slex. apply left_slex.
  now apply score_propagate.
Qed.

Lemma unit_model_final: ModelFinal UnitStep.
Proof.
  intros m f Heq Hall_def [s Hstep].
  inversion Hstep as [? ? c_unit l_unit Hl_in_c Hc_in_f Hconflict Hundef]; subst.
  assert (Def m l_unit).
  - apply Hall_def. now exists c_unit.
  - now apply def_undef in H.
Qed.

(* Unit as a rule of the transition system. *)
Definition Unit: Rule := {|
  step := UnitStep;
  rule_equivalence := preserves_formula_equivalence UnitStep unit_same_formula;
  rule_well_formed := unit_well_formed;
  rule_entails := unit_entails;
  rule_decreasing := unit_state_lt;
  rule_model_final := unit_model_final
|}.
