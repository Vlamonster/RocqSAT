From Stdlib Require Import Relations.

From Equations Require Import Equations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import Model.
From RocqSAT Require Import State.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import Entails.
From RocqSAT Require Import Measure.
From RocqSAT Require Import Rule.

(* Adds a literal that only occurs positively. *)
Inductive PureStep: relation State :=
| r_pure (m: PA) (f: CNF) (l: Lit):
  l ∈ f ->
  ¬l ∉ f ->
  Undef m l ->
  PureStep (state m f) (state ⟨m, l⟩ f).

Lemma pure_same_formula: PreservesFormula PureStep.
Proof. intros m m' f f' Hstep. now inversion Hstep. Qed.

Lemma pure_well_formed: PreservesWellFormed PureStep.
Proof.
  intros m m' f f' Hstep Hwf.
  inversion Hstep as [? ? l_pure Hl_in_f Hpure Hundef]; subst.
  apply well_formed_cons.
  - assumption.
  - assumption.
  - now left.
Qed.

Lemma pure_entails: PreservesEntails PureStep.
Proof.
  intros m m' f f' Hstep Hentails.
  inversion Hstep as [? ? l_pure Hl_in_f Hpure Hundef]; subst.
  apply e_pure.
  - intros m'' Hm''. apply model_union_iff in Hm'' as [Hf Hm]. apply model_union_iff. split.
    + now apply model_cons.
    + rewrite model_units_iff in *. intros l Hin. apply l_eval_cons_true.
      * intros ->. apply (def_undef m l_pure).
        -- apply l_eval_some_iff. now right.
        -- assumption.
      * now apply Hm.
  - assumption.
Qed.

Lemma pure_state_lt: Decreasing PureStep.
Proof.
  intros m f s' Hwf Hstep.
  inversion Hstep as [? ? l_pure Hl_in_f Hpure Hundef]; subst.
  apply pure_well_formed in Hstep. apply Hstep in Hwf.
  unfold StateLt, MR. simp state_measure. apply right_slex. apply left_slex.
  now apply score_propagate.
Qed.

Lemma pure_model_final: ModelFinal PureStep.
Proof.
  intros m f Heq Hall_def [s Hstep].
  inversion Hstep as [? ? l_pure Hl_in_f Hpure Hundef]; subst.
  assert (Def m l_pure).
  - now apply Hall_def.
  - now apply def_undef in H.
Qed.

(* Pure as a rule of the transition system. *)
Definition Pure: Rule := {|
  step := PureStep;
  rule_equivalence := preserves_formula_equivalence PureStep pure_same_formula;
  rule_well_formed := pure_well_formed;
  rule_entails := pure_entails;
  rule_decreasing := pure_state_lt;
  rule_model_final := pure_model_final
|}.
