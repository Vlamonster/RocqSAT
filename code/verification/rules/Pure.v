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
From RocqSAT Require Import Measure.

(* Adds a literal that only occurs positively. *)
Inductive PureStep: relation State :=
| r_pure (m: PA) (f: CNF) (c: Clause) (l: Lit) (Hwf: WellFormed m f) (Hwf': WellFormed (m ++p l) f):
  Clause.In l c ->
  CNF.In c f ->
  (forall (c': Clause), CNF.In c' f -> ~ Clause.In (¬l) c') ->
  Undef m l ->
  PureStep (state m f Hwf) (state (m ++p l) f Hwf').

Lemma pure_keeps_formula: KeepsFormula PureStep.
Proof. intros m m' f f' Hwf Hwf' Hstep. now inversion Hstep. Qed.

Lemma pure_entails: PreservesEntails PureStep.
Proof.
  intros m m' f f' Hwf Hwf' Hstep Hentails.
  inversion Hstep as [? ? c_pure l_pure ? ? Hl_in_c Hc_in_f Hpure Hundef]; subst.
  apply e_pure.
  - intros m'' Hm''. apply model_union_iff in Hm'' as [Hf Hm]. apply model_union_iff. split.
    + apply f_eval_true_iff. intros c Hc. apply c_eval_true_iff.
      unfold Model in Hf. rewrite f_eval_true_iff in Hf. apply Hf in Hc as G.
      rewrite c_eval_true_iff in G. destruct G as [l [Hin Hl]].
      exists l. split.
      * assumption.
      * simp l_eval. destruct (l =? ¬l_pure) eqn:G1, (l =? l_pure) eqn:G2; simpl.
        -- reflexivity.
        -- exfalso. apply Lit.eqb_eq in G1. subst l. now apply (Hpure c).
        -- reflexivity.
        -- assumption.
    + rewrite model_units_iff in *.
      intros l a Hin. simp l_eval. destruct (l =? ¬l_pure) eqn:G1, (l =? l_pure) eqn:G2; simpl.
      * reflexivity.
      * exfalso. apply Lit.eqb_eq in G1. subst l. apply (def_undef m l_pure).
        -- apply l_eval_some_iff. exists a. now right.
        -- assumption.
      * reflexivity.
      * now apply (Hm l a).
  - assumption.
Qed.

Lemma pure_state_lt: Decreasing PureStep.
Proof.
  intros m f s' Hwf Hstep.
  inversion Hstep as [? ? c_pure l_pure ? Hwf' Hl_in_c Hc_in_f Hpure Hundef]; subst.
  unfold StateLt. right. unfold MR. simp state_measure. apply left_slex.
  now apply prefix_prop.
Qed.

Lemma pure_model_final: ModelFinal PureStep.
Proof.
  intros m f Hwf Heq Hall_def [s Hstep].
  inversion Hstep as [? ? c_pure l_pure ? Hwf' Hl_in_c Hc_in_f Hpure Hundef]; subst.
  assert (Def m l_pure).
  - apply Hall_def. now exists c_pure.
  - now apply def_undef in H.
Qed.

(* Pure as a rule of the transition system. *)
Definition Pure: Rule := {|
  step := PureStep;
  rule_equivalence := keeps_formula_equivalence PureStep pure_keeps_formula;
  rule_entails := pure_entails;
  rule_decreasing := pure_state_lt;
  rule_model_final := pure_model_final
|}.
