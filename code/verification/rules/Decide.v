From Stdlib Require Import Relations.

From Equations Require Import Equations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import State.
From RocqSAT Require Import Rule.
From RocqSAT.entailment Require Import Entails.
From RocqSAT Require Import Measure.

(* Arbitrarily set an unassigned literal in the formula to true. *)
Inductive Decide: Rule :=
| r_decide (m: PA) (f: CNF) (c: Clause) (l: Lit) (Hwf: WellFormed m f) (Hwf': WellFormed (m ++d l) f):
  Clause.In l c \/ Clause.In (¬l) c ->
  CNF.In c f ->
  Undef m l ->
  Decide (state m f Hwf) (state (m ++d l) f Hwf').

Lemma decide_keeps_formula: KeepsFormula Decide.
Proof. intros m m' f f' Hwf Hwf' Hstep. now inversion Hstep. Qed.

Lemma decide_entails: PreservesEntails Decide.
Proof.
  intros m m' f f' Hwf Hwf' Hstep Hentails.
  inversion Hstep as [? ? c_decide l_decide ? ? Hx_in_c Hc_in_f Hundef]; subst.
  now apply e_decide.
Qed.

Lemma decide_state_lt: Decreasing Decide.
Proof.
  intros m f s' Hwf Hstep.
  inversion Hstep as [? ? c_decide l_decide ? Hwf' Hx_in_c Hc_in_f Hundef]; subst.
  unfold StateLt. right. unfold MR. simp state_measure. rewrite score_dec.
  - apply right_slex. now apply total_decide.
  - assumption.
Qed.

Lemma decide_model_final: ModelFinal Decide.
Proof.
  intros m f Hwf Heq Hall_def [s Hstep].
  inversion Hstep as [? ? c_decide l_decide ? Hwf' Hx_in_c Hc_in_f Hundef]; subst.
  destruct Hx_in_c as [Hl_in_c|Hnegl_in_c].
  - assert (Def m l_decide).
    + apply Hall_def. now exists c_decide.
    + now apply def_undef in H.
  - assert (Def m (¬l_decide)).
    + apply Hall_def. now exists c_decide.
    + apply def_undef in H. unfold Undef in H. now rewrite <- l_eval_neg_none_iff in H.
Qed.
