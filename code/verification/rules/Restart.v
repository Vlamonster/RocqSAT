From Stdlib Require Import Relations.

From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import State.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import Entails.
From RocqSAT Require Import Rule.

(* Start over from the empty assignment, keeping the formula. This is not a Rule, since it increases the measure:
   Schedule.v only allows it on a schedule. *)
Inductive RestartStep: relation State :=
| r_restart (m: PA) (f: CNF):
  RestartStep (state m f) (state ⟨⟩ f).

Lemma restart_same_formula: PreservesFormula RestartStep.
Proof. intros m m' f f' Hstep. now inversion Hstep. Qed.

Lemma restart_well_formed: PreservesWellFormed RestartStep.
Proof. intros m m' f f' Hstep _. inversion Hstep; subst. apply initial_well_formed. Qed.

Lemma restart_entails: PreservesEntails RestartStep.
Proof. intros m m' f f' Hstep _. inversion Hstep; subst. constructor. Qed.
