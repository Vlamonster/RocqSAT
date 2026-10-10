From Stdlib Require Import Relations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import Model.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import State.
From RocqSAT.entailment Require Import Entails.
From RocqSAT Require Import Measure.

(* The rule never changes the formula. *)
Definition KeepsFormula (r: relation State): Prop := forall (m m': PA) (f f': CNF),
  r (state m f) (state m' f') -> f = f'.

(* The rule only changes the formula to an equivalent one. *)
Definition PreservesEquivalence (r: relation State): Prop := forall (m m': PA) (f f': CNF),
  r (state m f) (state m' f') -> Equivalent f f'.

(* Every step of the rule from a well-formed state leads to a well-formed state. *)
Definition PreservesWellFormed (r: relation State): Prop := forall (m m': PA) (f f': CNF),
  r (state m f) (state m' f') -> WellFormed (state m f) -> WellFormed (state m' f').

(* Every step of the rule preserves the invariant, relative to the formula of each state. *)
Definition PreservesEntails (r: relation State): Prop := forall (m m': PA) (f f': CNF),
  r (state m f) (state m' f') -> Entails f m -> Entails f' m'.

(* Every step of the rule from a well-formed state of f decreases the measure. *)
Definition Decreasing (r: relation State): Prop := forall (m: PA) (f: CNF) (s': State),
  WellFormed (state m f) -> r (state m f) s' -> state m f >>[f] s'.

(* The rule cannot fire from a model of the formula that defines every literal of it. *)
Definition ModelFinal (r: relation State): Prop := forall (m: PA) (f: CNF),
  Model m f ->
  (forall (l: Lit), (exists (c: Clause), Clause.In l c /\ CNF.In c f) -> Def m l) ->
  ~ exists (s: State), r (state m f) s.

(* A rule that keeps the formula trivially preserves equivalence. *)
Lemma keeps_formula_equivalence: forall (r: relation State), KeepsFormula r -> PreservesEquivalence r.
Proof.
  intros r Hkeep m m' f f' Hstep. apply Hkeep in Hstep as <-. apply equivalent_refl.
Qed.

(* A rule of the transition system: a relation on states together with the properties every rule must have. *)
Record Rule: Type := {
  step: relation State;
  rule_equivalence: PreservesEquivalence step;
  rule_well_formed: PreservesWellFormed step;
  rule_entails: PreservesEntails step;
  rule_decreasing: Decreasing step;
  rule_model_final: ModelFinal step
}.
