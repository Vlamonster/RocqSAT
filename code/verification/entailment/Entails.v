From Stdlib Require Import List.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Model.

(* Semantic consequence: every model of f is a model of g. *)
Definition Consequence (f g: CNF): Prop := forall (m: PA), Model m f -> Model m g.

Notation "f ⊨ g" := (Consequence f g) (at level 70).

(* The entailment invariant on a trail: every propagated literal follows from f and the literals before it, except pure literals, which only have to preserve models. *)
Inductive Entails (f: CNF): PA -> Prop :=
(* The empty assignment. *)
| e_nil: Entails f []
(* A decision is an assumption, so it needs no justification. *)
| e_decide (m: PA) (l: Lit):
  Entails f m -> Entails f (m ++d l)
(* A propagated literal follows from the formula together with the assignment so far. *)
| e_propagate (m: PA) (l: Lit):
  Entails f m -> CNF.union f (units m) ⊨ unit_cnf l -> Entails f (m ++p l)
(* A pure literal does not follow, but making it true keeps every model a model. *)
| e_pure (m: PA) (l: Lit):
  Entails f m ->
  (forall (m': PA), Model m' (CNF.union f (units m)) -> Model (m' ++p l) (CNF.union f (units m))) ->
  Entails f (m ++p l).
