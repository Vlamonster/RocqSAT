From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.

(* A state is either the failure state or an assignment for a formula. *)
Inductive State: Type :=
| fail
| state (m: PA) (f: CNF).
