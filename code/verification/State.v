From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import WellFormed.

(* A state is either the failure state or a well-formed assignment for a formula. *)
Inductive State: Type :=
| fail
| state (m: PA) (f: CNF) (Hwf: WellFormed m f).
