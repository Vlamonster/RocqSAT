From Stdlib Require Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import State.
From RocqSAT Require Import Strategy.
From RocqSAT Require Import Solve.

(* The solver: the verified strategy run from the initial state of f. *)
Definition run (f: CNF): State := solve f next_state next_state_strategy.

(* dune collects the extracted files from the current directory. *)
Set Warnings "-extraction-default-directory".
Extraction "solver" run Clause.empty Clause.add CNF.empty CNF.add.
