From Stdlib Require Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.
From Stdlib Require Import ExtrOCamlInt63.
From Stdlib Require Import ExtrOCamlPArray.
Extraction NoInline PrimArray.array.

From RocqSAT Require Import Atom.
From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import State.
From RocqSAT.refinement Require Import Table.
From RocqSAT.refinement Require Import NextState.
From RocqSAT Require Import Solve.

(* The solver: the verified strategy run from the initial state of f. *)
Definition run (f: CNF): State := solve f next_state_strategy (initial_context_inv f).

(* The table index of a natural number: nat is extracted to OCaml's int, so this is a constant-time
   conversion. Unverified, like the other realizers of primitive integers and arrays above. *)
Extract Inlined Constant nat_index => "Uint63.of_int".

(* Compare atoms as ints rather than with OCaml's polymorphic equality, and call the EqB instances directly. *)
Extract Inlined Constant Atom.Definitions.EqBAtom => "Int.equal".
Extraction Inline eqb.

(* dune collects the extracted files from the current directory. *)
Set Warnings "-extraction-default-directory".
Extraction "solver" run Clause.empty Clause.add CNF.empty CNF.add.
