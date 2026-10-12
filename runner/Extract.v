From Stdlib Require Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.

From RocqSAT Require Import Atom.
From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import State.
From RocqSAT.refinement Require Import Table.
From RocqSAT.refinement Require Import Store.
From RocqSAT.refinement Require Import Imperative.
From RocqSAT Require Import Solve.
From RocqSAT Require Import Schedule.
From RocqSAT.utils Require Import Inspect.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

(* The number of solver steps before the first restart; later ones follow the Luby sequence. *)
Definition restart_unit: nat := 2 ^ 14.

(* Restart k comes after restart_unit * luby (k + 1) steps. *)
Definition luby_schedule (k: nat): nat := restart_unit * luby (S k).

Lemma luby_schedule_unbounded: forall (n: nat), exists (k: nat), n < luby_schedule k.
Proof. apply luby_unbounded. unfold restart_unit. simpl. lia. Qed.

(* The solver: the verified strategy run from the initial state of f, with Luby restarts. *)
Definition run (f: CNF): State :=
  solve_restart f luby_schedule luby_schedule_unbounded dpll_bj_keeps_formula next_impl_strategy restart_impl
    restart_impl_inv (initial_impl_inv f).

(* The tables of the store in mutable arrays (runner/store_rt.ml), updated in place: each operation returns the
   same store, changed. This realizes the model of Table.v and Store.v as long as every store is used linearly
   (see Store.v); tmake makes a new array each time it is evaluated, so it only occurs inside functions
   (initial_impl). The monad itself is extracted as defined, and inlined, so that the extracted code passes the
   store along directly. *)
Extract Constant Table "'a" => "'a Store_rt.table".
Extract Inlined Constant tmake => "Store_rt.make".
(* Reading and writing an entry are written out here instead of calling functions of Store_rt, so that OCaml can
   inline them: dune compiles each module with -opaque, which hides function bodies from other modules. An entry
   past the end of the array has the default value, and writing it grows the array (Store_rt.grow_set). *)
Extract Inlined Constant vget => "(fun k st -> (let t = st.svals in
  Store_rt.(if k < Array.length t.data then Array.unsafe_get t.data k else t.default)), st)".
Extract Inlined Constant vset => "(fun k a st -> (let t = st.svals in
  Store_rt.(if k < Array.length t.data then Array.unsafe_set t.data k a else grow_set t k a)); ((), st))".
Extract Inlined Constant cget => "(fun k st -> (let t = st.scmap in
  Store_rt.(if k < Array.length t.data then Array.unsafe_get t.data k else t.default)), st)".
Extract Inlined Constant cset => "(fun k a st -> (let t = st.scmap in
  Store_rt.(if k < Array.length t.data then Array.unsafe_set t.data k a else grow_set t k a)); ((), st))".
Extract Inlined Constant wget => "(fun k st -> (let t = st.swat in
  Store_rt.(if k < Array.length t.data then Array.unsafe_get t.data k else t.default)), st)".
Extract Inlined Constant wset => "(fun k a st -> (let t = st.swat in
  Store_rt.(if k < Array.length t.data then Array.unsafe_set t.data k a else grow_set t k a)); ((), st))".
Extract Inlined Constant lget => "(fun k st -> (let t = st.swls in
  Store_rt.(if k < Array.length t.data then Array.unsafe_get t.data k else t.default)), st)".
Extract Inlined Constant lset => "(fun k a st -> (let t = st.swls in
  Store_rt.(if k < Array.length t.data then Array.unsafe_set t.data k a else grow_set t k a)); ((), st))".
Extract Inlined Constant rget => "(fun k st -> (let t = st.srsn in
  Store_rt.(if k < Array.length t.data then Array.unsafe_get t.data k else t.default)), st)".
Extract Inlined Constant rset => "(fun k a st -> (let t = st.srsn in
  Store_rt.(if k < Array.length t.data then Array.unsafe_set t.data k a else grow_set t k a)); ((), st))".
Extract Inlined Constant dget => "(fun k st -> (let t = st.slvl in
  Store_rt.(if k < Array.length t.data then Array.unsafe_get t.data k else t.default)), st)".
Extract Inlined Constant dset => "(fun k a st -> (let t = st.slvl in
  Store_rt.(if k < Array.length t.data then Array.unsafe_set t.data k a else grow_set t k a)); ((), st))".
Extract Inlined Constant mget => "(fun k st -> (let t = st.smrk in
  Store_rt.(if k < Array.length t.data then Array.unsafe_get t.data k else t.default)), st)".
Extract Inlined Constant mset => "(fun k a st -> (let t = st.smrk in
  Store_rt.(if k < Array.length t.data then Array.unsafe_set t.data k a else grow_set t k a)); ((), st))".
Extract Inlined Constant pget => "(fun k st -> (let t = st.sphs in
  Store_rt.(if k < Array.length t.data then Array.unsafe_get t.data k else t.default)), st)".
Extract Inlined Constant pset => "(fun k a st -> (let t = st.sphs in
  Store_rt.(if k < Array.length t.data then Array.unsafe_set t.data k a else grow_set t k a)); ((), st))".
Extraction Inline ret bind runM.

(* Compare atoms as ints rather than with OCaml's polymorphic equality, and call the EqB instances directly. *)
Extract Inlined Constant Atom.Definitions.EqBAtom => "Int.equal".
(* Likewise for comparing decision levels; ExtrOcamlNatInt would extract these by unary recursion. *)
Extract Inlined Constant Nat.eqb => "Int.equal".
Extract Inlined Constant Nat.leb => "(<=)".
Extract Inlined Constant le_dec => "(fun (n: int) m -> n <= m)".
(* ExtrOcamlNatInt uses the polymorphic Stdlib.max for these, which compares generically. *)
Extract Inlined Constant Nat.max => "(fun (n: int) m -> if n >= m then n else m)".
Extract Inlined Constant Nat.sub => "(fun n m -> let d = n - m in if d > 0 then d else 0)".
Extraction Inline eqb.

Extraction Inline inspect.
Extraction Inline lookupM lookup_trueM lookup_undefM not_falseM add_watchM watchM replace_watchM phaseM.

(* dune collects the extracted files from the current directory. *)
Set Warnings "-extraction-default-directory".
Extraction "solver" run Clause.empty Clause.add CNF.empty CNF.add.
