(* A store of the solver's tables with a state monad over it.

   NOTE: the extracted solver keeps the store in mutable arrays: tables, tmake and the operations on the tables
   (vget ... pset) are realized in OCaml (runner/Extract.v). The definitions here and in Table.v are their model,
   and every proof is about the model. The realization agrees with the model as long as every store is used
   linearly, i.e. never again after it was passed on: computations built from ret and bind thread the store this
   way, and the only other place that handles a store, the strategy in Imperative.v, does too. *)
From Stdlib Require Import List.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Watches.

(* The tables of the solver: values, clauses, watches and watch lists, the reasons and levels hints, the marks of
   the analysis and the phases. *)
Record Store: Type := mkStore {
  svals: Values;
  scmap: ClauseMap;
  swat: Watches;
  swls: WatchLists;
  srsn: Table nat;
  slvl: Table nat;
  smrk: Table bool;
  sphs: Values
}.

(* A computation on the store with a result of type A. *)
Definition M (A: Type): Type := Store -> A * Store.

Definition ret {A: Type} (a: A): M A := fun (st: Store) => (a, st).

Definition bind {A B: Type} (m: M A) (k: A -> M B): M B :=
fun (st: Store) => let (a, st') := m st in k a st'.

Arguments bind : simpl never.

(* Run a computation on a store, giving its result and the store after it. *)
Definition runM {A: Type} (m: M A) (st: Store): A * Store := m st.

(* Reading and writing an entry of each table. *)
Definition vget (k: nat): M (option bool) := fun (st: Store) => (tget (svals st) k, st).
Definition vset (k: nat) (a: option bool): M unit :=
fun (st: Store) => (tt, mkStore (tset (svals st) k a) (scmap st) (swat st) (swls st) (srsn st) (slvl st) (smrk st) (sphs st)).

Definition cget (k: nat): M (option (list Lit)) := fun (st: Store) => (tget (scmap st) k, st).
Definition cset (k: nat) (a: option (list Lit)): M unit :=
fun (st: Store) => (tt, mkStore (svals st) (tset (scmap st) k a) (swat st) (swls st) (srsn st) (slvl st) (smrk st) (sphs st)).

Definition wget (k: nat): M (Lit * Lit) := fun (st: Store) => (tget (swat st) k, st).
Definition wset (k: nat) (a: Lit * Lit): M unit :=
fun (st: Store) => (tt, mkStore (svals st) (scmap st) (tset (swat st) k a) (swls st) (srsn st) (slvl st) (smrk st) (sphs st)).

Definition lget (k: nat): M (list nat) := fun (st: Store) => (tget (swls st) k, st).
Definition lset (k: nat) (a: list nat): M unit :=
fun (st: Store) => (tt, mkStore (svals st) (scmap st) (swat st) (tset (swls st) k a) (srsn st) (slvl st) (smrk st) (sphs st)).

Definition rget (k: nat): M nat := fun (st: Store) => (tget (srsn st) k, st).
Definition rset (k: nat) (a: nat): M unit :=
fun (st: Store) => (tt, mkStore (svals st) (scmap st) (swat st) (swls st) (tset (srsn st) k a) (slvl st) (smrk st) (sphs st)).

Definition dget (k: nat): M nat := fun (st: Store) => (tget (slvl st) k, st).
Definition dset (k: nat) (a: nat): M unit :=
fun (st: Store) => (tt, mkStore (svals st) (scmap st) (swat st) (swls st) (srsn st) (tset (slvl st) k a) (smrk st) (sphs st)).

Definition mget (k: nat): M bool := fun (st: Store) => (tget (smrk st) k, st).
Definition mset (k: nat) (a: bool): M unit :=
fun (st: Store) => (tt, mkStore (svals st) (scmap st) (swat st) (swls st) (srsn st) (slvl st) (tset (smrk st) k a) (sphs st)).

Definition pget (k: nat): M (option bool) := fun (st: Store) => (tget (sphs st) k, st).
Definition pset (k: nat) (a: option bool): M unit :=
fun (st: Store) => (tt, mkStore (svals st) (scmap st) (swat st) (swls st) (srsn st) (slvl st) (smrk st) (tset (sphs st) k a)).

(* What the operations give, for rewriting under bind. *)
Lemma vget_spec: forall (k: nat) (st: Store), vget k st = (tget (svals st) k, st).
Proof. reflexivity. Qed.

Lemma vset_spec: forall (k: nat) (a: option bool) (st: Store),
  vset k a st = (tt, mkStore (tset (svals st) k a) (scmap st) (swat st) (swls st) (srsn st) (slvl st) (smrk st) (sphs st)).
Proof. reflexivity. Qed.

Lemma cget_spec: forall (k: nat) (st: Store), cget k st = (tget (scmap st) k, st).
Proof. reflexivity. Qed.

Lemma cset_spec: forall (k: nat) (a: option (list Lit)) (st: Store),
  cset k a st = (tt, mkStore (svals st) (tset (scmap st) k a) (swat st) (swls st) (srsn st) (slvl st) (smrk st) (sphs st)).
Proof. reflexivity. Qed.

Lemma wget_spec: forall (k: nat) (st: Store), wget k st = (tget (swat st) k, st).
Proof. reflexivity. Qed.

Lemma wset_spec: forall (k: nat) (a: Lit * Lit) (st: Store),
  wset k a st = (tt, mkStore (svals st) (scmap st) (tset (swat st) k a) (swls st) (srsn st) (slvl st) (smrk st) (sphs st)).
Proof. reflexivity. Qed.

Lemma lget_spec: forall (k: nat) (st: Store), lget k st = (tget (swls st) k, st).
Proof. reflexivity. Qed.

Lemma lset_spec: forall (k: nat) (a: list nat) (st: Store),
  lset k a st = (tt, mkStore (svals st) (scmap st) (swat st) (tset (swls st) k a) (srsn st) (slvl st) (smrk st) (sphs st)).
Proof. reflexivity. Qed.

Lemma rget_spec: forall (k: nat) (st: Store), rget k st = (tget (srsn st) k, st).
Proof. reflexivity. Qed.

Lemma rset_spec: forall (k: nat) (a: nat) (st: Store),
  rset k a st = (tt, mkStore (svals st) (scmap st) (swat st) (swls st) (tset (srsn st) k a) (slvl st) (smrk st) (sphs st)).
Proof. reflexivity. Qed.

Lemma dget_spec: forall (k: nat) (st: Store), dget k st = (tget (slvl st) k, st).
Proof. reflexivity. Qed.

Lemma dset_spec: forall (k: nat) (a: nat) (st: Store),
  dset k a st = (tt, mkStore (svals st) (scmap st) (swat st) (swls st) (srsn st) (tset (slvl st) k a) (smrk st) (sphs st)).
Proof. reflexivity. Qed.

Lemma mget_spec: forall (k: nat) (st: Store), mget k st = (tget (smrk st) k, st).
Proof. reflexivity. Qed.

Lemma mset_spec: forall (k: nat) (a: bool) (st: Store),
  mset k a st = (tt, mkStore (svals st) (scmap st) (swat st) (swls st) (srsn st) (slvl st) (tset (smrk st) k a) (sphs st)).
Proof. reflexivity. Qed.

Lemma pget_spec: forall (k: nat) (st: Store), pget k st = (tget (sphs st) k, st).
Proof. reflexivity. Qed.

Lemma pset_spec: forall (k: nat) (a: option bool) (st: Store),
  pset k a st = (tt, mkStore (svals st) (scmap st) (swat st) (swls st) (srsn st) (slvl st) (smrk st) (tset (sphs st) k a)).
Proof. reflexivity. Qed.

(* The result and store after bind, given those of its first computation. *)
Lemma bind_spec: forall {A B: Type} (m: M A) (k: A -> M B) (st st': Store) (a: A),
  m st = (a, st') -> bind m k st = k a st'.
Proof. intros A B m k st st' a Hm. unfold bind. now rewrite Hm. Qed.
