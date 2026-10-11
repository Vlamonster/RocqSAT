(* A store of the solver's tables with a state monad over it.

   NOTE: the extracted solver keeps the store in mutable arrays: tables, tmake and the operations on the tables
   (vget ... lset) are realized in OCaml (runner/Extract.v). The definitions here and in Table.v are their model,
   and every proof is about the model. The realization agrees with the model as long as every store is used
   linearly, i.e. never again after it was passed on: computations built from ret and bind thread the store this
   way, and the only other place that handles a store, the strategy in Imperative.v, does too. *)
From Stdlib Require Import List.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Watches.

(* The tables of the solver: values, clauses, watches and watch lists. *)
Record Store: Type := mkStore {
  svals: Values;
  scmap: ClauseMap;
  swat: Watches;
  swls: WatchLists
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
fun (st: Store) => (tt, mkStore (tset (svals st) k a) (scmap st) (swat st) (swls st)).

Definition cget (k: nat): M (option (list Lit)) := fun (st: Store) => (tget (scmap st) k, st).
Definition cset (k: nat) (a: option (list Lit)): M unit :=
fun (st: Store) => (tt, mkStore (svals st) (tset (scmap st) k a) (swat st) (swls st)).

Definition wget (k: nat): M (Lit * Lit) := fun (st: Store) => (tget (swat st) k, st).
Definition wset (k: nat) (a: Lit * Lit): M unit :=
fun (st: Store) => (tt, mkStore (svals st) (scmap st) (tset (swat st) k a) (swls st)).

Definition lget (k: nat): M (list nat) := fun (st: Store) => (tget (swls st) k, st).
Definition lset (k: nat) (a: list nat): M unit :=
fun (st: Store) => (tt, mkStore (svals st) (scmap st) (swat st) (tset (swls st) k a)).

(* What the operations give, for rewriting under bind. *)
Lemma vget_spec: forall (k: nat) (st: Store), vget k st = (tget (svals st) k, st).
Proof. reflexivity. Qed.

Lemma vset_spec: forall (k: nat) (a: option bool) (st: Store),
  vset k a st = (tt, mkStore (tset (svals st) k a) (scmap st) (swat st) (swls st)).
Proof. reflexivity. Qed.

Lemma cget_spec: forall (k: nat) (st: Store), cget k st = (tget (scmap st) k, st).
Proof. reflexivity. Qed.

Lemma cset_spec: forall (k: nat) (a: option (list Lit)) (st: Store),
  cset k a st = (tt, mkStore (svals st) (tset (scmap st) k a) (swat st) (swls st)).
Proof. reflexivity. Qed.

Lemma wget_spec: forall (k: nat) (st: Store), wget k st = (tget (swat st) k, st).
Proof. reflexivity. Qed.

Lemma wset_spec: forall (k: nat) (a: Lit * Lit) (st: Store),
  wset k a st = (tt, mkStore (svals st) (scmap st) (tset (swat st) k a) (swls st)).
Proof. reflexivity. Qed.

Lemma lget_spec: forall (k: nat) (st: Store), lget k st = (tget (swls st) k, st).
Proof. reflexivity. Qed.

Lemma lset_spec: forall (k: nat) (a: list nat) (st: Store),
  lset k a st = (tt, mkStore (svals st) (scmap st) (swat st) (tset (swls st) k a)).
Proof. reflexivity. Qed.

(* The result and store after bind, given those of its first computation. *)
Lemma bind_spec: forall {A B: Type} (m: M A) (k: A -> M B) (st st': Store) (a: A),
  m st = (a, st') -> bind m k st = k a st'.
Proof. intros A B m k st st' a Hm. unfold bind. now rewrite Hm. Qed.
