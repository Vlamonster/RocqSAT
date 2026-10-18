From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Lookup.

(* Tables indexed by literal: keys, marks, and the watch lists of two watched literals. *)

(* A key for each literal: 2p for Pos p and 2p + 1 for Neg p. *)
Definition lit_key (l: Lit): nat :=
match l with
| Pos p => 2 * p
| Neg p => S (2 * p)
end.

(* Different literals have different keys. *)
Lemma lit_key_inj: forall (l l': Lit), lit_key l = lit_key l' -> l = l'.
Proof. intros [p|p] [p'|p'] Heq; simpl in Heq; f_equal; lia. Qed.

(* No literal is marked: the marks of conflict analysis, a table by lit_key. *)
Definition Unmarked (mk: Table bool): Prop := forall (y: Lit), tget mk (lit_key y) = false.

(* The literals of each clause of the formula by index, its first two literals being its
   watches. Clauses and watch lists are tables, so their lookups take constant time. *)
Definition ClauseMap: Type := Table (option (list Lit)).

(* A watcher: a clause and its blocker, a literal of the clause that is checked before the
   clause itself. *)
Definition Watcher: Type := nat * Lit.

(* For each literal, by lit_key, the watchers of the clauses that watch it. *)
Definition WatchLists: Type := Table (list Watcher).

(* The watchers of the clauses that watch l. *)
Definition watching (wl: WatchLists) (l: Lit): list Watcher := tget wl (lit_key l).

(* Setting the watchers of l, by cases on the literal. *)
Lemma watching_set: forall (wl: WatchLists) (l l': Lit) (ns: list Watcher),
  watching (tset wl (lit_key l) ns) l' = if Lit.eq_dec l l' then ns else watching wl l'.
Proof.
  intros wl l l' ns. unfold watching. destruct (Lit.eq_dec l l') as [<-|Hneq].
  - apply tget_tset_same.
  - apply tget_tset_other. intros Heq. apply Hneq. now apply lit_key_inj.
Qed.

(* Whether l is not false in v. *)
Definition not_false (v: Values) (l: Lit): bool :=
match lookup v l with
| Some false => false
| _          => true
end.

(* Clause i has a watcher among ws. *)
Definition HasWatcher (ws: list Watcher) (i: nat): Prop := exists (b: Lit), In (i, b) ws.
