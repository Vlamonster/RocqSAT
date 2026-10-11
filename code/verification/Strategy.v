From Stdlib Require Import Relations.

From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import State.
From RocqSAT Require Import Trans.

(* A strategy picks the next state: it never steps from fail, it only stops at states that are final for Basic, and every step it takes is a non-empty derivation. *)
Definition Strategy (next: State -> option State): Prop :=
  (next fail = None) /\
  (forall (s: State), next s = None -> Final Basic s) /\
  (forall (s s': State), next s = Some s' -> s ==>+ s').

(* States produced by a strategy stay reachable from the initial state. *)
Lemma strategy_trans: forall (f: CNF) (s s': State) (next: State -> option State) (Hstrat: Strategy next),
  next s = Some s' ->
  state ⟨⟩ f ==>* s ->
  state ⟨⟩ f ==>* s'.
Proof.
  intros f s s' next Hstrat ns H. eapply rt_trans.
  - apply H.
  - apply Hstrat in ns. now apply clos_t_clos_rt in ns.
Qed.
