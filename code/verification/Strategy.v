From Stdlib Require Import Relations.

From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import State.
From RocqSAT Require Import Trans.

(* A strategy picks the next state, using a context of type Ctx that it keeps consistent with the state (Inv):
   it never steps from fail, it only stops at states that are final for Basic, and every step it takes is a
   non-empty derivation to a state with a consistent context. *)
Definition Strategy {Ctx: Type} (Inv: State -> Ctx -> Prop) (next: State * Ctx -> option (State * Ctx)): Prop :=
  (forall (x: Ctx), next (fail, x) = None) /\
  (forall (s: State) (x: Ctx), Inv s x -> next (s, x) = None -> Final Basic s) /\
  (forall (s s': State) (x x': Ctx), Inv s x -> next (s, x) = Some (s', x') -> s ==>+ s' /\ Inv s' x').

(* States produced by a strategy stay reachable from the initial state, with a consistent context. *)
Lemma strategy_trans: forall {Ctx: Type} (Inv: State -> Ctx -> Prop) (next: State * Ctx -> option (State * Ctx))
  (f: CNF) (s s': State) (x x': Ctx),
  Strategy Inv next ->
  Inv s x ->
  next (s, x) = Some (s', x') ->
  state ⟨⟩ f ==>* s ->
  state ⟨⟩ f ==>* s' /\ Inv s' x'.
Proof.
  intros Ctx Inv next f s s' x x' (_ & _ & Hstep) Hinv Hnext H. apply Hstep in Hnext as [Hplus Hinv'].
  - split.
    + apply rt_trans with s.
      * assumption.
      * now apply clos_t_clos_rt.
    + assumption.
  - assumption.
Qed.
