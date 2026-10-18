(* The store lemmas of the decision heuristic (see Rep.v): what a store to its arrays
   (act, heap, hpos, dlit) or fields (inc, hsize) does to the represented heuristic. Each
   keeps the bounds HeurOk when the value stored is within them. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs Ctypes Cop
  Clight ClightBigstep.
From RocqSAT Require Import Lit Assignment.
From RocqSAT.refinement Require Import Table Lookup Watches Heur Propagate Analysis Step
  SolverStep.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep.
Import ListNotations.

Section Stores.
  Context {sh: Shape} {N: nat} {lss: list (list Lit)} {x: Ctx}.

  (* Storing the activity v of atom a: s->act[a] = v. *)
  Lemma rep_store_act: forall (m m': mem) (a: nat) (v: Z),
    RepL m sh N lss x -> (a < N)%nat -> (0 <= v < act_lim)%Z ->
    Mem.store Mint32 m (b_act sh) (4 * Z.of_nat a) (vint v) = Some m' ->
    RepL m' sh N lss (x <| hr := set_act (hr x) a v |>).
  Proof.
    intros m m' a v HRep Ha Hv Hst.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (r_heur HRep) as Hok.
    pose proof (arr_store (a_act HRep) Ha Hst) as A.
    destruct HRep. carry Hst Hnd.
    (* Every field is as before, but this array of the heuristic, which A gives. *)
    constructor; try assumption.
    - (* the bounds *)
      apply heur_ok_act.
      + assumption.
      + assumption.
  Qed.

  (* Storing atom b at heap position i: s->heap[i] = b. *)
  Lemma rep_store_heap: forall (m m': mem) (i b: nat),
    RepL m sh N lss x -> (i < N)%nat -> (b < N)%nat ->
    Mem.store Mint32 m (b_heap sh) (4 * Z.of_nat i) (vnat b) = Some m' ->
    RepL m' sh N lss (x <| hr := set_heap (hr x) i b |>).
  Proof.
    intros m m' i b HRep Hi Hb Hst.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (r_heur HRep) as Hok.
    pose proof (arr_store (a_heap HRep) Hi Hst) as A.
    destruct HRep. carry Hst Hnd.
    (* Every field is as before, but this array of the heuristic, which A gives. *)
    constructor; try assumption.
    - (* the array: the entry stored *)
      cbn [set_hr hr set_heap heap]. arr_tset.
    - (* the bounds *)
      apply heur_ok_heap.
      + assumption.
      + assumption.
  Qed.

  (* Storing the heap position o of atom a: s->hpos[a] = enc_pos o. *)
  Lemma rep_store_hpos: forall (m m': mem) (a: nat) (o: option nat),
    RepL m sh N lss x -> (a < N)%nat ->
    (forall (i: nat), o = Some i -> (i < N)%nat) ->
    Mem.store Mint32 m (b_hpos sh) (4 * Z.of_nat a) (vint (enc_pos o)) = Some m' ->
    RepL m' sh N lss (x <| hr := set_hpos (hr x) a o |>).
  Proof.
    intros m m' a o HRep Ha Ho Hst.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (r_heur HRep) as Hok.
    pose proof (arr_store (a_hpos HRep) Ha Hst) as A.
    destruct HRep. carry Hst Hnd.
    (* Every field is as before, but this array of the heuristic, which A gives. *)
    constructor; try assumption.
    - (* the array: the entry stored *)
      cbn [set_hr hr set_hpos hpos]. arr_tset.
    - (* the bounds *)
      apply heur_ok_hpos.
      + assumption.
      + assumption.
  Qed.

  (* Storing the literal o to decide on of atom a: s->dlit[a] = enc_lit o. *)
  Lemma rep_store_dlit: forall (m m': mem) (a: nat) (o: option Lit),
    RepL m sh N lss x -> (a < N)%nat ->
    (forall (l: Lit), o = Some l -> (extract l < N)%nat) ->
    Mem.store Mint32 m (b_dlit sh) (4 * Z.of_nat a) (vint (enc_lit o)) = Some m' ->
    RepL m' sh N lss (x <| hr := set_dlit (hr x) a o |>).
  Proof.
    intros m m' a o HRep Ha Ho Hst.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (r_heur HRep) as Hok.
    pose proof (arr_store (a_dlit HRep) Ha Hst) as A.
    destruct HRep. carry Hst Hnd.
    (* Every field is as before, but this array of the heuristic, which A gives. *)
    constructor; try assumption.
    - (* the array: the entry stored *)
      cbn [set_hr hr set_dlit dlit]. arr_tset.
    - (* the bounds *)
      apply heur_ok_dlit.
      + assumption.
      + assumption.
  Qed.

  (* Storing the bump v: s->inc = v. *)
  Lemma rep_store_inc: forall (m m': mem) (v: Z),
    RepL m sh N lss x -> (1 <= v < act_lim / 2)%Z ->
    Mem.store Mint32 m (b_s sh) o_inc (vint v) = Some m' ->
    RepL m' sh N lss (x <| hr := set_inc (hr x) v |>).
  Proof.
    intros m m' v HRep Hv Hst.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (r_heur HRep) as Hok.
    pose proof (fld_store (r_inc HRep) Hst) as F.
    cbn [Val.load_result] in F. destruct HRep. carry Hst Hnd.
    (* Every field but this one of the heuristic is as before. *)
    constructor; try assumption.
    - (* the bounds *)
      apply heur_ok_inc.
      + assumption.
      + assumption.
  Qed.

  (* Storing the size k of the heap: s->hsize = k. *)
  Lemma rep_store_hsize: forall (m m': mem) (k: nat),
    RepL m sh N lss x -> (k <= N)%nat ->
    Mem.store Mint32 m (b_s sh) o_hsize (vnat k) = Some m' ->
    RepL m' sh N lss (x <| hr := set_hsize (hr x) k |>).
  Proof.
    intros m m' k HRep Hk Hst.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (r_heur HRep) as Hok.
    pose proof (fld_store (r_hsize HRep) Hst) as F.
    cbn [Val.load_result] in F. destruct HRep. carry Hst Hnd.
    (* Every field but this one of the heuristic is as before. *)
    constructor; try assumption.
    - (* the bounds *)
      apply heur_ok_hsize.
      + assumption.
      + assumption.
  Qed.

End Stores.

(* Every block but those the functions of the heuristic write: its arrays and s. *)
Definition HeurFrame (sh: Shape): block -> Z -> Prop :=
  fun (b: block) (_: Z) =>
    b <> b_act sh /\ b <> b_heap sh /\ b <> b_hpos sh /\ b <> b_dlit sh /\ b <> b_s sh.

(* After a function of the heuristic: m' represents x with the heuristic h, and only the
   heuristic changed. *)
Abbreviation HeurPost sh N lss x m h m' :=
  (RepL m' sh N lss (x <| hr := h |>) /\ Mem.unchanged_on (HeurFrame sh) m m').
