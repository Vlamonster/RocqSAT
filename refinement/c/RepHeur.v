(* The store lemmas of the decision heuristic (see Rep.v): what a store to its arrays
   (act, heap, hpos, dlit) or fields (inc, hsize) does to the represented heuristic. Each
   keeps the bounds HeurOk when the value stored is within them. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs Ctypes Cop
  Clight ClightBigstep.
From RocqSAT Require Import Lit Assignment.
From RocqSAT.refinement Require Import Table Lookup Watches Heur Propagate Analysis Step
  CStep SolverStep.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep.
Import ListNotations.

(* Storing the activity v of atom a: s->act[a] = v. *)
Lemma rep_store_act {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (a: nat) (v: Z),
  RepL m S N lss x lims lt -> (a < N)%nat -> (0 <= v < act_lim)%Z ->
  Mem.store Mint32 m (b_act S) (4 * Z.of_nat a) (vint (v)) = Some m' ->
  RepL m' S N lss (with_heur x (set_act (hr x) a v)) lims lt.
Proof.
  intros m m' S N lss x lims a v HRep Ha Hv Hst.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_heur _ _ _ _ _ _ _ HRep) as Hok.
  pose proof (arr_store m m' (b_act S) N a _ _ (a_act _ _ _ _ _ _ _ HRep) Ha
                Hst) as A.
  destruct HRep. unpack. carry Hst Hnd.
  (* Every field is as before, but this array of the heuristic, which A gives. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* the bounds *)
    apply heur_ok_act.
    + assumption.
    + assumption.
Qed.

(* Storing atom b at heap position i: s->heap[i] = b. *)
Lemma rep_store_heap {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (i b: nat),
  RepL m S N lss x lims lt -> (i < N)%nat -> (b < N)%nat ->
  Mem.store Mint32 m (b_heap S) (4 * Z.of_nat i) (vint (Z.of_nat b)) = Some m' ->
  RepL m' S N lss (with_heur x (set_heap (hr x) i b)) lims lt.
Proof.
  intros m m' S N lss x lims i b HRep Hi Hb Hst.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_heur _ _ _ _ _ _ _ HRep) as Hok.
  pose proof (arr_store m m' (b_heap S) N i _ _ (a_heap _ _ _ _ _ _ _ HRep) Hi
                Hst) as A.
  destruct HRep. unpack. carry Hst Hnd.
  (* Every field is as before, but this array of the heuristic, which A gives. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* the array: the entry stored *)
    cbn [with_heur hr set_heap heap]. arr_tset.
  - (* the bounds *)
    apply heur_ok_heap.
    + assumption.
    + assumption.
Qed.

(* Storing the heap position o of atom a: s->hpos[a] = enc_pos o. *)
Lemma rep_store_hpos {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (a: nat) (o: option nat),
  RepL m S N lss x lims lt -> (a < N)%nat ->
  (forall (i: nat), o = Some i -> (i < N)%nat) ->
  Mem.store Mint32 m (b_hpos S) (4 * Z.of_nat a) (vint (enc_pos o)) = Some m' ->
  RepL m' S N lss (with_heur x (set_hpos (hr x) a o)) lims lt.
Proof.
  intros m m' S N lss x lims a o HRep Ha Ho Hst.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_heur _ _ _ _ _ _ _ HRep) as Hok.
  pose proof (arr_store m m' (b_hpos S) N a _ _ (a_hpos _ _ _ _ _ _ _ HRep) Ha
                Hst) as A.
  destruct HRep. unpack. carry Hst Hnd.
  (* Every field is as before, but this array of the heuristic, which A gives. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* the array: the entry stored *)
    cbn [with_heur hr set_hpos hpos]. arr_tset.
  - (* the bounds *)
    apply heur_ok_hpos.
    + assumption.
    + assumption.
Qed.

(* Storing the literal o to decide on of atom a: s->dlit[a] = enc_lit o. *)
Lemma rep_store_dlit {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (a: nat) (o: option Lit),
  RepL m S N lss x lims lt -> (a < N)%nat ->
  (forall (l: Lit), o = Some l -> (extract l < N)%nat) ->
  Mem.store Mint32 m (b_dlit S) (4 * Z.of_nat a) (vint (enc_lit o)) = Some m' ->
  RepL m' S N lss (with_heur x (set_dlit (hr x) a o)) lims lt.
Proof.
  intros m m' S N lss x lims a o HRep Ha Ho Hst.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_heur _ _ _ _ _ _ _ HRep) as Hok.
  pose proof (arr_store m m' (b_dlit S) N a _ _ (a_dlit _ _ _ _ _ _ _ HRep) Ha
                Hst) as A.
  destruct HRep. unpack. carry Hst Hnd.
  (* Every field is as before, but this array of the heuristic, which A gives. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* the array: the entry stored *)
    cbn [with_heur hr set_dlit dlit]. arr_tset.
  - (* the bounds *)
    apply heur_ok_dlit.
    + assumption.
    + assumption.
Qed.

(* Storing the bump v: s->inc = v. *)
Lemma rep_store_inc {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (v: Z),
  RepL m S N lss x lims lt -> (1 <= v < act_lim / 2)%Z ->
  Mem.store Mint32 m (b_s S) 248 (vint (v)) = Some m' ->
  RepL m' S N lss (with_heur x (set_inc (hr x) v)) lims lt.
Proof.
  intros m m' S N lss x lims v HRep Hv Hst.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_heur _ _ _ _ _ _ _ HRep) as Hok.
  pose proof (fld_store m m' (b_s S) 248 Mint32 _ _ (r_inc _ _ _ _ _ _ _ HRep) Hst) as F.
  cbn [Val.load_result] in F. destruct HRep. unpack. carry Hst Hnd.
  (* Every field but this one of the heuristic is as before. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* the bounds *)
    apply heur_ok_inc.
    + assumption.
    + assumption.
Qed.

(* Storing the size k of the heap: s->hsize = k. *)
Lemma rep_store_hsize {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (k: nat),
  RepL m S N lss x lims lt -> (k <= N)%nat ->
  Mem.store Mint32 m (b_s S) 272 (vint (Z.of_nat k)) = Some m' ->
  RepL m' S N lss (with_heur x (set_hsize (hr x) k)) lims lt.
Proof.
  intros m m' S N lss x lims k HRep Hk Hst.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_heur _ _ _ _ _ _ _ HRep) as Hok.
  pose proof (fld_store m m' (b_s S) 272 Mint32 _ _ (r_hsize _ _ _ _ _ _ _ HRep) Hst)
    as F.
  cbn [Val.load_result] in F. destruct HRep. unpack. carry Hst Hnd.
  (* Every field but this one of the heuristic is as before. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* the bounds *)
    apply heur_ok_hsize.
    + assumption.
    + assumption.
Qed.

(* The blocks the functions of the heuristic write: its arrays and the fields of s. *)
Definition HeurFrame (S: Shape): block -> Z -> Prop :=
  fun (b: block) (_: Z) =>
    b <> b_act S /\ b <> b_heap S /\ b <> b_hpos S /\ b <> b_dlit S /\ b <> b_s S.
