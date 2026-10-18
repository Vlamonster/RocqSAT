(* cut unassigns the trail from a position on, with an empty queue, drops the reason
   clauses of the literals from there on, and puts their atoms back into the heap (cut of
   core/Step.v). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Heur Propagate Analysis Step
  SolverStep.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep RepReasons RepHeur
  SetValue PopReasons Reinsert.
Import ListNotations.

(* What the parts of cut end in: the memory represents x' and the pool still holds t. *)
Definition CutPost (sh: Shape) (N: nat) (lss: list (list Lit)) (t: nat -> Z) (x': Ctx)
  (m': mem) (_: val): Prop :=
  RepL m' sh N lss x' /\ PoolArr m' sh t.

(* The statements of cut after its loop. *)
Definition cut_end: statement := drop_stmts 3 (fn_body f_cut).

(* The statements of cut that drop reason clauses. *)
Definition cut_drop: statement := then_stmt (drop_stmts 4 (drop_stmts 3 (fn_body f_cut))).

(* Dropping the reason clauses from n on, for n < nr y:

     {{ RepL y /\ n < nr y /\ Arr pool t }}
       s->rtop = s->rbeg[n];
       s->nr = n;                                                       (rep_store_pop)
     {{ RepL (y <| nr := n |>) /\ Arr pool t }}                                     *)
Lemma cut_drop_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (y: Ctx) (n: nat) (t: nat -> Z) (le: temp_env) (m: mem),
  RepL m sh N lss y -> (n < nr y)%nat -> PoolArr m sh t ->
  le ! _s = Some (sptr sh) -> le ! _n = Some (vnat n) ->
  Exec ge le m cut_drop (Returns f_cut (CutPost sh N lss t (y <| nr := n |>))).
Proof.
  intros sh N lss y n t le m HRep Hn Apool Hs Hn'.
  pose proof (r_n HRep) as HN.
  pose proof (r_nodup HRep) as Hnd.
  pose proof (r_nr_le HRep) as Hnrle.
  pose proof (r_nr HRep) as Fnr.
  pose proof (r_rtop HRep) as Frtop.
  pose proof (r_rbeg HRep) as Frbeg.
  pose proof (a_rbeg HRep) as (tb & Arbeg & Htb).
  unfold cut_drop, f_cut. cbn [fn_body drop_stmts then_stmt].
  (* s->rtop = s->rbeg[n]; *)
  run. rewrite (Htb n) by lia. eapply (exec_store_fld Frtop).
  - evl.
  - reflexivity.
  - ev.
  - intros m1 Hst1. normal.
    assert (Fnr1: IntAt m1 sh o_nr (nr y)).
    { apply (fld_store_other Fnr Hst1). right.
      unfold Mptr. cbv [Archi.ptr64]. cbn [size_chunk]. lia. }
    (* s->nr = n; *)
    eapply (exec_store_fld Fnr1).
    + evl.
    + reflexivity.
    + ev.
    + intros m2 Hst2. exists Vundef. split.
      * reflexivity.
      * split.
        -- apply (rep_store_pop m m1 m2 n HRep).
           ++ lia.
           ++ apply Hst1.
           ++ apply Hst2.
        -- assert (Apool1: PoolArr m1 sh t).
           { apply (arr_store_other Apool Hst1). neq Hnd. }
           apply (arr_store_other Apool1 Hst2). neq Hnd.
Qed.

(* The end of cut, once the values of x are v: the trail is cut at j with an empty queue,
   and the reason clauses of the literals from j on are dropped. Writing y for
   x <| vals := v |> <| tlen := j |> <| qhead := j |>:

     {{ RepL (x <| vals := v |>) /\ j <= tlen x /\ Arr pool t }}
       s->tlen = j;
       s->qhead = j;                                                     (rep_store_cut)
     {{ RepL y }}
       int n = pop_reasons(s, j);                                   (pop_reasons_correct)
     {{ RepL y /\ n = pop_reasons (rps x) j (nr x) }}
       if (n < s->nr) { ... }                                        (cut_drop_correct)
                                                                           (rep_nr_same)
     {{ RepL (y <| nr := n |>) /\ Arr pool t }}

   and y <| nr := n |> is cut x j without its heuristic and with the values v. *)
Lemma cut_end_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (j: nat) (v: Values) (t: nat -> Z) (le: temp_env) (m: mem),
  RepL m sh N lss (x <| vals := v |>) -> (j <= tlen x)%nat ->
  PoolArr m sh t ->
  le ! _s = Some (sptr sh) -> le ! _j = Some (vnat j) ->
  Exec ge le m cut_end (Returns f_cut (CutPost sh N lss t
    (x <| vals := v |> <| tlen := j |> <| qhead := j |>
       <| nr := pop_reasons (rps x) j (nr x) |>))).
Proof.
  intros sh N lss x j v t le m HRep Hj Apool Hs Hj'.
  pose proof (r_n HRep) as HN.
  pose proof (r_nodup HRep) as Hnd.
  pose proof (r_tlen_le HRep) as Htle. cbn [set_vals tlen] in Htle.
  pose proof (r_tlen HRep) as Ftlen.
  pose proof (r_qhead HRep) as Fqh.
  unfold cut_end, f_cut. cbn [fn_body drop_stmts].
  (* s->tlen = j; *)
  run. eapply (exec_store_fld Ftlen).
  - evl.
  - reflexivity.
  - ev.
  - intros m1 Hst1. normal.
    assert (Fqh1: IntAt m1 sh o_qhead (qhead x)).
    { apply (fld_store_other Fqh Hst1). right.
      unfold Mptr. cbv [Archi.ptr64]. cbn [size_chunk]. lia. }
    (* s->qhead = j; *)
    run. eapply (exec_store_fld Fqh1).
    + evl.
    + reflexivity.
    + ev.
    + intros m2 Hst2. normal.
      pose proof (rep_store_cut m m1 m2 j HRep Hj Hst1 Hst2) as HRep2.
      assert (Apool1: PoolArr m1 sh t).
      { apply (arr_store_other Apool Hst1). neq Hnd. }
      assert (Apool2: PoolArr m2 sh t).
      { apply (arr_store_other Apool1 Hst2). neq Hnd. }
      set (y := x <| vals := v |> <| tlen := j |> <| qhead := j |>) in HRep2.
      keep_mem m2.
      (* int n = pop_reasons(s, j); *)
      run.
      eapply (exec_call_triple pop_reasons_fun (pop_reasons_correct sh N lss y j)).
      * reflexivity.
      * evs.
      * split.
        -- apply HRep2.
        -- lia.
      * intros m3 v3 [-> ->]. normal.
        set (n := pop_reasons (rps y) j (nr y)).
        pose proof (pop_reasons_le (rps y) j (nr y)) as Hn.
        pose proof (r_nr HRep2) as Fnr.
        pose proof (r_nr_le HRep2) as Hnrle.
        (* if (n < s->nr) ... *)
        run.
        eapply exec_if_lt.
        -- ev.
        -- ev.
        -- reflexivity.
        -- lia.
        -- (* some are dropped *)
           intros Hlt. apply (cut_drop_correct sh N lss y n t).
           ++ assumption.
           ++ lia.
           ++ assumption.
           ++ tmp.
           ++ tmp.
        -- (* all are kept *)
           intros Hge. apply exec_skip. exists Vundef. split.
           ++ reflexivity.
           ++ split.
              ** apply (rep_nr_same m2 sh N lss y n HRep2). lia.
              ** assumption.
Qed.

(* The invariant of the loop of cut at q: the memory represents x with values v that,
   unassigned from j up to q, give those of the model, and the pool still holds t. *)
Record CutInv {sh: Shape} {N: nat} {lss: list (list Lit)} {x: Ctx}
  {j: nat} {t: nat -> Z} {q: nat} {le: temp_env} {m1: mem}: Prop := {
  cu_s: le ! _s = Some (sptr sh);
  cu_j: le ! _j = Some (vnat j);
  cu_q: le ! _q = Some (vnat q);
  cu_range: (j <= q <= tlen x)%nat;
  cu_vals: exists (v: Values),
    unset_range v (tr x) j (q - j) = unset_range (vals x) (tr x) j (tlen x - j) /\
    RepL m1 sh N lss (x <| vals := v |>);
  cu_pool: PoolArr m1 sh t;
}.
Arguments CutInv : clear implicits.

(* The loop of cut unassigns the literals of the trail from its end down to position j,
   and then cuts the trail at j with an empty queue, dropping the reason clauses from
   there on:

     {{ RepL m sh N lss x /\ j <= tlen x /\ Arr m pool t }}
       int q = s->tlen;
     {{ CutInv (tlen x) }}
       while (q > j) {
     {{ CutInv q /\ q > j }}
         set_value(s, s->tr[q - 1] >> 1, 0);                          (set_value_correct)
         q--;
     {{ CutInv (q - 1) }}                                             (unset_range_last)
       }
     {{ CutInv j: the values are unset_range (vals x) (tr x) j (tlen x - j) }}
       the cut;                                                         (cut_end_correct)
     {{ RepL (x <| vals := unset_range ... |> <| tlen := j |> <| qhead := j |>
          <| nr := pop_reasons (rps x) j (nr x) |>) /\ Arr pool t }}

   The loop ends: q decreases. *)
Lemma cut_loop_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (j: nat) (t: nat -> Z) (le: temp_env) (m: mem),
  RepL m sh N lss x -> (j <= tlen x)%nat -> PoolArr m sh t ->
  le ! _s = Some (sptr sh) -> le ! _j = Some (vnat j) ->
  Exec ge le m (drop_stmts 1 (fn_body f_cut)) (Returns f_cut (CutPost sh N lss t
    (x <| vals := unset_range (vals x) (tr x) j (tlen x - j) |>
       <| tlen := j |> <| qhead := j |> <| nr := pop_reasons (rps x) j (nr x) |>))).
Proof.
  intros sh N lss x j t le m HRep Hj Apool0 Hs0 Hj0.
  pose proof (r_n HRep) as HN.
  pose proof (r_tlen_le HRep) as Ht.
  unfold f_cut. cbn [fn_body fn_return drop_stmts].
  pose proof (r_tlen HRep) as Ftlen.
  (* int q = s->tlen; *)
  run. clear Ftlen. unfold Swhile.
  apply exec_loop with (R := Peano.lt) (I := CutInv sh N lss x j t)
    (a := tlen x).
  + apply lt_wf.
  + intros q le1 m1 HI. destruct HI as [Hs Hj' Hq Hjq (v & Hv & HRepq) Apool].
    pose proof (r_nodup HRepq) as Hnd.
    pose proof (r_tr_atoms HRepq) as Hatoms.
    pose proof (r_tr HRepq) as Ftr.
    pose proof (a_tr HRepq) as Atr.
    cbn [set_vals tr tlen] in Hatoms, Atr.
    apply exec_seq.
    (* if (q > j) ... else break; *)
    eapply exec_if_gt.
    * ev.
    * ev.
    * reflexivity.
    * lia.
    * (* q > j: unassign the literal at q - 1 *)
      intros Hgt.
      assert (Hsub: Int.sub (Int.repr (Z.of_nat q)) (Int.repr 1)
                    = Int.repr (Z.of_nat (q - 1))).
      { rewrite sub_repr. f_equal. lia. }
      assert (Hl: (extract (tget (tr x) (q - 1)) < N)%nat).
      { apply Hatoms. lia. }
      pose proof (key_small _ N Hl HN) as Hkey.
      assert (Hshr: Int.shr (Int.repr (key (tget (tr x) (q - 1)))) (Int.repr 1)
                    = Int.repr (Z.of_nat (extract (tget (tr x) (q - 1))))).
      { apply shr_key. lia. }
      (* set_value(s, s->tr[q - 1] >> 1, 0); *)
      run.
      eapply (exec_call_triple_none set_value_fun
                (set_value_correct sh N lss (x <| vals := v |>)
                   (extract (tget (tr x) (q - 1))) None)).
      -- reflexivity.
      -- unfold vint. rewrite <- Hshr. evs.
      -- split.
         ++ apply HRepq.
         ++ assumption.
      -- intros m2 v2 [HRep2 Hun2]. normal. transfer Hun2 Hnd. keep_mem m2.
         (* q--; and the loop goes on *)
         run. ints. apply loopk_next with (q - 1)%nat.
         ++ lia.
         ++ constructor.
            ** tmp.
            ** tmp.
            ** tmp.
            ** lia.
            ** exists (unset_value v (tget (tr x) (q - 1))). split.
               --- rewrite unset_range_last by lia. assumption.
               --- apply HRep2.
            ** assumption.
    * (* q = j: break; and the cut *)
      intros Hle. assert (Hqj: q = j) by lia. subst q.
      apply exec_break. abrupt. apply loopk_break. normal.
      rewrite Nat.sub_diag in Hv. simpl in Hv. rewrite <- Hv.
      apply (cut_end_correct sh N lss x j v t).
      -- assumption.
      -- assumption.
      -- assumption.
      -- tmp.
      -- tmp.
  + (* The invariant holds at the end of the trail. *)
    constructor.
    * tmp.
    * tmp.
    * tmp.
    * lia.
    * exists (vals x). split.
      -- reflexivity.
      -- destruct x. apply HRep.
    * assumption.
Qed.

(* cut first puts the atoms of the trail from j on back into the heap of the heuristic,
   then runs its loop:

     {{ RepL m sh N lss x /\ j <= tlen x /\ Arr m pool t }}
       reinsert(s, j, s->tlen);                                        (reinsert_correct)
     {{ RepL (x <| hr := reinsert (hr x) (tr x) N j (tlen x) (tlen x - j) |>) /\
        Arr pool t }}
       the loop and the cut;                                           (cut_loop_correct)
     {{ RepL (cut x j) /\ Arr pool t }}                                              *)
Lemma cut_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (j: nat) (t: nat -> Z),
  {{ m | RepL m sh N lss x /\ (j <= tlen x)%nat /\
    PoolArr m sh t }}
    f_cut(sptr sh, vnat j)
  {{ m', v | RepL m' sh N lss (cut x j) /\
             PoolArr m' sh t }}.
Proof.
  intros sh N lss x j t m (HRep & Hj & Apool).
  pose proof (r_nodup HRep) as Hnd.
  pose proof (r_tlen HRep) as Ftlen.
  pose proof (r_nvars HRep) as Hnv.
  unfold cut. rewrite Hnv.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_cut. cbn [fn_body fn_return].
    (* reinsert(s, j, s->tlen); *)
    run.
    eapply (exec_call_triple_none reinsert_fun
              (reinsert_correct sh N lss x j (tlen x))).
    + reflexivity.
    + evs.
    + split.
      * apply HRep.
      * lia.
    + intros m1 v1 [HRep1 Hun1]. normal. transfer Hun1 Hnd. keep_mem m1.
      (* the loop and the cut, on the context with the new heuristic *)
      apply (cut_loop_correct sh N lss
               (x <| hr := reinsert (hr x) (tr x) N j (tlen x) (tlen x - j) |>) j t).
      * assumption.
      * assumption.
      * assumption.
      * tmp.
      * tmp.
Qed.

Lemma cut_fun: FunAt _cut f_cut.
Proof. apply find_fun. reflexivity. Qed.
