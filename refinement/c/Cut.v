(* cut unassigns the trail from a position on, with an empty queue, and drops the reason
   clauses of the literals from there on (the values, length, queue and reason clauses
   of jump). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Heur Propagate Analysis Step
  CStep SolverStep.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep RepReasons RepHeur
  SetValue PopReasons Reinsert.
Import ListNotations.

(* Unassigning the last literal of a range first. *)
Lemma unset_range_last: forall (v: Values) (tr: Table Lit) (j q: nat), (j < q)%nat ->
  unset_range (unset_value v (tget tr (q - 1))) tr j (q - 1 - j)
  = unset_range v tr j (q - j).
Proof.
  intros v tr j q Hjq. replace (q - j)%nat with (Datatypes.S (q - 1 - j)) by lia. simpl.
  now replace (j + (q - 1 - j))%nat with (q - 1)%nat by lia.
Qed.

(* The statements of cut after its loop. *)
Definition cut_end: statement := drop_stmts 3 (fn_body f_cut).

(* The statements of cut that drop reason clauses. *)
Definition cut_drop: statement := then_stmt (drop_stmts 4 (drop_stmts 3 (fn_body f_cut))).

(* Dropping the reason clauses from n on, for n < nr y:

     {{ RepL y lt /\ n < nr y /\ Arr pool t }}
       s->rtop = s->rbeg[n];
       s->nr = n;                                                       (rep_store_pop)
     {{ RepL (set_nr y n) lt /\ Arr pool t }}                                         *)
Lemma cut_drop_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (y: Ctx) (lims: list nat) (n: nat) (t: nat -> Z) (le: temp_env) (m: mem),
  RepL m S N lss y lims lt -> (n < nr y)%nat -> Arr m (b_wpool S) (2 * npool S) t ->
  le ! _s = Some (sptr S) -> le ! _n = Some (vint (Z.of_nat n)) ->
  Exec ge le m cut_drop (Returns f_cut (fun (m': mem) (_: val) =>
    RepL m' S N lss (set_nr y n) lims lt /\ Arr m' (b_wpool S) (2 * npool S) t)).
Proof.
  intros S N lss y lims n t le m HRep Hn Apool Hs Hn'.
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_nr_le _ _ _ _ _ _ _ HRep) as Hnrle.
  pose proof (r_nr _ _ _ _ _ _ _ HRep) as Fnr.
  pose proof (r_rtop _ _ _ _ _ _ _ HRep) as Frtop.
  pose proof (r_rbeg _ _ _ _ _ _ _ HRep) as Frbeg.
  pose proof (a_rbeg _ _ _ _ _ _ _ HRep) as (tb & Arbeg & Htb).
  unfold cut_drop, f_cut. cbn [fn_body drop_stmts then_stmt].
  (* s->rtop = s->rbeg[n]; *)
  run. rewrite (Htb n) by lia. eapply exec_store.
  - evl.
  - ev.
  - reflexivity.
  - reflexivity.
  - fofs. bound.
  - fofs. cbn [cast_int_int].
    destruct (fld_storable m (b_s S) 204 Mint32 _
                (vint (Z.of_nat (reasons_size (rcl y) n))) Frtop) as [m1 Hst1].
    exists m1. split.
    + apply Hst1.
    + normal.
      assert (Fnr1: Fld m1 (b_s S) 232 Mint32 (vint (Z.of_nat (nr y)))).
      { apply (fld_store_other _ _ _ _ _ _ _ _ _ _ Fnr Hst1). right.
        unfold Mptr. cbv [Archi.ptr64]. cbn [size_chunk]. lia. }
      (* s->nr = n; *)
      eapply exec_store.
      * evl.
      * ev.
      * reflexivity.
      * reflexivity.
      * fofs. bound.
      * fofs. cbn [cast_int_int].
        destruct (fld_storable m1 (b_s S) 232 Mint32 _ (vint (Z.of_nat n)) Fnr1)
          as [m2 Hst2].
        exists m2. split.
        -- apply Hst2.
        -- exists Vundef. split.
           ++ reflexivity.
           ++ split.
              ** apply (rep_store_pop m m1 m2 S N lss y lims n HRep).
                 --- lia.
                 --- apply Hst1.
                 --- apply Hst2.
              ** assert (Apool1: Arr m1 (b_wpool S) (2 * npool S) t).
                 { apply (arr_store_other _ _ _ _ _ _ _ _ _ Apool Hst1). neq Hnd. }
                 apply (arr_store_other _ _ _ _ _ _ _ _ _ Apool1 Hst2). neq Hnd.
Qed.

(* The end of cut, once the values of x are v: the trail is cut at j with an empty queue,
   and the reason clauses of the literals from j on are dropped. Writing y for
   set_qhead (set_tlen (set_vals x v) j) j:

     {{ RepL (set_vals x v) lt /\ j <= tlen x /\ Arr pool t }}
       s->tlen = j;
       s->qhead = j;                                                     (rep_store_cut)
     {{ RepL y lt }}
       int n = pop_reasons(s, j);                                   (pop_reasons_correct)
     {{ RepL y lt /\ n = pop_reasons (rps x) j (nr x) }}
       if (n < s->nr) { ... }                                        (cut_drop_correct)
                                                                           (rep_nr_same)
     {{ RepL (set_nr y n) lt /\ Arr pool t }}

   and set_nr y n is the context after the jump. *)
Lemma cut_end_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (j: nat) (v: Values) (t: nat -> Z) (le: temp_env) (m: mem),
  RepL m S N lss (set_vals x v) lims lt -> (j <= tlen x)%nat ->
  Arr m (b_wpool S) (2 * npool S) t ->
  le ! _s = Some (sptr S) -> le ! _j = Some (vint (Z.of_nat j)) ->
  Exec ge le m cut_end (Returns f_cut (fun (m': mem) (_: val) =>
    RepL m' S N lss (jump x v j (cur x) (saved x) (dl x) (mrk x)) lims lt /\
    Arr m' (b_wpool S) (2 * npool S) t)).
Proof.
  intros S N lss x lims j v t le m HRep Hj Apool Hs Hj'.
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_tlen_le _ _ _ _ _ _ _ HRep) as Htle. cbn [set_vals tlen] in Htle.
  pose proof (r_tlen _ _ _ _ _ _ _ HRep) as Ftlen.
  pose proof (r_qhead _ _ _ _ _ _ _ HRep) as Fqh.
  unfold cut_end, f_cut. cbn [fn_body drop_stmts].
  (* s->tlen = j; *)
  run. eapply exec_store.
  - evl.
  - ev.
  - reflexivity.
  - reflexivity.
  - fofs. bound.
  - fofs. cbn [cast_int_int].
    destruct (fld_storable m (b_s S) 80 Mint32 _ (vint (Z.of_nat j)) Ftlen) as [m1 Hst1].
    exists m1. split.
    + apply Hst1.
    + normal.
      assert (Fqh1: Fld m1 (b_s S) 84 Mint32 (vint (Z.of_nat (qhead x)))).
      { apply (fld_store_other _ _ _ _ _ _ _ _ _ _ Fqh Hst1). right.
        unfold Mptr. cbv [Archi.ptr64]. cbn [size_chunk]. lia. }
      (* s->qhead = j; *)
      run. eapply exec_store.
      * evl.
      * ev.
      * reflexivity.
      * reflexivity.
      * fofs. bound.
      * fofs. cbn [cast_int_int].
        destruct (fld_storable m1 (b_s S) 84 Mint32 _ (vint (Z.of_nat j)) Fqh1)
          as [m2 Hst2].
        exists m2. split.
        -- apply Hst2.
        -- normal.
           pose proof (rep_store_cut m m1 m2 S N lss (set_vals x v) lims j HRep Hj Hst1
                         Hst2) as HRep2.
           assert (Apool1: Arr m1 (b_wpool S) (2 * npool S) t).
           { apply (arr_store_other _ _ _ _ _ _ _ _ _ Apool Hst1). neq Hnd. }
           assert (Apool2: Arr m2 (b_wpool S) (2 * npool S) t).
           { apply (arr_store_other _ _ _ _ _ _ _ _ _ Apool1 Hst2). neq Hnd. }
           set (y := set_qhead (set_tlen (set_vals x v) j) j) in HRep2.
           keep_mem m2.
           (* int n = pop_reasons(s, j); *)
           run. call pop_reasons_fun. eapply call_weaken.
           { apply (pop_reasons_correct (lt := lt) S N lss y lims j). split.
             - assumption.
             - lia. }
           intros m3 v3 [-> ->]. normal.
           set (n := pop_reasons (rps y) j (nr y)).
           pose proof (pop_reasons_le (rps y) j (nr y)) as Hn.
           pose proof (r_nr _ _ _ _ _ _ _ HRep2) as Fnr.
           pose proof (r_nr_le _ _ _ _ _ _ _ HRep2) as Hnrle.
           (* if (n < s->nr) ... *)
           run.
           eapply (exec_if_cmp _ _ _ Clt).
           ++ ev.
           ++ ev.
           ++ reflexivity.
           ++ reflexivity.
           ++ unfold Small. lia.
           ++ unfold Small. lia.
           ++ cbn [zcmp]. destruct (Nat.ltb_spec n (nr y)) as [Hlt | Hge].
              ** (* some are dropped *)
                 replace (Z.of_nat n <? Z.of_nat (nr y)) with true
                   by (symmetry; apply Z.ltb_lt; lia).
                 cbv beta iota. apply (cut_drop_correct S N lss y lims n t).
                 --- assumption.
                 --- assumption.
                 --- assumption.
                 --- tmp.
                 --- tmp.
              ** (* all are kept *)
                 replace (Z.of_nat n <? Z.of_nat (nr y)) with false
                   by (symmetry; apply Z.ltb_ge; lia).
                 cbv beta iota. apply exec_skip. exists Vundef. split.
                 --- reflexivity.
                 --- split.
                     +++ apply (rep_nr_same m2 S N lss y lims n HRep2). lia.
                     +++ assumption.
Qed.

(* The invariant of the loop of cut at q, for the memory m of the call with pool t: the
   temporaries hold s, j and q, q is between j and the end of the trail, and the memory
   represents x with values v that, unassigned from j up to q, give the values of the
   model. *)
Record CutInv (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx) (lims: list nat)
  (lt: list Lit) (j: nat) (t: nat -> Z) (q: nat) (le: temp_env) (m1: mem): Prop := {
  cu_s: le ! _s = Some (sptr S);
  cu_j: le ! _j = Some (vint (Z.of_nat j));
  cu_q: le ! _q = Some (vint (Z.of_nat q));
  cu_range: (j <= q <= tlen x)%nat;
  cu_vals: exists (v: Values),
    unset_range v (tr x) j (q - j) = unset_range (vals x) (tr x) j (tlen x - j) /\
    RepL m1 S N lss (set_vals x v) lims lt;
  cu_pool: Arr m1 (b_wpool S) (2 * npool S) t;
}.

(* The loop of cut unassigns the literals of the trail from its end down to position j,
   and then cuts the trail at j with an empty queue, dropping the reason clauses from
   there on:

     {{ RepL m S N lss x lims lt /\ j <= tlen x /\ Arr m pool t }}
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
     {{ RepL (jump x (unset_range ...) j (cur x) (saved x) (dl x) (mrk x)) lt /\
        Arr pool t }}

   The loop ends: q decreases. *)
Lemma cut_loop_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (j: nat) (t: nat -> Z) (le: temp_env) (m: mem),
  RepL m S N lss x lims lt -> (j <= tlen x)%nat -> Arr m (b_wpool S) (2 * npool S) t ->
  le ! _s = Some (sptr S) -> le ! _j = Some (vint (Z.of_nat j)) ->
  Exec ge le m (drop_stmts 1 (fn_body f_cut)) (Returns f_cut (fun (m': mem) (_: val) =>
    RepL m' S N lss
      (jump x (unset_range (vals x) (tr x) j (tlen x - j)) j (cur x) (saved x) (dl x)
         (mrk x)) lims lt /\
    Arr m' (b_wpool S) (2 * npool S) t)).
Proof.
  intros S N lss x lims j t le m HRep Hj Apool0 Hs0 Hj0.
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_tlen_le _ _ _ _ _ _ _ HRep) as Ht.
  unfold f_cut. cbn [fn_body fn_return drop_stmts].
  pose proof (r_tlen _ _ _ _ _ _ _ HRep) as Ftlen.
  (* int q = s->tlen; *)
  run. clear Ftlen. unfold Swhile.
  apply exec_loop with (R := Peano.lt) (I := CutInv S N lss x lims lt j t)
    (a := tlen x).
  + apply lt_wf.
  + intros q le1 m1 HI. destruct HI as [Hs Hj' Hq Hjq (v & Hv & HRepq) Apool].
    pose proof (r_nodup _ _ _ _ _ _ _ HRepq) as Hnd.
    pose proof (r_tr_atoms _ _ _ _ _ _ _ HRepq) as Hatoms.
    pose proof (r_tr _ _ _ _ _ _ _ HRepq) as Ftr.
    pose proof (a_tr _ _ _ _ _ _ _ HRepq) as Atr.
    cbn [set_vals tr tlen] in Hatoms, Atr.
    apply exec_seq.
    (* if (q > j) ... else break; *)
    eapply (exec_if_cmp _ _ _ Cgt).
    * ev.
    * ev.
    * reflexivity.
    * reflexivity.
    * unfold Small. lia.
    * unfold Small. lia.
    * destruct (Nat.eq_dec q j) as [-> | Hne].
      -- (* q = j: break; and the cut *)
         replace (zcmp Cgt (Z.of_nat j) (Z.of_nat j)) with false
           by (simpl; symmetry; apply Z.ltb_irrefl).
         apply exec_break. abrupt. apply loopk_break. normal.
         rewrite Nat.sub_diag in Hv. simpl in Hv. rewrite <- Hv.
         apply (cut_end_correct S N lss x lims j v t).
         ++ assumption.
         ++ assumption.
         ++ assumption.
         ++ tmp.
         ++ tmp.
      -- (* q > j: unassign the literal at q - 1 *)
         replace (zcmp Cgt (Z.of_nat q) (Z.of_nat j)) with true
           by (simpl; symmetry; apply Z.ltb_lt; lia).
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
         cbv beta iota. run. call set_value_fun. cbn [cast_int_int]. rewrite Hshr.
         eapply call_weaken.
         { apply (set_value_correct (lt := lt) S N lss (set_vals x v) lims _ None).
           split; assumption. }
         intros m2 v2 [HRep2 Hun2]. normal. transfer Hun2 Hnd. keep_mem m2.
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

     {{ RepL m S N lss x lims lt /\ j <= tlen x /\ Arr m pool t }}
       reinsert(s, j, s->tlen);                                        (reinsert_correct)
     {{ RepL (with_heur x (reinsert (hr x) (tr x) N j (tlen x) (tlen x - j))) lt /\
        Arr pool t }}
       the loop and the cut;                                           (cut_loop_correct)
     {{ RepL (jump_heur x (unset_range ...) j (cur x) (saved x) (dl x) (mrk x) (hr x)) lt
        /\ Arr pool t }}                                                               *)
Lemma cut_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (j: nat) (t: nat -> Z),
  {{ m | RepL m S N lss x lims lt /\ (j <= tlen x)%nat /\
    Arr m (b_wpool S) (2 * npool S) t }}
    f_cut(sptr S, vint (Z.of_nat j))
  {{ m', v | RepL m' S N lss
               (jump_heur x (unset_range (vals x) (tr x) j (tlen x - j)) j (cur x)
                  (saved x) (dl x) (mrk x) (hr x)) lims lt /\
             Arr m' (b_wpool S) (2 * npool S) t }}.
Proof.
  intros S N lss x lims j t m (HRep & Hj & Apool).
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_tlen _ _ _ _ _ _ _ HRep) as Ftlen.
  pose proof (r_nvars _ _ _ _ _ _ _ HRep) as Hnv.
  unfold jump_heur. rewrite Hnv.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_cut. cbn [fn_body fn_return].
    (* reinsert(s, j, s->tlen); *)
    run. call reinsert_fun. eapply call_weaken.
    { apply (reinsert_correct (lt := lt) S N lss x lims j (tlen x)). split.
      - assumption.
      - lia. }
    intros m1 v1 [HRep1 Hun1]. normal. transfer Hun1 Hnd. keep_mem m1.
    (* the loop and the cut, on the context with the new heuristic *)
    apply (cut_loop_correct S N lss
             (with_heur x (reinsert (hr x) (tr x) N j (tlen x) (tlen x - j))) lims j t).
    + assumption.
    + assumption.
    + assumption.
    + tmp.
    + tmp.
Qed.

Lemma cut_fun: exists (b: block),
  Genv.find_symbol ge _cut = Some b /\ Genv.find_funct_ptr ge b = Some (Internal f_cut).
Proof. apply find_fun. reflexivity. Qed.
