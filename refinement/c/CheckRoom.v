(* check_room checks that the watch lists laid out by the caller fit in the pool, one
   after the other. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep.
Import ListNotations.

(* The first n watch lists, at offsets tw with capacities tc, lie within 0 .. bound. *)
Definition Fits (tw tc: nat -> Z) (n: nat) (bound: Z): Prop :=
  forall (k: nat), (k < n)%nat -> 0 <= tw k /\ 0 <= tc k /\ tw k + tc k <= bound.

(* The first n watch lists come one after the other. *)
Definition InOrder (tw tc: nat -> Z) (n: nat): Prop :=
  forall (k k': nat), (k < k' < n)%nat -> tw k + tc k <= tw k'.

(* The invariant of the loop of check_room at q, for the memory m of the call: the
   temporaries hold s, n = 2 N, off and q, the memory is still m, and the watch lists
   before q fit below off, which is within the pool, one after the other. *)
Record RoomInv (m: mem) (S: Shape) (N: nat) (tw tc: nat -> Z) (off: Z) (q: nat)
  (le: temp_env) (m1: mem): Prop := {
  ri_s: le ! _s = Some (sptr S);
  ri_n: le ! _n = Some (vint (Z.of_nat (2 * N)));
  ri_off: le ! _off = Some (vint off);
  ri_q: le ! _q = Some (vint (Z.of_nat q));
  ri_mem: m1 = m;
  ri_le: (q <= 2 * N)%nat;
  ri_off_range: 0 <= off <= Z.of_nat (npool S);
  ri_fits: Fits tw tc q off;
  ri_order: InOrder tw tc q;
}.

(* A watch list from off >= 0 on extends lists that fit below off, in order. *)
Lemma room_next: forall (tw tc: nat -> Z) (q: nat) (off: Z),
  0 <= off -> Fits tw tc q off -> InOrder tw tc q -> off <= tw q -> 0 <= tc q ->
  Fits tw tc (Datatypes.S q) (tw q + tc q) /\ InOrder tw tc (Datatypes.S q).
Proof.
  intros tw tc q off Hoff Hfits Horder Hlo Hc. split.
  - intros k Hk. destruct (Nat.eq_dec k q) as [-> | Hne].
    + lia.
    + assert (Hkq: (k < q)%nat) by lia. specialize (Hfits k Hkq). lia.
  - intros k k' Hk. destruct (Nat.eq_dec k' q) as [-> | Hne].
    + assert (Hkq: (k < q)%nat) by lia. specialize (Hfits k Hkq). lia.
    + apply Horder. lia.
Qed.

(* check_room walks the watch lists in order, with off the end of the previous one, and
   rejects the layout at the first list that starts before off, has a negative capacity
   or does not fit in the pool. It stores nothing.

     {{ the fields nv, npool, woff, wcap and the arrays tw, tc are in m }}
       int n = 2 * s->nv;
       int off = 0;
       int q = 0;
     {{ RoomInv m S N tw tc 0 0 }}
       while (q < n) {
     {{ RoomInv m S N tw tc off q /\ q < n }}
         int o = s->woff[q];
         int c = s->wcap[q];
         if (o < off) return 0;
         if (c < 0) return 0;
         if (c > s->npool - o) return 0;
     {{ result = 0 (rejected) }}
     {{ RoomInv m S N tw tc off q /\ off <= o /\ 0 <= c /\ o + c <= npool }}
         off = o + c;
         q++;
     {{ RoomInv m S N tw tc (o + c) (q + 1) }}            (room_next)
       }
     {{ RoomInv m S N tw tc off q /\ q >= n }}
       return 1;
     {{ result = 1 /\ Fits tw tc (2 N) npool /\ InOrder tw tc (2 N) }}

   The loop ends: 2 N - q decreases. *)
Lemma check_room_correct: forall (S: Shape) (N: nat) (tw tc: nat -> Z),
  {{ m | Fld m (b_s S) 0 Mint32 (vint (Z.of_nat N)) /\
         Fld m (b_s S) 40 Mint32 (vint (Z.of_nat (npool S))) /\
         Fld m (b_s S) 48 Mptr (Vptr (b_woff S) Ptrofs.zero) /\
         Fld m (b_s S) 64 Mptr (Vptr (b_wcap S) Ptrofs.zero) /\
         Arr m (b_woff S) (2 * N) tw /\ Arr m (b_wcap S) (2 * N) tc /\
         (forall (k: nat), (k < 2 * N)%nat -> Small (tw k) /\ Small (tc k)) /\
         Z.of_nat N < 268435456 /\ Z.of_nat (npool S) < 1073741824 }}
    f_check_room(sptr S)
  {{ m', v | m' = m /\
             (v = vint 0 \/
              (v = vint 1 /\ Fits tw tc (2 * N) (Z.of_nat (npool S)) /\
               InOrder tw tc (2 * N))) }}.
Proof.
  intros S N tw tc m (Fnv & Fnp & Fwo & Fwc & Awo & Awc & Hsmall & HN & Hnp).
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_check_room. cbn [fn_body fn_return].
    assert (Hmul: Int.mul (Int.repr 2) (Int.repr (Z.of_nat N))
                  = Int.repr (Z.of_nat (2 * N))).
    { rewrite mul_repr. f_equal. lia. }
    (* int n = 2 * s->nv; int off = 0; int q = 0; *)
    run. ints. unfold Swhile.
    apply exec_loop with (R := ltof nat (fun (q: nat) => 2 * N - q)%nat)
      (I := fun (q: nat) (le: temp_env) (m1: mem) =>
              exists (off: Z), RoomInv m S N tw tc off q le m1)
      (a := 0%nat).
    + apply well_founded_ltof.
    + intros q le1 m1 [off HI]. destruct HI as [Hs Hn Hoff Hq -> Hqn Hoffr Hfits Horder].
      apply exec_seq.
      (* if (q < n) ... else break; *)
      eapply (exec_if_cmp _ _ _ Clt).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * destruct (Nat.lt_ge_cases q (2 * N)) as [Hlt | Hge].
        -- (* q < n: int o = s->woff[q]; int c = s->wcap[q]; *)
           replace (zcmp Clt (Z.of_nat q) (Z.of_nat (2 * N))) with true
             by (symmetry; cbn [zcmp]; apply Z.ltb_lt; lia).
           destruct (Hsmall q Hlt) as [Hsw Hsc].
           assert (Hadd: Int.add (Int.repr (Z.of_nat q)) (Int.repr 1)
                         = Int.repr (Z.of_nat (Datatypes.S q))).
           { rewrite add_repr by lia. f_equal. lia. }
           cbv beta iota. run.
           (* if (o < off) return 0; *)
           eapply (exec_if_cmp _ _ _ Clt _ _ (tw q) off).
           ++ ev.
           ++ ev.
           ++ reflexivity.
           ++ reflexivity.
           ++ assumption.
           ++ unfold Small. lia.
           ++ cbn [zcmp]. destruct (Z.ltb_spec (tw q) off) as [Hlo | Hlo].
              { cbv beta iota. eapply exec_return.
                - ev.
                - ret. exists (vint 0). split.
                  + apply result_int.
                  + split.
                    * reflexivity.
                    * now left. }
              (* if (c < 0) return 0; *)
              cbv beta iota. run.
              eapply (exec_if_cmp _ _ _ Clt _ _ (tc q) 0).
              ** ev.
              ** ev.
              ** reflexivity.
              ** reflexivity.
              ** assumption.
              ** unfold Small. lia.
              ** cbn [zcmp]. destruct (Z.ltb_spec (tc q) 0) as [Hlc | Hlc].
                 { cbv beta iota. eapply exec_return.
                   - ev.
                   - ret. exists (vint 0). split.
                     + apply result_int.
                     + split.
                       * reflexivity.
                       * now left. }
                 (* if (c > s->npool - o) return 0; *)
                 cbv beta iota. run.
                 eapply (exec_if_cmp _ _ _ Cgt _ _ (tc q) (Z.of_nat (npool S) - tw q)).
                 --- ev.
                 --- eapply eval_Ebinop.
                     +++ ev.
                     +++ ev.
                     +++ cbn -[Int.sub Int.repr]. unfold vint. rewrite <- sub_repr.
                         reflexivity.
                 --- reflexivity.
                 --- reflexivity.
                 --- assumption.
                 --- unfold Small in *. lia.
                 --- cbn [zcmp]. destruct (Z.ltb_spec (Z.of_nat (npool S) - tw q) (tc q))
                       as [Hlr | Hlr].
                     { cbv beta iota. eapply exec_return.
                       - ev.
                       - ret. exists (vint 0). split.
                         + apply result_int.
                         + split.
                           * reflexivity.
                           * now left. }
                     (* off = o + c; q++; and the list at q extends the invariant *)
                     assert (Hoc: Int.add (Int.repr (tw q)) (Int.repr (tc q))
                                  = Int.repr (tw q + tc q)).
                     { rewrite add_repr by (unfold Small in *; lia). reflexivity. }
                     assert (Hoff0: 0 <= off) by lia.
                     destruct (room_next tw tc q off Hoff0 Hfits Horder Hlo Hlc)
                       as [Hfits' Horder'].
                     cbv beta iota. run. ints. apply loopk_next with (Datatypes.S q).
                     +++ unfold ltof. lia.
                     +++ exists (tw q + tc q). constructor.
                         *** tmp.
                         *** tmp.
                         *** tmp.
                         *** tmp.
                         *** reflexivity.
                         *** lia.
                         *** lia.
                         *** assumption.
                         *** assumption.
        -- (* q >= n: break; return 1; every list fits, in order *)
           replace (zcmp Clt (Z.of_nat q) (Z.of_nat (2 * N))) with false
             by (symmetry; cbn [zcmp]; apply Z.ltb_ge; lia).
           cbv beta iota. apply exec_break. abrupt. apply loopk_break. normal.
           eapply exec_return.
           ++ ev.
           ++ exists (vint 1). split.
              ** apply result_int.
              ** split.
                 --- reflexivity.
                 --- right. split.
                     +++ reflexivity.
                     +++ split.
                         *** intros k Hk. assert (Hkq: (k < q)%nat) by lia.
                             specialize (Hfits k Hkq). lia.
                         *** intros k k' Hk. apply Horder. lia.
    + (* The invariant holds at q = 0, with off = 0. *)
      exists 0. constructor.
      * tmp.
      * tmp.
      * tmp.
      * tmp.
      * reflexivity.
      * lia.
      * lia.
      * intros k Hk. lia.
      * intros k k' Hk. lia.
Qed.

Lemma check_room_fun: exists (b: block),
  Genv.find_symbol ge _check_room = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_check_room).
Proof. apply find_fun. reflexivity. Qed.
