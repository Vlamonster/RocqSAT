(* check_room checks that the watch lists laid out by the caller fit in the pool, one
   after the other. *)
From Stdlib Require Import List.
Import ListNotations.

From compcert Require Import Coqlib.
From compcert Require Import Maps.
From compcert Require Import Integers.
From compcert Require Import AST.
From compcert Require Import Values.
From compcert Require Import Memory.
From compcert Require Import Globalenvs.
From compcert Require Import Ctypes.
From compcert Require Import Cop.
From compcert Require Import Clight.
From compcert Require Import ClightBigstep.

From RocqSAT.refinement Require Import Tactics.
From RocqSAT.refinement.c Require Import Arrays.
From RocqSAT.refinement.c Require Import Logic.
From RocqSAT.refinement.c Require Import Common.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Rep.

(* The first n watch lists, at offsets tw with capacities tc, lie within 0 .. bound. *)
Definition Fits (tw tc: nat -> Z) (n: nat) (bound: Z): Prop :=
  forall (k: nat), (k < n)%nat -> 0 <= tw k /\ 0 <= tc k /\ tw k + tc k <= bound.

(* The first n watch lists come one after the other. *)
Definition InOrder (tw tc: nat -> Z) (n: nat): Prop :=
  forall (k k': nat), (k < k' < n)%nat -> tw k + tc k <= tw k'.

(* The invariant of the loop of check_room at q, for the memory m of the call: the
   temporaries hold s, n = 2 N, off and q, the memory is still m, and the watch lists
   before q fit below off, which is within the pool, one after the other. *)
Record RoomInv {m: mem} {sh: Shape} {N: nat} {tw tc: nat -> Z} {off: Z} {q: nat}
  {le: temp_env} {m1: mem}: Prop := {
  ri_s: le ! _s = Some (sptr sh);
  ri_n: le ! _n = Some (vnat (2 * N));
  ri_off: le ! _off = Some (vint off);
  ri_q: le ! _q = Some (vnat q);
  ri_mem: m1 = m;
  ri_le: (q <= 2 * N)%nat;
  ri_off_range: 0 <= off <= Z.of_nat (npool sh);
  ri_fits: Fits tw tc q off;
  ri_order: InOrder tw tc q;
}.
Arguments RoomInv : clear implicits.

(* A watch list from off >= 0 on extends lists that fit below off, in order. *)
Lemma room_next: forall (tw tc: nat -> Z) (q: nat) (off: Z),
  0 <= off -> Fits tw tc q off -> InOrder tw tc q -> off <= tw q -> 0 <= tc q ->
  Fits tw tc (S q) (tw q + tc q) /\ InOrder tw tc (S q).
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
     {{ RoomInv m sh N tw tc 0 0 }}
       while (q < n) {
     {{ RoomInv m sh N tw tc off q /\ q < n }}
         int o = s->woff[q];
         int c = s->wcap[q];
         if (o < off) return 0;
         if (c < 0) return 0;
         if (c > s->npool - o) return 0;
     {{ result = 0 (rejected) }}
     {{ RoomInv m sh N tw tc off q /\ off <= o /\ 0 <= c /\ o + c <= npool }}
         off = o + c;
         q++;
     {{ RoomInv m sh N tw tc (o + c) (q + 1) }}            (room_next)
       }
     {{ RoomInv m sh N tw tc off q /\ q >= n }}
       return 1;
     {{ result = 1 /\ Fits tw tc (2 N) npool /\ InOrder tw tc (2 N) }}

   The loop ends: 2 N - q decreases. *)
Lemma check_room_correct: forall (sh: Shape) (N: nat) (tw tc: nat -> Z),
  {{ m | IntAt m sh o_nv N /\
         IntAt m sh o_npool (npool sh) /\
         PtrAt m sh o_woff (b_woff sh) /\
         PtrAt m sh o_wcap (b_wcap sh) /\
         Arr m (b_woff sh) (2 * N) tw /\ Arr m (b_wcap sh) (2 * N) tc /\
         (forall (k: nat), (k < 2 * N)%nat -> Small (tw k) /\ Small (tc k)) /\
         Z.of_nat N < atom_bound /\ Z.of_nat (npool sh) < small_bound }}
    f_check_room(sptr sh)
  {{ m', v | m' = m /\
             (v = vint 0 \/
              (v = vint 1 /\ Fits tw tc (2 * N) (Z.of_nat (npool sh)) /\
               InOrder tw tc (2 * N))) }}.
Proof.
  intros sh N tw tc m (Fnv & Fnp & Fwo & Fwc & Awo & Awc & Hsmall & HN & Hnp).
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
              exists (off: Z), RoomInv m sh N tw tc off q le m1)
      (a := 0%nat).
    + apply well_founded_ltof.
    + intros q le1 m1 [off HI]. destruct HI as [Hs Hn Hoff Hq -> Hqn Hoffr Hfits Horder].
      apply exec_seq.
      (* if (q < n) ... else break; *)
      branch.
      * (* q < n: int o = s->woff[q]; int c = s->wcap[q]; *)
        intros Hlt. assert (Hq_lt: (q < 2 * N)%nat) by lia.
        destruct (Hsmall q Hq_lt) as [Hsw Hsc].
        assert (Hadd: Int.add (Int.repr (Z.of_nat q)) (Int.repr 1)
                      = Int.repr (Z.of_nat (S q))).
        { rewrite add_repr by lia. f_equal. lia. }
        run.
        (* if (o < off) return 0; *)
        branch.
        -- intros _. return_int.
           split.
           ++ reflexivity.
           ++ now left.
        -- (* if (c < 0) return 0; *)
           intros Hlo. run.
           branch.
           ++ intros _. return_int.
              split.
              ** reflexivity.
              ** now left.
           ++ (* if (c > s->npool - o) return 0; *)
              intros Hlc. run.
              eapply exec_if_gt.
              ** ev.
              ** eapply eval_Ebinop.
                 --- ev.
                 --- ev.
                 --- cbn -[Int.sub Int.repr]. unfold vint. rewrite <- sub_repr.
                     reflexivity.
              ** reflexivity.
              ** lia.
              ** intros _. return_int.
                 split.
                 --- reflexivity.
                 --- now left.
              ** (* off = o + c; q++; and the list at q extends the invariant *)
                 intros Hlr.
                 assert (Hoc: Int.add (Int.repr (tw q)) (Int.repr (tc q))
                              = Int.repr (tw q + tc q)).
                 { rewrite add_repr by (lia). reflexivity. }
                 assert (Hoff0: 0 <= off) by lia.
                 destruct (room_next tw tc q off Hoff0 Hfits Horder Hlo Hlc)
                   as [Hfits' Horder'].
                 run. ints. apply loopk_next with (S q).
                 --- unfold ltof. lia.
                 --- exists (tw q + tc q). constructor.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
                     +++ reflexivity.
                     +++ lia.
                     +++ lia.
                     +++ assumption.
                     +++ assumption.
      * (* q >= n: break; return 1; every list fits, in order *)
        intros Hge. apply exec_break. abrupt. apply loopk_break. normal.
        return_int.
        split.
        -- reflexivity.
        -- right. splits.
           ++ reflexivity.
           ++ intros k Hk. assert (Hkq: (k < q)%nat) by lia.
              specialize (Hfits k Hkq). lia.
           ++ intros k k' Hk. apply Horder. lia.
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

Lemma check_room_fun: FunAt _check_room f_check_room.
Proof. apply find_fun. reflexivity. Qed.
