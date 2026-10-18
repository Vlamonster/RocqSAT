(* decay raises the bump after a conflict, rescaling when it gets too large (decay). *)
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

From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import Heur.
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement Require Import Analysis.
From RocqSAT.refinement Require Import Step.
From RocqSAT.refinement.c Require Import Arrays.
From RocqSAT.refinement.c Require Import Logic.
From RocqSAT.refinement.c Require Import Common.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Rep.
From RocqSAT.refinement.c Require Import RepHeur.
From RocqSAT.refinement.c Require Import Rescale.

(* C divides a nonnegative int by a positive one as Z.div. *)
Lemma sem_div_pos: forall (a b: Z) (m: mem), 0 <= a <= Int.max_signed ->
  0 < b <= Int.max_signed ->
  sem_div (vint a) Ctypesdefs.tint (vint b) Ctypesdefs.tint m = Some (vint (a / b)).
Proof.
  intros a b m Ha Hb. assert (Hmin: Int.min_signed = - int_bound) by reflexivity.
  unfold sem_div, sem_binarith, sem_cast, vint. simpl. cbv [Archi.ptr64]. simpl.
  rewrite !Int.eq_signed, Int.signed_zero, !Int.signed_repr by lia.
  destruct (zeq b 0) as [Hb0 | Hb0].
  - lia.
  - destruct (zeq a Int.min_signed) as [Ha0 | Ha0].
    + lia.
    + cbn [orb andb]. unfold Int.divs. rewrite !Int.signed_repr by lia.
      rewrite Z.quot_div_nonneg by lia. reflexivity.
Qed.

(* decay raises the bump by a 19th; at act_lim / 2 or more, it rescales with the raised
   bump instead of storing it. Writing c for inc h + inc h / 19, with h = hr x:

     {{ RepL m sh N lss x }}
       int c = s->inc;
       c = c + c / 19;
     {{ RepL m sh N lss x /\ c = inc h + inc h / 19 /\ 1 <= c < act_lim }}
       if (c >= ACT_LIM / 2)
         rescale(s, c);                                             (rescale_correct)
     {{ RepL m' sh N lss (x <| hr := rescale h N c |>) }}
       else
         s->inc = c;                                                  (rep_store_inc)
     {{ RepL m' sh N lss (x <| hr := set_inc h c |>) }}

   and both are x <| hr := decay h N |>; only the heuristic is written. *)
Lemma decay_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx),
  {{ m | RepL m sh N lss x }}
    f_decay(sptr sh)
  {{ m', v | HeurPost sh N lss x m (decay (hr x) N) m' }}.
Proof.
  intros sh N lss x m HRep.
  pose proof (r_nodup HRep) as Hnd.
  pose proof (r_inc HRep) as Finc.
  pose proof (ho_inc (r_heur HRep)) as Hinc.
  assert (Hlim: act_lim = small_bound) by reflexivity.
  assert (Hhalf: (act_lim / 2 = key_bound)%Z) by reflexivity.
  set (c := (inc (hr x) + inc (hr x) / 19)%Z).
  (* The raised bump stays below act_lim. *)
  assert (Hc: (1 <= c < act_lim)%Z).
  { unfold c. pose proof (Z.mul_div_le (inc (hr x)) 19) as Hle.
    pose proof (Z.div_pos (inc (hr x)) 19) as Hpos. lia. }
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_decay. cbn [fn_body fn_return].
    (* int c = s->inc; c = c + c / 19; *)
    run. eapply exec_set.
    + eapply eval_Ebinop.
      * ev.
      * eapply eval_Ebinop.
        -- ev.
        -- ev.
        -- apply sem_div_pos.
           ++ assert (Int.max_signed = 2147483647) by reflexivity. lia.
           ++ assert (Int.max_signed = 2147483647) by reflexivity. lia.
      * reflexivity.
    + cbn [cast_int_int]. rewrite add_repr. fold c. normal.
      (* if (c >= ACT_LIM / 2) ... *)
      unfold decay. cbv zeta. fold c.
      eapply (exec_if_ge c (act_lim / 2)).
      * ev.
      * ev.
      * reflexivity.
      * lia.
      * (* rescale(s, c); *)
        intros Hge.
        replace (act_lim / 2 <=? c) with true by (symmetry; now apply Z.leb_le).
        eapply (exec_call_triple_none rescale_fun (rescale_correct sh N lss x c)).
        -- reflexivity.
        -- evs.
        -- split.
           ++ apply HRep.
           ++ lia.
        -- intros m1 v1 [HRep1 Hun1]. exists Vundef. split.
           ++ reflexivity.
           ++ split.
              ** assumption.
              ** assumption.
      * (* s->inc = c; *)
        intros Hlt.
        replace (act_lim / 2 <=? c) with false by (symmetry; now apply Z.leb_gt).
        eapply (exec_store_fld Finc).
        -- evl.
        -- reflexivity.
        -- ev.
        -- intros m1 Hst. exists Vundef. split.
           ++ reflexivity.
           ++ split.
              ** apply (rep_store_inc m m1 c HRep).
                 --- lia.
                 --- apply Hst.
              ** apply (store_unchanged _ m m m1 Mint32 (b_s sh) o_inc (vint c)).
                 --- apply Mem.unchanged_on_refl.
                 --- assumption.
                 --- intros i Hi. now apply Hi.
Qed.

Lemma decay_fun: FunAt _decay f_decay.
Proof. apply find_fun. reflexivity. Qed.
