(* decay raises the bump after a conflict, rescaling when it gets too large (decay). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Heur Propagate Analysis Step.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep RepHeur Rescale.
Import ListNotations.

(* C divides an int from 0 by a positive one as Z.div. *)
Lemma sem_div_pos: forall (a b: Z) (m: mem), 0 <= a <= Int.max_signed ->
  0 < b <= Int.max_signed ->
  sem_div (vint a) Ctypesdefs.tint (vint b) Ctypesdefs.tint m = Some (vint (a / b)).
Proof.
  intros a b m Ha Hb. assert (Hmin: Int.min_signed = -2147483648) by reflexivity.
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

     {{ RepL m S N lss x lims lt }}
       int c = s->inc;
       c = c + c / 19;
     {{ RepL m S N lss x lims lt /\ c = inc h + inc h / 19 /\ 1 <= c < act_lim }}
       if (c >= ACT_LIM / 2)
         rescale(s, c);                                             (rescale_correct)
     {{ RepL m' S N lss (with_heur x (rescale h N c)) lims lt }}
       else
         s->inc = c;                                                  (rep_store_inc)
     {{ RepL m' S N lss (with_heur x (set_inc h c)) lims lt }}

   and both are with_heur x (decay h N); only the heuristic is written. *)
Lemma decay_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat),
  {{ m | RepL m S N lss x lims lt }}
    f_decay(sptr S)
  {{ m', v | RepL m' S N lss (with_heur x (decay (hr x) N)) lims lt /\
             Mem.unchanged_on (HeurFrame S) m m' }}.
Proof.
  intros S N lss x lims m HRep.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_inc _ _ _ _ _ _ _ HRep) as Finc.
  pose proof (ho_inc _ _ (r_heur _ _ _ _ _ _ _ HRep)) as Hinc.
  assert (Hlim: act_lim = 1073741824) by reflexivity.
  assert (Hhalf: (act_lim / 2 = 536870912)%Z) by reflexivity.
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
      eapply (exec_if_cmp _ _ _ Cge _ _ c (act_lim / 2)).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * cbn [zcmp]. unfold decay. cbv zeta. fold c.
        destruct (Z.leb_spec (act_lim / 2) c) as [Hge | Hlt].
        -- (* rescale(s, c); *)
           call rescale_fun. eapply call_weaken.
           { apply (rescale_correct (lt := lt) S N lss x lims c). split.
             - assumption.
             - lia. }
           intros m1 v1 [HRep1 Hun1]. exists Vundef. split.
           ++ reflexivity.
           ++ split.
              ** assumption.
              ** assumption.
        -- (* s->inc = c; *)
           eapply exec_store.
           ++ evl.
           ++ ev.
           ++ reflexivity.
           ++ reflexivity.
           ++ fofs. bound.
           ++ fofs. cbn [cast_int_int].
              destruct (fld_storable m (b_s S) 248 Mint32 _ (vint c) Finc) as [m1 Hst].
              exists m1. split.
              ** apply Hst.
              ** exists Vundef. split.
                 --- reflexivity.
                 --- split.
                     +++ apply (rep_store_inc m m1 S N lss x lims c HRep).
                         *** lia.
                         *** apply Hst.
                     +++ apply (store_unchanged _ m m m1 Mint32 (b_s S) 248 (vint c)).
                         *** apply Mem.unchanged_on_refl.
                         *** assumption.
                         *** intros i Hi. now apply Hi.
Qed.

Lemma decay_fun: exists (b: block),
  Genv.find_symbol ge _decay = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_decay).
Proof. apply find_fun. reflexivity. Qed.
