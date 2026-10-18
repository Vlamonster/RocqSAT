(* rescale divides the activities and the bump by 2^20, keeping the bump at least 1
   (rescale). *)
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
From RocqSAT.refinement Require Import Ctx.
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement Require Import Step.
From RocqSAT.refinement.c Require Import Arrays.
From RocqSAT.refinement.c Require Import Logic.
From RocqSAT.refinement.c Require Import Common.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Rep.
From RocqSAT.refinement.c Require Import RepHeur.

(* The heuristic h with the activities t. *)
Definition with_acts (h: Heur) (t: Table Z): Heur :=
  mkHeur t (inc h) (heap h) (hpos h) (hsize h) (dlit h).

(* The heuristic with its own activities is itself. *)
Lemma with_acts_act: forall (h: Heur), with_acts h (act h) = h.
Proof. intros h. now destruct h. Qed.

(* Shifting an activity (0 <= z < act_lim) right by 20 bits divides it by act_shift. *)
Lemma shr_act: forall (z: Z), 0 <= z < act_lim ->
  Int.shr (Int.repr z) (Int.repr 20) = Int.repr (z / act_shift).
Proof.
  intros z Hz. unfold act_lim in Hz. change (2 ^ 30) with small_bound in Hz.
  assert (Hint: Int.max_signed = 2147483647) by reflexivity.
  assert (Hmin: Int.min_signed = - int_bound) by reflexivity.
  unfold Int.shr. rewrite Int.signed_repr by lia.
  rewrite Int.unsigned_repr by (unfold Int.max_unsigned; simpl; lia).
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* Dividing by act_shift keeps an activity within its bounds, and makes it a bump below
   act_lim / 2. *)
Lemma shift_bounds: forall (z: Z), 0 <= z < act_lim ->
  0 <= z / act_shift < act_lim / 2.
Proof.
  intros z Hz. unfold act_lim, act_shift in *.
  change (2 ^ 30) with small_bound in *. change (2 ^ 20) with 1048576.
  change (small_bound / 2) with key_bound. split.
  - apply Z.div_pos.
    + lia.
    + lia.
  - apply Z.div_lt_upper_bound.
    + lia.
    + lia.
Qed.

(* The invariant of the loop of rescale at atom a, for the memory m of the call: the
   temporaries hold s, c and a, a is at most N, the memory m1 represents x with
   activities t that, shifted from a on, give the activities of the model (the loop
   follows the recursion of shift_acts), and m1 is m but for the heuristic. *)
Record RescaleInv {m: mem} {sh: Shape} {N: nat} {lss: list (list Lit)} {x: Ctx}
  {c: Z} {a: nat} {le: temp_env} {m1: mem}: Prop := {
  rs_s: le ! _s = Some (sptr sh);
  rs_c: le ! _c = Some (vint c);
  rs_a: le ! _a = Some (vnat a);
  rs_le: (a <= N)%nat;
  rs_acts: exists (t: Table Z),
    shift_acts t a (N - a) = shift_acts (act (hr x)) 0 N /\
    RepL m1 sh N lss (x <| hr := with_acts (hr x) t |>);
  rs_frame: Mem.unchanged_on (HeurFrame sh) m m1;
}.
Arguments RescaleInv : clear implicits.

(* The arrays of the heuristic and the fields of s are outside the frame of the
   heuristic's functions. *)
Lemma act_not_frame: forall (sh: Shape) (i: Z), ~ HeurFrame sh (b_act sh) i.
Proof. intros sh i [Hne _]. now apply Hne. Qed.

Lemma heap_not_frame: forall (sh: Shape) (i: Z), ~ HeurFrame sh (b_heap sh) i.
Proof. intros sh i (_ & Hne & _). now apply Hne. Qed.

Lemma hpos_not_frame: forall (sh: Shape) (i: Z), ~ HeurFrame sh (b_hpos sh) i.
Proof. intros sh i (_ & _ & Hne & _). now apply Hne. Qed.

Lemma s_not_frame: forall (sh: Shape) (i: Z), ~ HeurFrame sh (b_s sh) i.
Proof. intros sh i (_ & _ & _ & _ & Hne). now apply Hne. Qed.

(* rescale divides the activities of the atoms a = 0 .. N - 1 by act_shift, one after
   the other, and then stores the bump c / act_shift, at least 1. Only the heuristic
   changes:

     {{ RepL m sh N lss x /\ 0 <= c < act_lim }}
       int a = 0;
     {{ RescaleInv 0: activities act (hr x) }}
       while (a < s->nv) {
     {{ RescaleInv a: activities t /\ a < N }}
         s->act[a] = s->act[a] >> 20;                         (shr_act, rep_store_act)
         a++;
     {{ RescaleInv (a + 1): activities tset t a (tget t a / act_shift) }}
       }
     {{ RescaleInv N: activities shift_acts (act (hr x)) 0 N }}
       c = c >> 20;
       if (c < 1) c = 1;
     {{ c = Z.max 1 (c / act_shift) }}
       s->inc = c;                                                       (rep_store_inc)
     {{ RepL (x <| hr := rescale (hr x) N c |>) /\ only the heuristic changed }}

   The loop ends: N - a decreases. *)
Lemma rescale_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (c: Z),
  {{ m | RepL m sh N lss x /\ (0 <= c < act_lim)%Z }}
    f_rescale(sptr sh, vint c)
  {{ m', v | HeurPost sh N lss x m (rescale (hr x) N c) m' }}.
Proof.
  intros sh N lss x c m [HRep Hc]. pose proof (r_n HRep) as HN.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_rescale. cbn [fn_body fn_return].
    (* int a = 0; *)
    run.
    apply exec_loop with (R := ltof nat (fun (a: nat) => N - a)%nat)
      (I := RescaleInv m sh N lss x c) (a := 0%nat).
    + apply well_founded_ltof.
    + intros a le1 m1 HI. destruct HI as [Hs Hc' Ha Hale (t & Ht & HRep1) Hun1].
      pose proof (r_nodup HRep1) as Hnd.
      pose proof (r_nv HRep1) as Fnv.
      apply exec_seq.
      (* if (a < s->nv) ... else break; *)
      run. eapply exec_if_lt.
      * ev.
      * ev.
      * reflexivity.
      * lia.
      * (* a < N: shift the activity of a *)
        intros Hlt_z. assert (Hlt: (a < N)%nat) by lia.
        pose proof (r_act HRep1) as Fact.
        pose proof (a_act HRep1) as Aact.
        cbn [set_hr hr with_acts act] in Aact.
        pose proof (ho_act (r_heur HRep1) a Hlt) as Hta.
        cbn [set_hr hr with_acts act] in Hta.
        pose proof (shr_act _ Hta) as Hshr.
        pose proof (shift_bounds _ Hta) as Hdiv.
        pose proof half_lim as Hhalf.
        assert (Hadd: Int.add (Int.repr (Z.of_nat a)) (Int.repr 1)
                      = Int.repr (Z.of_nat (S a))).
        { rewrite add_repr. f_equal. lia. }
        (* s->act[a] = s->act[a] >> 20; *)
        apply exec_skip. normal. run. eapply (exec_store_arr Aact Hlt).
        -- evl.
        -- ofs.
        -- reflexivity.
        -- ev.
        -- intros m2 Hst2. rewrite Hshr in Hst2. normal.
           (* a++; and the loop goes on *)
           run. ints. apply loopk_next with (S a).
           ++ unfold ltof. lia.
           ++ constructor.
              ** tmp.
              ** tmp.
              ** tmp.
              ** lia.
              ** exists (tset t a (tget t a / act_shift)). split.
                 --- rewrite <- Ht. replace (N - a)%nat
                       with (S (N - S a)) by lia.
                     reflexivity.
                 --- apply (rep_store_act m1 m2 a _ HRep1 Hlt).
                     +++ lia.
                     +++ apply Hst2.
              ** apply (store_unchanged _ m m1 m2 Mint32 (b_act sh)
                          (4 * Z.of_nat a) (vint (tget t a / act_shift))).
                 --- assumption.
                 --- assumption.
                 --- apply act_not_frame.
      * (* a = N: break; the activities are those of the model *)
        intros Hge.
        replace a with N in Ht by lia. rewrite Nat.sub_diag in Ht.
        cbn [shift_acts] in Ht.
        apply exec_break. abrupt. apply loopk_break. normal.
        pose proof (shr_act c Hc) as Hshr.
        pose proof (shift_bounds c Hc) as Hdiv.
        (* c = c >> 20; *)
        run. rewrite Hshr.
        (* if (c < 1) c = 1; gives c = Z.max 1 (c / act_shift) *)
        apply exec_weaken with (Q := fun (le2: temp_env) (m2: mem) (out: outcome) =>
          out = Out_normal /\ m2 = m1 /\ le2 ! _s = Some (sptr sh) /\
          le2 ! _c = Some (vint (Z.max 1 (c / act_shift)))).
        -- eapply exec_if_lt.
           ++ ev.
           ++ ev.
           ++ reflexivity.
           ++ change (act_lim / 2) with key_bound in Hdiv. lia.
           ++ (* below 1: c = 1; *)
              intros Hlt1. run. split.
              ** reflexivity.
              ** split.
                 --- reflexivity.
                 --- split.
                     +++ tmp.
                     +++ rewrite Z.max_l by lia. tmp.
           ++ (* at least 1 *)
              intros Hge1. apply exec_skip. split.
              ** reflexivity.
              ** split.
                 --- reflexivity.
                 --- split.
                     +++ tmp.
                     +++ rewrite Z.max_r by lia. tmp.
        -- intros le2 m2 out (-> & -> & Hs2 & Hc2). apply seqk_normal.
           pose proof (r_inc HRep1) as Finc.
           (* s->inc = c; *)
           eapply (exec_store_fld Finc).
           ++ evl.
           ++ reflexivity.
           ++ ev.
           ++ intros m3 Hst3. exists Vundef. split.
              ** reflexivity.
              ** split.
                 --- unfold rescale. rewrite <- Ht.
                     apply (rep_store_inc m1 m3 _ HRep1).
                     +++ change (act_lim / 2) with key_bound in *. lia.
                     +++ apply Hst3.
                 --- apply (store_unchanged _ m m1 m3 Mint32 (b_s sh) o_inc
                              (vint (Z.max 1 (c / act_shift)))).
                     +++ assumption.
                     +++ assumption.
                     +++ apply s_not_frame.
    + (* The invariant holds at a = 0, with the activities of x. *)
      constructor.
      * tmp.
      * tmp.
      * tmp.
      * lia.
      * exists (act (hr x)). split.
        -- rewrite Nat.sub_0_r. reflexivity.
        -- rewrite with_acts_act, set_hr_same. assumption.
      * apply Mem.unchanged_on_refl.
Qed.

Lemma rescale_fun: FunAt _rescale f_rescale.
Proof. apply find_fun. reflexivity. Qed.
