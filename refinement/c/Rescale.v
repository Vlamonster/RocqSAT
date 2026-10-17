(* rescale divides the activities and the bump by 2^20, keeping the bump at least 1
   (rescale). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Heur Propagate Step.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep RepHeur.
Import ListNotations.

(* The heuristic h with the activities t. *)
Definition with_acts (h: Heur) (t: Table Z): Heur :=
  mkHeur t (inc h) (heap h) (hpos h) (hsize h) (dlit h).

(* The context x with its own heuristic is x, and the heuristic h with its own
   activities is h. *)
Lemma with_heur_hr: forall (x: Ctx), with_heur x (hr x) = x.
Proof. intros x. now destruct x. Qed.

Lemma with_acts_act: forall (h: Heur), with_acts h (act h) = h.
Proof. intros h. now destruct h. Qed.

(* Shifting a value from 0 below 2^30 right by 20 bits divides it by act_shift. *)
Lemma shr_act: forall (z: Z), 0 <= z < act_lim ->
  Int.shr (Int.repr z) (Int.repr 20) = Int.repr (z / act_shift).
Proof.
  intros z Hz. unfold act_lim in Hz. change (2 ^ 30) with 1073741824 in Hz.
  assert (Hint: Int.max_signed = 2147483647) by reflexivity.
  assert (Hmin: Int.min_signed = -2147483648) by reflexivity.
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
  change (2 ^ 30) with 1073741824 in *. change (2 ^ 20) with 1048576.
  change (1073741824 / 2) with 536870912. split.
  - apply Z.div_pos.
    + lia.
    + lia.
  - apply Z.div_lt_upper_bound.
    + lia.
    + lia.
Qed.

(* The bump below act_lim / 2 is also below act_lim. *)
Lemma half_lim: act_lim / 2 < act_lim.
Proof. reflexivity. Qed.

(* The invariant of the loop of rescale at atom a, for the memory m of the call: the
   temporaries hold s, c and a, a is at most N, the memory m1 represents x with
   activities t that, shifted from a on, give the activities of the model (the loop
   follows the recursion of shift_acts), and m1 is m but for the heuristic. *)
Record RescaleInv (m: mem) (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (lt: list Lit) (c: Z) (a: nat) (le: temp_env) (m1: mem): Prop := {
  rs_s: le ! _s = Some (sptr S);
  rs_c: le ! _c = Some (vint c);
  rs_a: le ! _a = Some (vint (Z.of_nat a));
  rs_le: (a <= N)%nat;
  rs_acts: exists (t: Table Z),
    shift_acts t a (N - a) = shift_acts (act (hr x)) 0 N /\
    RepL m1 S N lss (with_heur x (with_acts (hr x) t)) lims lt;
  rs_frame: Mem.unchanged_on (HeurFrame S) m m1;
}.

(* The arrays of the heuristic and the fields of s are outside the frame of the
   heuristic's functions. *)
Lemma act_not_frame: forall (S: Shape) (i: Z), ~ HeurFrame S (b_act S) i.
Proof. intros S i [Hne _]. now apply Hne. Qed.

Lemma heap_not_frame: forall (S: Shape) (i: Z), ~ HeurFrame S (b_heap S) i.
Proof. intros S i (_ & Hne & _). now apply Hne. Qed.

Lemma hpos_not_frame: forall (S: Shape) (i: Z), ~ HeurFrame S (b_hpos S) i.
Proof. intros S i (_ & _ & Hne & _). now apply Hne. Qed.

Lemma dlit_not_frame: forall (S: Shape) (i: Z), ~ HeurFrame S (b_dlit S) i.
Proof. intros S i (_ & _ & _ & Hne & _). now apply Hne. Qed.

Lemma s_not_frame: forall (S: Shape) (i: Z), ~ HeurFrame S (b_s S) i.
Proof. intros S i (_ & _ & _ & _ & Hne). now apply Hne. Qed.

(* rescale divides the activities of the atoms a = 0 .. N - 1 by act_shift, one after
   the other, and then stores the bump c / act_shift, at least 1. Only the heuristic
   changes:

     {{ RepL m S N lss x lims lt /\ 0 <= c < act_lim }}
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
     {{ RepL (with_heur x (rescale (hr x) N c)) /\ only the heuristic changed }}

   The loop ends: N - a decreases. *)
Lemma rescale_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (c: Z),
  {{ m | RepL m S N lss x lims lt /\ (0 <= c < act_lim)%Z }}
    f_rescale(sptr S, vint c)
  {{ m', v | RepL m' S N lss (with_heur x (rescale (hr x) N c)) lims lt /\
             Mem.unchanged_on (HeurFrame S) m m' }}.
Proof.
  intros S N lss x lims c m [HRep Hc]. pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_rescale. cbn [fn_body fn_return].
    (* int a = 0; *)
    run.
    apply exec_loop with (R := ltof nat (fun (a: nat) => N - a)%nat)
      (I := RescaleInv m S N lss x lims lt c) (a := 0%nat).
    + apply well_founded_ltof.
    + intros a le1 m1 HI. destruct HI as [Hs Hc' Ha Hale (t & Ht & HRep1) Hun1].
      pose proof (r_nodup _ _ _ _ _ _ _ HRep1) as Hnd.
      pose proof (r_nv _ _ _ _ _ _ _ HRep1) as Fnv.
      apply exec_seq.
      (* if (a < s->nv) ... else break; *)
      run. eapply (exec_if_cmp _ _ _ Clt).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * destruct (Nat.lt_ge_cases a N) as [Hlt | Hge].
        -- (* a < N: shift the activity of a *)
           replace (zcmp Clt (Z.of_nat a) (Z.of_nat N)) with true
             by (symmetry; cbn [zcmp]; apply Z.ltb_lt; lia).
           pose proof (r_act _ _ _ _ _ _ _ HRep1) as Fact.
           pose proof (a_act _ _ _ _ _ _ _ HRep1) as Aact.
           cbn [with_heur hr with_acts act] in Aact.
           pose proof (ho_act _ _ (r_heur _ _ _ _ _ _ _ HRep1) a Hlt) as Hta.
           cbn [with_heur hr with_acts act] in Hta.
           pose proof (shr_act _ Hta) as Hshr.
           pose proof (shift_bounds _ Hta) as Hdiv.
           pose proof half_lim as Hhalf.
           assert (Hadd: Int.add (Int.repr (Z.of_nat a)) (Int.repr 1)
                         = Int.repr (Z.of_nat (Datatypes.S a))).
           { rewrite add_repr. f_equal. lia. }
           (* s->act[a] = s->act[a] >> 20; *)
           cbv beta iota. apply exec_skip. normal. run. eapply exec_store.
           ++ evl.
           ++ ev.
           ++ reflexivity.
           ++ reflexivity.
           ++ ofs. bound.
           ++ ofs. cbn [cast_int_int].
              destruct (arr_storable m1 (b_act S) N a _ (tget t a / act_shift) Aact Hlt)
                as [m2 Hst2].
              exists m2. split.
              ** apply Hst2.
              ** normal.
                 (* a++; and the loop goes on *)
                 run. ints. apply loopk_next with (Datatypes.S a).
                 --- unfold ltof. lia.
                 --- constructor.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
                     +++ lia.
                     +++ exists (tset t a (tget t a / act_shift)). split.
                         *** rewrite <- Ht. replace (N - a)%nat
                               with (Datatypes.S (N - Datatypes.S a)) by lia.
                             reflexivity.
                         *** apply (rep_store_act m1 m2 S N lss _ lims a _ HRep1 Hlt).
                             ---- lia.
                             ---- apply Hst2.
                     +++ apply (store_unchanged _ m m1 m2 Mint32 (b_act S)
                                  (4 * Z.of_nat a) (vint (tget t a / act_shift))).
                         *** assumption.
                         *** assumption.
                         *** apply act_not_frame.
        -- (* a = N: break; the activities are those of the model *)
           replace (zcmp Clt (Z.of_nat a) (Z.of_nat N)) with false
             by (symmetry; cbn [zcmp]; apply Z.ltb_ge; lia).
           replace a with N in Ht by lia. rewrite Nat.sub_diag in Ht.
           cbn [shift_acts] in Ht.
           cbv beta iota. apply exec_break. abrupt. apply loopk_break. normal.
           pose proof (shr_act c Hc) as Hshr.
           pose proof (shift_bounds c Hc) as Hdiv.
           (* c = c >> 20; *)
           run. rewrite Hshr.
           (* if (c < 1) c = 1; gives c = Z.max 1 (c / act_shift) *)
           apply exec_weaken with (Q := fun (le2: temp_env) (m2: mem) (out: outcome) =>
             out = Out_normal /\ m2 = m1 /\ le2 ! _s = Some (sptr S) /\
             le2 ! _c = Some (vint (Z.max 1 (c / act_shift)))).
           ++ eapply (exec_if_cmp _ _ _ Clt).
              ** ev.
              ** ev.
              ** reflexivity.
              ** reflexivity.
              ** unfold Small. change (act_lim / 2) with 536870912 in Hdiv. lia.
              ** unfold Small. lia.
              ** cbn [zcmp]. destruct (Z.ltb_spec (c / act_shift) 1) as [Hlt1 | Hge1].
                 --- (* below 1: c = 1; *)
                     run. split.
                     +++ reflexivity.
                     +++ split.
                         *** reflexivity.
                         *** split.
                             ---- tmp.
                             ---- rewrite Z.max_l by lia. tmp.
                 --- (* at least 1 *)
                     apply exec_skip. split.
                     +++ reflexivity.
                     +++ split.
                         *** reflexivity.
                         *** split.
                             ---- tmp.
                             ---- rewrite Z.max_r by lia. tmp.
           ++ intros le2 m2 out (-> & -> & Hs2 & Hc2). apply seqk_normal.
              pose proof (r_inc _ _ _ _ _ _ _ HRep1) as Finc.
              (* s->inc = c; *)
              eapply exec_store.
              ** evl.
              ** ev.
              ** reflexivity.
              ** reflexivity.
              ** fofs. bound.
              ** fofs. cbn [cast_int_int].
                 destruct (fld_storable m1 (b_s S) 248 Mint32 _
                             (vint (Z.max 1 (c / act_shift))) Finc) as [m3 Hst3].
                 exists m3. split.
                 --- apply Hst3.
                 --- exists Vundef. split.
                     +++ reflexivity.
                     +++ split.
                         *** unfold rescale. rewrite <- Ht.
                             apply (rep_store_inc m1 m3 S N lss _ lims _ HRep1).
                             ---- change (act_lim / 2) with 536870912 in *. lia.
                             ---- apply Hst3.
                         *** apply (store_unchanged _ m m1 m3 Mint32 (b_s S) 248
                                      (vint (Z.max 1 (c / act_shift)))).
                             ---- assumption.
                             ---- assumption.
                             ---- apply s_not_frame.
    + (* The invariant holds at a = 0, with the activities of x. *)
      constructor.
      * tmp.
      * tmp.
      * tmp.
      * lia.
      * exists (act (hr x)). split.
        -- rewrite Nat.sub_0_r. reflexivity.
        -- rewrite with_acts_act, with_heur_hr. assumption.
      * apply Mem.unchanged_on_refl.
Qed.

Lemma rescale_fun: exists (b: block),
  Genv.find_symbol ge _rescale = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_rescale).
Proof. apply find_fun. reflexivity. Qed.
