(* bump raises the activity of an atom by the bump, rescaling first when it would get too
   large, and moves the atom up in the heap (bump). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Heur Propagate Analysis Step.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep RepHeur Rescale HeapUp.
Import ListNotations.

(* shift_acts from a0 on leaves the activities below a0 alone. *)
Lemma shift_acts_below: forall (k: nat) (t: Table Z) (a0 a: nat), (a < a0)%nat ->
  tget (shift_acts t a0 k) a = tget t a.
Proof.
  intros k. induction k as [|k IH]; intros t a0 a Ha; cbn [shift_acts].
  - reflexivity.
  - rewrite IH by lia. apply tget_tset_other. lia.
Qed.

(* shift_acts divides the activities of the k atoms from a0 on by act_shift. *)
Lemma shift_acts_in: forall (k: nat) (t: Table Z) (a0 a: nat), (a0 <= a < a0 + k)%nat ->
  tget (shift_acts t a0 k) a = (tget t a / act_shift)%Z.
Proof.
  intros k. induction k as [|k IH]; intros t a0 a Ha; cbn [shift_acts].
  - lia.
  - destruct (Nat.eq_dec a0 a) as [<- | Hne].
    + rewrite shift_acts_below by lia. apply tget_tset_same.
    + rewrite IH by lia. rewrite tget_tset_other by assumption. reflexivity.
Qed.

(* After rescaling, an atom's activity plus the bump is below act_lim: both are below
   2^10. *)
Lemma rescale_bump_lt: forall (h: Heur) (n a: nat), HeurOk n h -> (a < n)%nat ->
  (tget (act (rescale h n (inc h))) a + inc (rescale h n (inc h)) < act_lim)%Z.
Proof.
  intros h n a Hok Ha. cbn [rescale act inc]. rewrite shift_acts_in by lia.
  pose proof (ho_act _ _ Hok a Ha) as Hact. pose proof (ho_inc _ _ Hok) as Hinc.
  assert (Hlim: act_lim = 1073741824) by reflexivity.
  assert (Hshift: act_shift = 1048576) by reflexivity.
  assert (Hhalf: (act_lim / 2 = 536870912)%Z) by reflexivity.
  assert (Hact': (tget (act h) a / act_shift < 1024)%Z).
  { apply Z.div_lt_upper_bound.
    - lia.
    - lia. }
  assert (Hinc': (Z.max 1 (inc h / act_shift) < 1024)%Z).
  { apply Z.max_lub_lt.
    - lia.
    - apply Z.div_lt_upper_bound.
      + lia.
      + lia. }
  lia.
Qed.

(* What bump does once the activity is low enough: raise it by the bump, and move the
   atom up if it is in the heap. bump h n a is bump_rest of h, rescaled or not. *)
Definition bump_rest (h: Heur) (a: nat): Heur :=
  let h2 := set_act h a (tget (act h) a + inc h)%Z in
  match tget (hpos h2) a with
  | Some i => heap_up h2 i
  | None   => h2
  end.

(* The statements of bump after the possible rescale. *)
Definition bump_end: statement := drop_stmts 1 (fn_body f_bump).

(* The end of bump, for a context y whose activity of a plus the bump is below act_lim.
   Writing h for hr y and h2 for set_act h a (act h a + inc h):

     {{ RepL m S N lss y lims lt /\ a < N /\ act h a + inc h < act_lim }}
       s->act[a] = s->act[a] + s->inc;                                (rep_store_act)
     {{ RepL m2 S N lss (with_heur y h2) lims lt }}
       int i = s->hpos[a];
       if (i >= 0)
         heap_up(s, i);                                               (heap_up_correct)
     {{ RepL m' S N lss (with_heur y (heap_up h2 i)) lims lt }}
     {{ RepL m' S N lss (with_heur y (bump_rest h a)) lims lt }}

   and only the heuristic is written. *)
Lemma bump_end_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (y: Ctx) (lims: list nat) (a: nat) (le: temp_env) (m: mem),
  RepL m S N lss y lims lt -> (a < N)%nat ->
  (tget (act (hr y)) a + inc (hr y) < act_lim)%Z ->
  le ! _s = Some (sptr S) -> le ! _a = Some (vint (Z.of_nat a)) ->
  Exec ge le m bump_end (Returns f_bump (fun (m': mem) (_: val) =>
    RepL m' S N lss (with_heur y (bump_rest (hr y) a)) lims lt /\
    Mem.unchanged_on (HeurFrame S) m m')).
Proof.
  intros S N lss y lims a le m HRep Ha Hlt Hs Ha'.
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_act _ _ _ _ _ _ _ HRep) as Fact.
  pose proof (r_inc _ _ _ _ _ _ _ HRep) as Finc.
  pose proof (a_act _ _ _ _ _ _ _ HRep) as Aact.
  pose proof (ho_act _ _ (r_heur _ _ _ _ _ _ _ HRep) a Ha) as Hact.
  pose proof (ho_inc _ _ (r_heur _ _ _ _ _ _ _ HRep)) as Hinc.
  set (v := (tget (act (hr y)) a + inc (hr y))%Z).
  unfold bump_end, f_bump. cbn [fn_body drop_stmts].
  (* s->act[a] = s->act[a] + s->inc; *)
  run. eapply exec_store.
  - evl.
  - ev.
  - reflexivity.
  - reflexivity.
  - ofs. bound.
  - ofs. cbn [cast_int_int]. rewrite add_repr. fold v.
    destruct (arr_storable m (b_act S) N a _ v Aact Ha) as [m2 Hst].
    exists m2. split.
    + apply Hst.
    + normal.
      assert (Hv: (0 <= v < act_lim)%Z) by (unfold v; lia).
      pose proof (rep_store_act m m2 S N lss y lims a v HRep Ha Hv Hst) as HRep2.
      keep_mem m2.
      pose proof (r_hpos _ _ _ _ _ _ _ HRep2) as Fhpos.
      pose proof (a_hpos _ _ _ _ _ _ _ HRep2) as Ahpos.
      pose proof (ho_hpos _ _ (r_heur _ _ _ _ _ _ _ HRep) a) as Hpos_lt.
      cbn [with_heur hr set_act hpos] in Fhpos, Ahpos.
      (* int i = s->hpos[a]; *)
      run. unfold bump_rest. cbv zeta. fold v. cbn [set_act hpos].
      destruct (tget (hpos (hr y)) a) as [i|] eqn:Hpos.
      * (* in the heap at i: if (i >= 0) heap_up(s, i); *)
        assert (Hi: (i < N)%nat).
        { apply (Hpos_lt i Ha). reflexivity. }
        cbn [enc_pos]. eapply (exec_if_cmp _ _ _ Cge).
        -- ev.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- unfold Small. lia.
        -- unfold Small. lia.
        -- replace (zcmp Cge (Z.of_nat i) 0) with true
             by (symmetry; cbn [zcmp]; apply Z.leb_le; lia).
           cbv beta iota. call heap_up_fun. eapply call_weaken.
           { apply (heap_up_correct (lt := lt) S N lss (with_heur y (set_act (hr y) a v))
                      lims i).
             split.
             - apply HRep2.
             - assumption. }
           intros m3 v3 [HRep3 Hun3]. exists Vundef. split.
           ++ reflexivity.
           ++ split.
              ** apply HRep3.
              ** apply (Mem.unchanged_on_trans _ m m2 m3).
                 --- apply (store_unchanged _ m m m2 Mint32 (b_act S) (4 * Z.of_nat a)
                              (vint v)).
                     +++ apply Mem.unchanged_on_refl.
                     +++ assumption.
                     +++ intros k [Hne _]. now apply Hne.
                 --- assumption.
      * (* not in the heap: i = -1 *)
        cbn [enc_pos]. eapply (exec_if_cmp _ _ _ Cge).
        -- ev.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- unfold Small. lia.
        -- unfold Small. lia.
        -- replace (zcmp Cge (-1) 0) with false by reflexivity.
           cbv beta iota. apply exec_skip. exists Vundef. split.
           ++ reflexivity.
           ++ split.
              ** apply HRep2.
              ** apply (store_unchanged _ m m m2 Mint32 (b_act S) (4 * Z.of_nat a)
                          (vint v)).
                 --- apply Mem.unchanged_on_refl.
                 --- assumption.
                 --- intros k [Hne _]. now apply Hne.
Qed.

(* bump rescales when the activity of a would reach act_lim, and then does the rest.
   Writing h for hr x and h1 for rescale h N (inc h) if act h a >= act_lim - inc h, and
   h otherwise:

     {{ RepL m S N lss x lims lt /\ a < N }}
       if (s->act[a] >= ACT_LIM - s->inc)
         rescale(s, s->inc);                                        (rescale_correct)
     {{ RepL m1 S N lss (with_heur x h1) lims lt /\
        act h1 a + inc h1 < act_lim }}                              (rescale_bump_lt)
       the rest;                                                    (bump_end_correct)
     {{ RepL m' S N lss (with_heur x (bump_rest h1 a)) lims lt }}

   and bump_rest h1 a is bump h N a; only the heuristic is written. *)
Lemma bump_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (a: nat),
  {{ m | RepL m S N lss x lims lt /\ (a < N)%nat }}
    f_bump(sptr S, vint (Z.of_nat a))
  {{ m', v | RepL m' S N lss (with_heur x (bump (hr x) N a)) lims lt /\
             Mem.unchanged_on (HeurFrame S) m m' }}.
Proof.
  intros S N lss x lims a m [HRep Ha].
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_act _ _ _ _ _ _ _ HRep) as Fact.
  pose proof (r_inc _ _ _ _ _ _ _ HRep) as Finc.
  pose proof (a_act _ _ _ _ _ _ _ HRep) as Aact.
  pose proof (ho_act _ _ (r_heur _ _ _ _ _ _ _ HRep) a Ha) as Hact.
  pose proof (ho_inc _ _ (r_heur _ _ _ _ _ _ _ HRep)) as Hinc.
  assert (Hlim: act_lim = 1073741824) by reflexivity.
  assert (Hhalf: (act_lim / 2 = 536870912)%Z) by reflexivity.
  assert (Hsub: Int.sub (Int.shl (Int.repr 1) (Int.repr 30)) (Int.repr (inc (hr x)))
                = Int.repr (act_lim - inc (hr x))).
  { apply sub_repr. }
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_bump. cbn [fn_body fn_return]. apply exec_seq.
    (* if (s->act[a] >= ACT_LIM - s->inc) ... *)
    run. eapply (exec_if_cmp _ _ _ Cge _ _ _ (act_lim - inc (hr x))).
    + ev.
    + unfold vint. rewrite <- Hsub. ev.
    + reflexivity.
    + reflexivity.
    + unfold Small. lia.
    + unfold Small. lia.
    + cbn [zcmp]. unfold bump.
      destruct (Z.leb_spec (act_lim - inc (hr x)) (tget (act (hr x)) a)) as [Hge | Hlt].
      * (* rescale(s, s->inc); *)
        run. call rescale_fun. eapply call_weaken.
        { apply (rescale_correct (lt := lt) S N lss x lims (inc (hr x))). split.
          - assumption.
          - lia. }
        intros m1 v1 [HRep1 Hun1]. normal. keep_mem m1.
        eapply exec_weaken.
        { apply (bump_end_correct (lt := lt) S N lss
                   (with_heur x (rescale (hr x) N (inc (hr x)))) lims a).
          - assumption.
          - assumption.
          - apply (rescale_bump_lt (hr x) N a).
            + apply (r_heur _ _ _ _ _ _ _ HRep).
            + assumption.
          - tmp.
          - tmp. }
        intros le' m' out [v' [Hres [HRep' Hun']]]. exists v'. split.
        -- assumption.
        -- split.
           ++ apply HRep'.
           ++ apply (Mem.unchanged_on_trans _ m m1 m').
              ** assumption.
              ** assumption.
      * (* no rescale *)
        apply exec_skip. normal. apply (bump_end_correct (lt := lt) S N lss x lims a).
        -- assumption.
        -- assumption.
        -- lia.
        -- tmp.
        -- tmp.
Qed.

Lemma bump_fun: exists (b: block),
  Genv.find_symbol ge _bump = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_bump).
Proof. apply find_fun. reflexivity. Qed.
