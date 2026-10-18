(* bump raises the activity of an atom by the bump, rescaling first when it would get too
   large, and moves the atom up in the heap (bump). *)
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
From RocqSAT.refinement.c Require Import HeapUp.

(* After rescaling, an atom's activity plus the bump is below act_lim: both are below
   2^10. *)
Lemma rescale_bump_lt: forall (h: Heur) (n a: nat), HeurOk n h -> (a < n)%nat ->
  (tget (act (rescale h n (inc h))) a + inc (rescale h n (inc h)) < act_lim)%Z.
Proof.
  intros h n a Hok Ha. cbn [rescale act inc]. rewrite shift_acts_in by lia.
  pose proof (ho_act Hok a Ha) as Hact. pose proof (ho_inc Hok) as Hinc.
  assert (Hlim: act_lim = small_bound) by reflexivity.
  assert (Hshift: act_shift = 1048576) by reflexivity.
  assert (Hhalf: (act_lim / 2 = key_bound)%Z) by reflexivity.
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

     {{ RepL m sh N lss y /\ a < N /\ act h a + inc h < act_lim }}
       s->act[a] = s->act[a] + s->inc;                                (rep_store_act)
     {{ RepL m2 sh N lss (y <| hr := h2 |>) }}
       int i = s->hpos[a];
       if (i >= 0)
         heap_up(s, i);                                               (heap_up_correct)
     {{ RepL m' sh N lss (y <| hr := heap_up h2 i |>) }}
     {{ RepL m' sh N lss (y <| hr := bump_rest h a |>) }}

   and only the heuristic is written. *)
Lemma bump_end_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (y: Ctx) (a: nat) (le: temp_env) (m: mem),
  RepL m sh N lss y -> (a < N)%nat ->
  (tget (act (hr y)) a + inc (hr y) < act_lim)%Z ->
  le ! _s = Some (sptr sh) -> le ! _a = Some (vnat a) ->
  Exec ge le m bump_end (Returns f_bump (fun (m': mem) (_: val) =>
    HeurPost sh N lss y m (bump_rest (hr y) a) m')).
Proof.
  intros sh N lss y a le m HRep Ha Hlt Hs Ha'.
  pose proof (r_n HRep) as HN.
  pose proof (r_nodup HRep) as Hnd.
  pose proof (r_act HRep) as Fact.
  pose proof (r_inc HRep) as Finc.
  pose proof (a_act HRep) as Aact.
  pose proof (ho_act (r_heur HRep) a Ha) as Hact.
  pose proof (ho_inc (r_heur HRep)) as Hinc.
  set (v := (tget (act (hr y)) a + inc (hr y))%Z).
  unfold bump_end, f_bump. cbn [fn_body drop_stmts].
  (* s->act[a] = s->act[a] + s->inc; *)
  run. eapply (exec_store_arr Aact Ha).
  - evl.
  - ofs.
  - reflexivity.
  - ev.
  - intros m2 Hst. cbn [cast_int_int] in Hst. rewrite add_repr in Hst. fold v in Hst.
    normal.
    assert (Hv: (0 <= v < act_lim)%Z) by (unfold v; lia).
    pose proof (rep_store_act m m2 a v HRep Ha Hv Hst) as HRep2.
    keep_mem m2.
    pose proof (r_hpos HRep2) as Fhpos.
    pose proof (a_hpos HRep2) as Ahpos.
    pose proof (ho_hpos (r_heur HRep) a) as Hpos_lt.
    cbn [set_hr hr set_act hpos] in Fhpos, Ahpos.
    (* int i = s->hpos[a]; *)
    run. unfold bump_rest. cbv zeta. fold v. cbn [set_act hpos].
    destruct (tget (hpos (hr y)) a) as [i|] eqn:Hpos.
    + (* in the heap at i: if (i >= 0) heap_up(s, i); *)
      assert (Hi: (i < N)%nat).
      { apply (Hpos_lt i Ha). reflexivity. }
      cbn [enc_pos]. eapply exec_if_ge.
      * ev.
      * ev.
      * reflexivity.
      * lia.
      * intros Hi_nonneg.
        eapply (exec_call_triple_none heap_up_fun
                  (heap_up_correct sh N lss (y <| hr := set_act (hr y) a v |>) i)).
        -- reflexivity.
        -- evs.
        -- split.
           ++ apply HRep2.
           ++ apply Hi.
        -- intros m3 v3 [HRep3 Hun3]. exists Vundef. split.
           ++ reflexivity.
           ++ split.
              ** apply HRep3.
              ** apply (Mem.unchanged_on_trans _ m m2 m3).
                 --- apply (store_unchanged _ m m m2 Mint32 (b_act sh) (4 * Z.of_nat a)
                              (vint v)).
                     +++ apply Mem.unchanged_on_refl.
                     +++ assumption.
                     +++ intros k [Hne _]. now apply Hne.
                 --- assumption.
      * (* i < 0 is impossible *)
        intros Hi_neg. lia.
    + (* not in the heap: i = -1 *)
      cbn [enc_pos]. eapply exec_if_ge.
      * ev.
      * ev.
      * reflexivity.
      * lia.
      * (* -1 >= 0 is impossible *)
        intros Hneg_nonneg. lia.
      * intros Hneg. apply exec_skip. exists Vundef. split.
        -- reflexivity.
        -- split.
           ++ apply HRep2.
           ++ apply (store_unchanged _ m m m2 Mint32 (b_act sh) (4 * Z.of_nat a)
                       (vint v)).
              ** apply Mem.unchanged_on_refl.
              ** assumption.
              ** intros k [Hne _]. now apply Hne.
Qed.

(* bump rescales when the activity of a would reach act_lim, and then does the rest.
   Writing h for hr x and h1 for rescale h N (inc h) if act h a >= act_lim - inc h, and
   h otherwise:

     {{ RepL m sh N lss x /\ a < N }}
       if (s->act[a] >= ACT_LIM - s->inc)
         rescale(s, s->inc);                                        (rescale_correct)
     {{ RepL m1 sh N lss (x <| hr := h1 |>) /\
        act h1 a + inc h1 < act_lim }}                              (rescale_bump_lt)
       the rest;                                                    (bump_end_correct)
     {{ RepL m' sh N lss (x <| hr := bump_rest h1 a |>) }}

   and bump_rest h1 a is bump h N a; only the heuristic is written. *)
Lemma bump_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (a: nat),
  {{ m | RepL m sh N lss x /\ (a < N)%nat }}
    f_bump(sptr sh, vnat a)
  {{ m', v | HeurPost sh N lss x m (bump (hr x) N a) m' }}.
Proof.
  intros sh N lss x a m [HRep Ha].
  pose proof (r_n HRep) as HN.
  pose proof (r_nodup HRep) as Hnd.
  pose proof (r_act HRep) as Fact.
  pose proof (r_inc HRep) as Finc.
  pose proof (a_act HRep) as Aact.
  pose proof (ho_act (r_heur HRep) a Ha) as Hact.
  pose proof (ho_inc (r_heur HRep)) as Hinc.
  assert (Hlim: act_lim = small_bound) by reflexivity.
  assert (Hhalf: (act_lim / 2 = key_bound)%Z) by reflexivity.
  assert (Hsub: Int.sub (Int.shl (Int.repr 1) (Int.repr 30)) (Int.repr (inc (hr x)))
                = Int.repr (act_lim - inc (hr x))).
  { apply sub_repr. }
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_bump. cbn [fn_body fn_return]. apply exec_seq.
    (* if (s->act[a] >= ACT_LIM - s->inc) ... *)
    run. eapply (exec_if_ge _ (act_lim - inc (hr x))).
    + ev.
    + unfold vint. rewrite <- Hsub. ev.
    + reflexivity.
    + lia.
    + (* rescale(s, s->inc); *)
      intros Hge. unfold bump.
      apply Z.leb_le in Hge as Hleb. rewrite Hleb.
      run. eapply (exec_call_triple_none rescale_fun
                     (rescale_correct sh N lss x (inc (hr x)))).
      * reflexivity.
      * evs.
      * split.
        -- apply HRep.
        -- lia.
      * intros m1 v1 [HRep1 Hun1]. normal. keep_mem m1.
        eapply exec_weaken.
        { apply (bump_end_correct sh N lss
                   (x <| hr := rescale (hr x) N (inc (hr x)) |>) a).
          - assumption.
          - assumption.
          - apply (rescale_bump_lt (hr x) N a).
            + apply (r_heur HRep).
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
    + (* no rescale *)
      intros Hlt. unfold bump.
      apply Z.leb_gt in Hlt as Hleb. rewrite Hleb.
      apply exec_skip. normal. apply (bump_end_correct sh N lss x a).
      * assumption.
      * assumption.
      * lia.
      * tmp.
      * tmp.
Qed.

Lemma bump_fun: FunAt _bump f_bump.
Proof. apply find_fun. reflexivity. Qed.
