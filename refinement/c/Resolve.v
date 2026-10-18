(* resolve resolves a conflict (resolve): it fails without decisions; otherwise it
   analyses the conflict and backjumps, asserting the literal the analysis gives with the
   analysed clause as its reason, or flips the last decision; or it gives up. *)
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
From RocqSAT.refinement Require Import Tactics.
From RocqSAT.refinement Require Import Table.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import Heur.
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement Require Import Analysis.
From RocqSAT.refinement Require Import Step.
From RocqSAT.refinement Require Import SolverStep.
From RocqSAT.refinement.c Require Import Arrays.
From RocqSAT.refinement.c Require Import Logic.
From RocqSAT.refinement.c Require Import Common.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Rep.
From RocqSAT.refinement.c Require Import RepReasons.
From RocqSAT.refinement.c Require Import RepHeur.
From RocqSAT.refinement.c Require Import Assign.
From RocqSAT.refinement.c Require Import Decay.
From RocqSAT.refinement.c Require Import Cut.
From RocqSAT.refinement.c Require Import Analyze.
From RocqSAT.refinement.c Require Import UnmarkLower.
From RocqSAT.refinement.c Require Import PushReason.

(* What C returns and leaves for an outcome of a step on the context: 0 to stop with P of
   the memory, 1 to fail, and 2 with the next context in memory. *)
Definition COutcome (sh: Shape) (N: nat) (lss: list (list Lit)) (P: mem -> Prop)
  (cr: CResult) (m: mem) (v: val): Prop :=
match cr with
| CStop          => v = vint 0 /\ P m
| CFail          => v = vint 1
| CNext x'       => v = vint 2 /\ Rep m sh N lss x'
end.

(* What resolve returns: -1 when out of room, or the outcome cr. *)
Definition ResolvePost (sh: Shape) (N: nat) (lss: list (list Lit)) (P: mem -> Prop)
  (cr: CResult) (m': mem) (v: val): Prop :=
  v = vint (-1) \/ COutcome sh N lss P cr m' v.

(* Setting the level field by field is set_level. *)
Lemma set_level_setters: forall (z: Ctx) (c: nat) (st: list nat) (d: nat)
  (ls: list nat),
  z <| cur := c |> <| saved := st |> <| dl := d |> <| lims := ls |> =
    set_level z c st d ls.
Proof. intros z c st d ls. reflexivity. Qed.

(* Going back is cutting the trail and then setting the level. (Proved through
   set_level_setters: a direct reflexivity makes the kernel unfold cut, for seconds.) *)
Lemma back_level: forall (x: Ctx) (j c: nat) (st: list nat) (d: nat) (ls: list nat),
  back x j c st d ls = set_level (cut x j) c st d ls.
Proof. intros x j c st d ls. unfold back. apply set_level_setters. Qed.

(* The context y is represented between steps: by RepL, without lower literals, and with
   the watch-list pool free beyond its watch lists. *)
Lemma rep_intro: forall (m: mem) (sh: Shape) (N: nat) (lss: list (list Lit)) (y: Ctx)
  (tp: nat -> Z),
  RepL m sh N lss y -> lower y = [] -> PoolArr m sh tp -> PoolFree sh N tp (wls y) ->
  Rep m sh N lss y.
Proof.
  intros m sh N lss y tp HRep Hlow Apool Hpool. split.
  - assumption.
  - split.
    + assumption.
    + exists tp. split; assumption.
Qed.

(* A part of resolve that returns can be followed by more statements: they do not run. *)
Lemma returns_seq: forall (Q: mem -> val -> Prop) (rest s: statement) (le: temp_env)
  (m: mem),
  Exec ge le m s (Returns f_resolve Q) -> Exec ge le m s
    (SeqK ge rest (Returns f_resolve Q)).
Proof.
  intros Q rest s le m Hs. eapply exec_weaken.
  - apply Hs.
  - intros le' m' out Hret. apply seqk_abrupt.
    + intros ->. destruct Hret as (v & Hv & _). cbn in Hv. contradiction.
    + assumption.
Qed.

(* The test of both ways on after assign has put its result in the temporary tw:
   if (!w) return -1;. *)
Definition assigned_stmt (tw: ident): statement :=
  Sifthenelse (Eunop Onotbool (Etempvar tw Ctypesdefs.tint) Ctypesdefs.tint)
    (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) Ctypesdefs.tint)
                      Ctypesdefs.tint)))
    Sskip.
(* The statement after it, for the next context: return 2;. *)
Definition return_next: statement :=
  Sreturn (Some (Econst_int (Int.repr 2) Ctypesdefs.tint)).

(* The end of both ways on: the assignment of the literal to assert, done by assign whose
   result is in temporary tw:

     {{ the result w of assign: 0, or 1 with RepL x' /\ Arr pool tp }}
       if (!w) return -1;
       return 2;
     {{ ResolvePost (CNext x') }}                                                    *)
Lemma resolve_assigned: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (P: mem -> Prop) (x': Ctx) (tp: nat -> Z) (tw: ident) (w: val) (le: temp_env)
  (m: mem),
  le ! tw = Some w ->
  (w = vint 0 \/
   (w = vint 1 /\ RepL m sh N lss x' /\ PoolArr m sh tp)) ->
  lower x' = [] -> PoolFree sh N tp (wls x') ->
  Exec ge le m (assigned_stmt tw)
    (SeqK ge return_next (Returns f_resolve (ResolvePost sh N lss P (CNext x')))).
Proof.
  intros sh N lss P x' tp tw w le m Htw Hw Hlower Hpool.
  unfold assigned_stmt, return_next.
  destruct Hw as [-> | (-> & HRep & Apool)].
  - (* out of room: return -1; *)
    branch 1.
    + (* w = 0: !w is 1 *)
      intros Hnonzero. return_int.
      now left.
    + (* 1 is not 0 *)
      intros Hzero. lia.
  - (* return 2; with the next context *)
    branch 0.
    + (* 0 is not nonzero *)
      intros Hnonzero. lia.
    + (* w = 1: !w is 0 *)
      intros Hzero. apply exec_skip. normal.
      return_int.
      right. split.
      * reflexivity.
      * apply (rep_intro m sh N lss x' tp); assumption.
Qed.

(* The statements of resolve after the backjump: flipping the last decision. *)
Definition resolve_flip: statement := drop_stmts 7 (fn_body f_resolve).

(* The statements of the flip after cut: from s->cur = s->saved[d - 1]. *)
Definition resolve_flip_level: statement := drop_stmts 3 resolve_flip.

(* After the flip has cut the trail of y at the last decision j0, with l = tget (tr y) j0
   and the cursor c0 saved for it:

     {{ RepL (cut (y <| lower := [] |>) j0) /\ saved y = c0 :: st }}
       s->cur = s->saved[d - 1];
       s->dl = d - 1;                                                  (rep_store_level)
     {{ RepL xb, xb = back (y <| lower := [] |>) j0 c0 st (dl y - 1) (tl (lims y)) }}
       if (!assign(s, l ^ 1, 0)) return -1;                           (assign_correct)
       return 2;                                                      (resolve_assigned)
     {{ ResolvePost (flip y j0) }}                                                   *)
Lemma resolve_flip_level_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (y: Ctx) (lims0: list nat) (j0 c0: nat) (st: list nat) (P: mem -> Prop)
  (tp: nat -> Z) (le: temp_env) (m: mem),
  RepL m sh N lss (cut (y <| lower := [] |>) j0) -> lims y = j0 :: lims0 ->
  saved y = c0 :: st -> (extract (tget (tr y) j0) < N)%nat ->
  PoolArr m sh tp -> PoolFree sh N tp (wls y) ->
  le ! _s = Some (sptr sh) -> le ! _l = Some (vint (key (tget (tr y) j0))) ->
  le ! _d = Some (vnat (length (j0 :: lims0))) ->
  Exec ge le m resolve_flip_level
    (Returns f_resolve (ResolvePost sh N lss P (flip y j0))).
Proof.
  intros sh N lss y lims0 j0 c0 st P tp le m HRep Hlims Hsv Hl Apool Hpool Hs Hlv Hd.
  pose proof (r_n HRep) as HN.
  pose proof (r_nodup HRep) as Hnd.
  pose proof (r_dl_eq HRep) as Hdl.
  pose proof (r_saved_len HRep) as Hslen.
  pose proof (r_dl_le HRep) as Hdle.
  cbn [cut set_vals set_tlen set_qhead set_nr set_hr set_lower dl lims saved]
    in Hdl, Hslen, Hdle.
  rewrite Hsv, Hlims in Hslen. rewrite Hlims in Hdl, Hdle.
  cbn [length] in Hdl, Hslen, Hdle.
  pose proof (key_small _ N Hl HN) as Hkl.
  (* the flipped literal ¬l, as C computes it: l ^ 1 *)
  assert (Hxor: Int.xor (Int.repr (key (tget (tr y) j0))) (Int.repr 1)
                = Int.repr (key (¬(tget (tr y) j0)))).
  { apply xor_key. lia. }
  assert (Hnl: (extract (¬(tget (tr y) j0)) < N)%nat) by (now destruct (tget (tr y) j0)).
  (* the level d - 1 below the last decision is the number of cursors saved before it *)
  assert (Hsub: Int.sub (Int.repr (Z.of_nat (length (j0 :: lims0)))) (Int.repr 1)
                = Int.repr (Z.of_nat (length st))).
  { rewrite sub_repr. f_equal. cbn [length]. lia. }
  pose proof (r_cur HRep) as Fcur.
  pose proof (r_dl HRep) as Fdl.
  pose proof (r_saved HRep) as Fsaved.
  pose proof (a_saved HRep) as (tsv & Asaved & Htsv).
  cbn [cut set_vals set_tlen set_qhead set_nr set_hr set_lower saved] in Htsv.
  rewrite Hsv in Htsv. cbn [length] in Htsv.
  assert (Htc0: tsv (length st) = Z.of_nat c0).
  { rewrite Htsv by lia. cbn [rev]. rewrite <- length_rev, nth_middle. reflexivity. }
  unfold resolve_flip_level, resolve_flip, f_resolve. cbn [fn_body drop_stmts].
  (* s->cur = s->saved[d - 1]; *)
  run. rewrite Htc0. store Fcur as m1 Hst1.
  assert (Fdl1: IntAt m1 sh o_dl (length (lims y))).
  { apply (fld_store_other Fdl Hst1). right.
    cbn [size_chunk]. lia. }
  (* s->dl = d - 1; *)
  run. store Fdl1 as m2 Hst2.
  cbn [cast_int_int] in Hst2. rewrite Hsub in Hst2. normal.
  (* the context after going back, as flip has it *)
  pose proof (rep_store_level m m1 m2 0 c0 st HRep Hsv Hst1 Hst2) as HRep2.
  change (lims (cut (y <| lower := [] |>) j0)) with (lims y) in HRep2.
  rewrite <- back_level in HRep2.
  set (xb := back (y <| lower := [] |>) j0 c0 st (length st) (skipn 1 (lims y)))
    in HRep2.
  assert (Apool1: PoolArr m1 sh tp).
  { apply (arr_store_other Apool Hst1). neq Hnd. }
  assert (Apool2: PoolArr m2 sh tp).
  { apply (arr_store_other Apool1 Hst2). neq Hnd. }
  keep_mem m2.
  (* if (!assign(s, l ^ 1, 0)) return -1; return 2; *)
  run. eapply (exec_call_triple assign_fun
                 (assign_correct sh N lss xb (¬(tget (tr y) j0)) no_reason tp)).
  - reflexivity.
  - unfold vint. rewrite <- Hxor. evs.
  - splits.
    + apply HRep2.
    + assumption.
    + constructor.
    + assumption.
  - intros m3 w Hw. normal. unfold flip. rewrite Hsv.
    replace (dl y - 1)%nat with (length st) by lia.
    replace (tl (lims y)) with (skipn 1 (lims y)) by (now rewrite Hlims).
    apply (resolve_assigned sh N lss P _ tp _t'5 w).
    + tmp.
    + assumption.
    + reflexivity.
    + assumption.
Qed.

(* Flipping the last decision of the context y, at trail position j0:

     {{ RepL y /\ lims y = j0 :: lims0 /\ saved y = c0 :: st }}
       s->ltlen = 0;                                              (rep_store_ltlen_zero)
     {{ RepL y1, y1 = y <| lower := [] |> }}
       int l = s->tr[lo];
       cut(s, lo);                                                       (cut_correct)
     {{ RepL (cut y1 j0) /\ l = key (tget (tr y) j0) }}
       ...                                                (resolve_flip_level_correct)
     {{ ResolvePost (flip y j0) }}                                                   *)
Lemma resolve_flip_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit)) (y: Ctx)
  (lims0: list nat) (j0 c0: nat) (st: list nat) (P: mem -> Prop) (tp: nat -> Z)
  (le: temp_env) (m: mem),
  RepL m sh N lss y -> lims y = j0 :: lims0 -> saved y = c0 :: st -> (j0 < tlen y)%nat ->
  PoolArr m sh tp ->
  PoolFree sh N tp (wls y) ->
  le ! _s = Some (sptr sh) -> le ! _lo = Some (vnat j0) ->
  le ! _d = Some (vnat (length (j0 :: lims0))) ->
  Exec ge le m resolve_flip (Returns f_resolve (ResolvePost sh N lss P (flip y j0))).
Proof.
  intros sh N lss y lims0 j0 c0 st P tp le m HRep Hlims Hsv Hj0 Apool Hpool Hs Hlo Hd.
  pose proof (r_nodup HRep) as Hnd.
  pose proof (r_n HRep) as HN.
  pose proof (r_ltlen HRep) as Fltlen.
  pose proof (r_tlen_le HRep) as Htlen.
  assert (Hl: (extract (tget (tr y) j0) < N)%nat)
    by (apply (r_tr_atoms HRep); assumption).
  unfold resolve_flip, f_resolve. cbn [fn_body drop_stmts].
  (* s->ltlen = 0; *)
  run. store Fltlen as m1 Hst1.
  pose proof (rep_store_ltlen_zero m m1 HRep Hst1) as HRep1.
  set (y1 := y <| lower := [] |>) in HRep1.
  assert (Apool1: PoolArr m1 sh tp).
  { apply (arr_store_other Apool Hst1). neq Hnd. }
  keep_mem m1.
  pose proof (r_tr HRep1) as Ftr1.
  pose proof (a_tr HRep1) as Atr1. cbn [set_lower tr y1] in Atr1.
  (* int l = s->tr[lo]; cut(s, lo); *)
  run. call cut_fun (cut_correct sh N lss y1 j0 tp).
  - splits.
    + apply HRep1.
    + cbn [set_lower tlen y1]. lia.
    + assumption.
  - intros m2 v [HRep2 Apool2]. normal. keep_mem m2.
    apply (resolve_flip_level_correct sh N lss y lims0 j0 c0 st P tp).
    + apply HRep2.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + tmp.
    + tmp.
    + tmp.
Qed.

(* The backjump: the statements of resolve when the analysis gives a literal to assert
   below the current level. *)
Definition resolve_jump: statement :=
  then_stmt (drop_stmts 1 (then_stmt (first_stmt (drop_stmts 6 (fn_body f_resolve))))).

(* The decision of level mx + 1 of y, below the current level: it is at trail position
   j, c0 is the cursor saved for it, st are the cursors saved before it and ls the
   decision positions up to level mx (entry length (lims y) - (mx + 1) of the stacks,
   from the newest). *)
Record LevelAt (y: Ctx) (mx j c0: nat) (st ls: list nat): Prop := {
  la_below: (mx < length (lims y))%nat;
  la_pos: nth_error (lims y) (length (lims y) - S mx) = Some j;
  la_saved: skipn (length (lims y) - S mx) (saved y) = c0 :: st;
  la_rest: skipn (S (length (lims y) - S mx)) (lims y) = ls;
}.

(* The arrays hold the stacks oldest first: at a level mx + 1 below the current one,
   entry mx of lims is its decision position j and entry mx of saved its cursor c0, and
   the mx cursors st are saved before it. *)
Lemma level_at_entries: forall (y: Ctx) (mx j c0: nat) (st ls: list nat),
  LevelAt y mx j c0 st ls -> length (saved y) = length (lims y) ->
  length st = mx /\ nth mx (rev (lims y)) 0%nat = j /\ nth mx (rev (saved y)) 0%nat = c0.
Proof.
  intros y mx j c0 st ls [Hmx Hj Hsv _] Hslen.
  set (k := (length (lims y) - S mx)%nat) in Hj, Hsv.
  assert (Hk: k = (length (lims y) - S mx)%nat) by reflexivity. clearbody k.
  splits.
  - assert (Hlen: length (skipn k (saved y)) = S (length st))
      by (rewrite Hsv; reflexivity).
    rewrite length_skipn in Hlen. lia.
  - rewrite rev_nth by assumption. rewrite <- Hk. apply nth_error_nth. assumption.
  - rewrite rev_nth by lia. rewrite Hslen, <- Hk.
    rewrite (skipn_nth (saved y) 0%nat k) in Hsv by lia. injection Hsv as Hc0 _.
    assumption.
Qed.

(* The backjump after going back: the statements from int r = push_reason(s, u). *)
Definition resolve_push: statement := drop_stmts 3 resolve_jump.

(* Asserting u with the reason push_reason gives, in the context xj after going back:

     {{ RepL xj /\ Arr pool tp /\ u in the temporaries }}
       int r = push_reason(s, u);                                (push_reason_correct)
     {{ RepL x4, for push_reason xj u = (x4, r) }}
       s->ltlen = 0;                                              (rep_store_ltlen_zero)
     {{ RepL (x4 <| lower := [] |>) }}
       if (!assign(s, u, r)) return -1;                               (assign_correct)
       return 2;                                                      (resolve_assigned)
     {{ ResolvePost (CNext (assign (x4 <| lower := [] |>) u r)) }}                 *)
Lemma resolve_push_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (xj: Ctx) (u: Lit) (P: mem -> Prop) (tp: nat -> Z) (le: temp_env) (m: mem),
  RepL m sh N lss xj -> PoolArr m sh tp -> PoolFree sh N tp (wls xj) ->
  (extract u < N)%nat ->
  le ! _s = Some (sptr sh) -> le ! _u = Some (vint (key u)) ->
  Exec ge le m resolve_push
    (Returns f_resolve (ResolvePost sh N lss P
       (match push_reason xj u with
        | (x4, r) => CNext (assign (x4 <| lower := [] |>) u r)
        end))).
Proof.
  intros sh N lss xj u P tp le m HRep Apool Hpool Hu Hs Hu'.
  pose proof (r_nodup HRep) as Hnd.
  unfold resolve_push, resolve_jump, f_resolve.
  cbn [fn_body drop_stmts first_stmt then_stmt].
  (* int r = push_reason(s, u); *)
  run. call push_reason_fun (push_reason_correct sh N lss xj u).
  - split.
    + assumption.
    + assumption.
  - intros m4 w Hpost. unfold PushPost in Hpost.
    (* push_reason keeps the watch lists *)
    assert (Hwls: wls (fst (push_reason xj u)) = wls xj)
      by (rewrite push_reason_wls; reflexivity).
    destruct (push_reason xj u) as [x4 r] eqn:Hpush.
    destruct Hpost as (Hr & -> & HRep4 & Hun4). normal.
    transfer Hun4 Hnd. keep_mem m4.
    cbn [fst] in Hwls.
    pose proof (r_ltlen HRep4) as Fltlen4.
    (* s->ltlen = 0; *)
    run. store Fltlen4 as m5 Hst5.
    pose proof (rep_store_ltlen_zero m4 m5 HRep4 Hst5) as HRep5.
    assert (Apool5: PoolArr m5 sh tp).
    { apply (arr_store_other Apool Hst5). neq Hnd. }
    keep_mem m5.
    (* if (!assign(s, u, r)) return -1; return 2; *)
    run. call assign_fun (assign_correct sh N lss (x4 <| lower := [] |>) u r tp).
    + split.
      * apply HRep5.
      * split.
        -- assumption.
        -- split; assumption.
    + intros m6 w Hw. normal.
      apply (resolve_assigned sh N lss P _ tp _t'4 w).
      * tmp.
      * assumption.
      * reflexivity.
      * cbn [assign set_lower wls]. rewrite Hwls. assumption.
Qed.

(* Going back from the context y to level mx, below the current one, and asserting u:

     {{ RepL y /\ LevelAt y mx j c0 st ls /\ u in the temporaries }}
       cut(s, s->lims[mx]);                                              (cut_correct)
       s->cur = s->saved[mx];
       s->dl = mx;                                                     (rep_store_level)
     {{ RepL xj, xj = back y j c0 st mx ls }}
       ...                                                      (resolve_push_correct)
     {{ ResolvePost (CNext (assign (x4 <| lower := [] |>) u r)),
        for push_reason xj u = (x4, r) }}                                          *)
Lemma resolve_jump_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit)) (y: Ctx)
  (u: Lit) (mx j c0: nat) (st ls: list nat) (P: mem -> Prop) (tp: nat -> Z)
  (le: temp_env) (m: mem),
  RepL m sh N lss y -> PoolArr m sh tp -> PoolFree sh N tp (wls y) -> LimsBelow y ->
  LevelAt y mx j c0 st ls -> (extract u < N)%nat ->
  le ! _s = Some (sptr sh) -> le ! _u = Some (vint (key u)) ->
  le ! _mx = Some (vnat mx) ->
  Exec ge le m resolve_jump
    (Returns f_resolve (ResolvePost sh N lss P
       (match push_reason (back y j c0 st mx ls) u with
        | (x4, r) => CNext (assign (x4 <| lower := [] |>) u r)
        end))).
Proof.
  intros sh N lss y u mx j c0 st ls P tp le m HRep Apool Hpool Hlims Hlevel Hu
    Hs Hu' Hmx'.
  pose proof Hlevel as [Hmx Hj Hsv Hls].
  (* k: the entry of the stacks, from the newest *)
  set (k := (length (lims y) - S mx)%nat) in Hj, Hsv, Hls.
  subst ls.
  pose proof (r_n HRep) as HN.
  pose proof (r_nodup HRep) as Hnd.
  pose proof (r_saved_len HRep) as Hslen.
  pose proof (r_dl_le HRep) as Hdle.
  pose proof (r_tlen_le HRep) as Htlen.
  destruct (level_at_entries y mx j c0 st _ Hlevel Hslen) as (Hst & Hlj & Hsc0).
  assert (Hjt: (j < tlen y)%nat).
  { apply Hlims. apply nth_error_In with k. assumption. }
  pose proof (r_lims HRep) as Flims.
  pose proof (a_lims HRep) as (tl & Alims & Htl).
  unfold resolve_jump, f_resolve.
  cbn [fn_body drop_stmts first_stmt then_stmt].
  (* cut(s, s->lims[mx]); *)
  run. rewrite (Htl mx Hmx), Hlj.
  call cut_fun (cut_correct sh N lss y j tp).
  - splits.
    + apply HRep.
    + lia.
    + assumption.
  - intros m1 v [HRep1 Apool1]. normal. keep_mem m1.
    pose proof (r_cur HRep1) as Fcur1.
    pose proof (r_dl HRep1) as Fdl1.
    pose proof (r_saved HRep1) as Fsaved1.
    pose proof (a_saved HRep1) as (tsv & Asaved & Htsv).
    cbn [cut set_vals set_tlen set_qhead set_nr set_hr saved] in Htsv.
    (* s->cur = s->saved[mx]; *)
    run. rewrite (Htsv mx) by lia. rewrite Hsc0. store Fcur1 as m2 Hst2.
    assert (Fdl2: IntAt m2 sh o_dl (length (lims y))).
    { apply (fld_store_other Fdl1 Hst2). right.
      cbn [size_chunk]. lia. }
    (* s->dl = mx; *)
    run. store Fdl2 as m3 Hst3.
    cbn [cast_int_int] in Hst3. rewrite <- Hst in Hst3 |- *.
    normal.
    (* the context after going back, as resolve has it, at level mx = length st *)
    pose proof (rep_store_level m1 m2 m3 k c0 st HRep1 Hsv Hst2 Hst3) as HRep3.
    change (lims (cut y j)) with (lims y) in HRep3.
    rewrite <- back_level in HRep3.
    assert (Apool2: PoolArr m2 sh tp).
    { apply (arr_store_other Apool1 Hst2). neq Hnd. }
    assert (Apool3: PoolArr m3 sh tp).
    { apply (arr_store_other Apool2 Hst3). neq Hnd. }
    keep_mem m3.
    apply (resolve_push_correct sh N lss _ u P tp).
    + apply HRep3.
    + assumption.
    + assumption.
    + assumption.
    + tmp.
    + tmp.
Qed.

(* What resolve does after the analysis gave the literal u to assert and unmarking the
   lower literals gave the highest level mx among them, in the context y with u
   unmarked: it goes back to level mx and asserts u when mx is below the current level,
   or else flips the last decision j0. *)
Definition jump_or_flip (y: Ctx) (j0 mx: nat) (u: Lit): CResult :=
  if (mx <? dl y)%nat then
    match nth_error (lims y) (dl y - S mx)%nat with
    | Some j =>
      match skipn (dl y - S mx)%nat (saved y) with
      | c0 :: st =>
        match push_reason (back y j c0 st mx (skipn (S (dl y - S mx)) (lims y))) u
        with
        | (x4, r) => CNext (assign (x4 <| lower := [] |>) u r)
        end
      | []       => flip y j0
      end
    | None   => flip y j0
    end
  else flip y j0.

(* What resolve does after the analysis gave ou and unmarking the lower literals gave
   the context x2 and the highest level mx among them: assert the literal, or else flip
   the last decision j0. *)
Definition assert_or_flip (x2: Ctx) (j0 mx: nat) (ou: option Lit): CResult :=
  match ou with
  | Some u => jump_or_flip (x2 <| mrk := tset (mrk x2) (lit_key u) false |>) j0 mx u
  | None   => flip x2 j0
  end.

(* The analysis and the unmarking change only the marks, the lower literals and the
   heuristic: the levels, the trail and the watch lists stay those of x. *)
Lemma analysed_keeps: forall (x x1 x2: Ctx) (hd: Heur) (i d lo mx: nat)
  (ou: option Lit),
  analyze (x <| hr := hd |>) i d lo = (x1, ou) -> unmark_lower x1 = (x2, mx) ->
  dl x2 = dl x /\ lims x2 = lims x /\ saved x2 = saved x /\ tlen x2 = tlen x /\
  wls x2 = wls x.
Proof.
  intros x x1 x2 hd i d lo mx ou Han Hul.
  pose proof (resolve_analysed x x1 x2 hd i d lo mx ou Han Hul) as Hx2.
  rewrite Hx2. splits; reflexivity.
Qed.

(* resolve in its parts: the analysis, the unmarking, and then assert_or_flip, which
   reads the levels of the context after them (they are those of x). *)
Lemma resolve_parts: forall (x: Ctx) (i j0: nat) (lims0: list nat),
  lims x = j0 :: lims0 ->
  resolve x i =
    match analyze (x <| hr := decay (hr x) (nvars x) |>) i (dl x) j0 with
    | (x1, ou) =>
      match unmark_lower x1 with
      | (x2, mx) => assert_or_flip x2 j0 mx ou
      end
    end.
Proof.
  intros x i j0 lims0 Hlims. unfold resolve. rewrite Hlims.
  destruct (analyze _ i (dl x) j0) as [x1 ou] eqn:Han.
  destruct (unmark_lower x1) as [x2 mx] eqn:Hul.
  destruct (analysed_keeps x x1 x2 _ i (dl x) j0 mx ou Han Hul)
    as (Hdl2 & Hlims2 & Hsaved2 & _ & _).
  destruct ou as [u|].
  - unfold assert_or_flip, jump_or_flip. cbn [set_mrk dl lims saved].
    rewrite Hdl2, Hlims2, Hsaved2, Hlims. reflexivity.
  - reflexivity.
Qed.

(* Below the current level, the stacks have an entry for level mx + 1. *)
Lemma level_at_below: forall (y: Ctx) (mx: nat),
  (mx < length (lims y))%nat -> length (saved y) = length (lims y) ->
  exists (j c0: nat) (st ls: list nat), LevelAt y mx j c0 st ls.
Proof.
  intros y mx Hmx Hslen.
  set (k := (length (lims y) - S mx)%nat).
  exists (nth k (lims y) 0%nat), (nth k (saved y) 0%nat), (skipn (S k) (saved y)),
    (skipn (S k) (lims y)).
  constructor.
  - assumption.
  - apply nth_error_nth'. unfold k. lia.
  - apply skipn_nth. unfold k. lia.
  - reflexivity.
Qed.

(* Below the current level, jump_or_flip goes back to level mx and asserts u. *)
Lemma jump_or_flip_below: forall (y: Ctx) (j0 mx j c0: nat) (st ls: list nat) (u: Lit),
  dl y = length (lims y) -> LevelAt y mx j c0 st ls ->
  jump_or_flip y j0 mx u =
    match push_reason (back y j c0 st mx ls) u with
    | (x4, r) => CNext (assign (x4 <| lower := [] |>) u r)
    end.
Proof.
  intros y j0 mx j c0 st ls u Hdl [Hmx Hj Hsv Hls].
  unfold jump_or_flip. rewrite Hdl.
  replace (mx <? length (lims y))%nat with true by (symmetry; now apply Nat.ltb_lt).
  rewrite Hj, Hsv, Hls. reflexivity.
Qed.

(* At or above the current level, jump_or_flip flips the last decision. *)
Lemma jump_or_flip_above: forall (y: Ctx) (j0 mx: nat) (u: Lit),
  (dl y <= mx)%nat -> jump_or_flip y j0 mx u = flip y j0.
Proof.
  intros y j0 mx u Hge. unfold jump_or_flip.
  replace (mx <? dl y)%nat with false by (symmetry; now apply Nat.ltb_ge).
  reflexivity.
Qed.


(* The test of resolve after the analysis and the unmarking: if (u >= 0) { ... }, and
   its then branch, when the analysis gave a literal u to assert. *)
Definition resolve_assert: statement := first_stmt (drop_stmts 6 (fn_body f_resolve)).
Definition resolve_unmark: statement := then_stmt resolve_assert.

(* Asserting the literal u the analysis gave, in the context y after unmarking the lower
   literals, with mx the highest level among them:

     {{ RepL y /\ lims y = j0 :: lims0 /\ saved y = c0 :: st /\ u in the temporaries }}
       s->mrk[u] = 0;                                                  (rep_store_mrk)
     {{ RepL y3, y3 = y <| mrk := tset (mrk y) (lit_key u) false |> }}
       if (mx < d) { ... }                         (level_at_below, resolve_jump_correct)
     {{ d <= mx }}
       ...                                                      (resolve_flip_correct)
     {{ ResolvePost (jump_or_flip y3 j0 mx u) }}                                   *)
Lemma resolve_unmark_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (y: Ctx) (lims0: list nat) (j0 c0 mx: nat) (st: list nat) (u: Lit) (P: mem -> Prop)
  (tp: nat -> Z) (le: temp_env) (m: mem),
  RepL m sh N lss y -> lims y = j0 :: lims0 -> saved y = c0 :: st -> LimsBelow y ->
  PoolArr m sh tp -> PoolFree sh N tp (wls y) -> (extract u < N)%nat -> (mx <= N)%nat ->
  le ! _s = Some (sptr sh) -> le ! _u = Some (vint (key u)) ->
  le ! _mx = Some (vnat mx) -> le ! _d = Some (vnat (length (j0 :: lims0))) ->
  le ! _lo = Some (vnat j0) ->
  Exec ge le m resolve_unmark
    (SeqK ge resolve_flip (Returns f_resolve (ResolvePost sh N lss P
       (jump_or_flip (y <| mrk := tset (mrk y) (lit_key u) false |>) j0 mx u)))).
Proof.
  intros sh N lss y lims0 j0 c0 mx st u P tp le m HRep Hlims_y Hsv Hlims Apool Hpool
    Hu Hmx Hs Hu' Hmx' Hd Hlo.
  pose proof (r_n HRep) as HN.
  pose proof (r_nodup HRep) as Hnd.
  pose proof (r_dl_le HRep) as Hdle.
  rewrite Hlims_y in Hdle.
  pose proof (key_small u N Hu HN) as Hku.
  pose proof (r_mrk HRep) as Fmrk.
  pose proof (a_mrk HRep) as Amrk.
  assert (Hk: (lit_key u < 2 * N)%nat) by (apply lit_key_lt; assumption).
  unfold resolve_unmark, resolve_assert, f_resolve.
  cbn [fn_body drop_stmts first_stmt then_stmt].
  (* s->mrk[u] = 0; *)
  run. store Amrk Hk as m3 Hst3.
  pose proof (rep_store_mrk m m3 (lit_key u) false HRep Hk Hst3) as HRep3.
  set (y3 := y <| mrk := tset (mrk y) (lit_key u) false |>) in HRep3 |- *.
  pose proof (r_dl_eq HRep3) as Hdl3.
  pose proof (r_saved_len HRep3) as Hslen3.
  assert (Hlims3: lims y3 = j0 :: lims0) by apply Hlims_y.
  assert (Apool3: PoolArr m3 sh tp).
  { apply (arr_store_other Apool Hst3). neq Hnd. }
  keep_mem m3.
  (* if (mx < d) *)
  eapply exec_if_lt.
  - ev.
  - ev.
  - reflexivity.
  - cbn [length] in *. lia.
  - (* below the current level: the backjump *)
    intros Hlt.
    assert (Hbelow: (mx < length (lims y3))%nat) by (rewrite Hlims3; lia).
    destruct (level_at_below y3 mx Hbelow Hslen3) as (j & c0' & st' & ls & Hlevel).
    rewrite (jump_or_flip_below y3 j0 mx j c0' st' ls u Hdl3 Hlevel).
    apply returns_seq.
    apply (resolve_jump_correct sh N lss y3 u mx j c0' st' ls P tp).
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + tmp.
    + tmp.
    + tmp.
  - (* at or above the current level: the flip *)
    intros Hge.
    rewrite jump_or_flip_above by (rewrite Hdl3, Hlims3; lia).
    apply exec_skip. normal.
    apply (resolve_flip_correct sh N lss y3 lims0 j0 c0 st P tp).
    + assumption.
    + assumption.
    + apply Hsv.
    + apply Hlims. rewrite Hlims_y. now left.
    + assumption.
    + assumption.
    + tmp.
    + tmp.
    + tmp.
Qed.


(* After the analysis gave ou and unmarking the lower literals gave the context y and the
   highest level mx among them:

     {{ RepL y /\ lims y = j0 :: lims0 /\ saved y = c0 :: st /\ u = enc_lit ou }}
       if (u >= 0) { ... }                                    (resolve_unmark_correct)
     {{ ou = None }}
     then, after the if:
       ...                                                      (resolve_flip_correct)
     {{ ResolvePost (assert_or_flip y j0 mx ou) }}                                 *)
Lemma resolve_assert_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (y: Ctx) (lims0: list nat) (j0 c0 mx: nat) (st: list nat) (ou: option Lit)
  (P: mem -> Prop) (tp: nat -> Z) (le: temp_env) (m: mem),
  RepL m sh N lss y -> lims y = j0 :: lims0 -> saved y = c0 :: st -> LimsBelow y ->
  PoolArr m sh tp -> PoolFree sh N tp (wls y) ->
  (forall (u: Lit), ou = Some u -> (extract u < N)%nat) -> (mx <= N)%nat ->
  le ! _s = Some (sptr sh) -> le ! _u = Some (vint (enc_lit ou)) ->
  le ! _mx = Some (vnat mx) -> le ! _d = Some (vnat (length (j0 :: lims0))) ->
  le ! _lo = Some (vnat j0) ->
  Exec ge le m resolve_assert
    (SeqK ge resolve_flip
       (Returns f_resolve (ResolvePost sh N lss P (assert_or_flip y j0 mx ou)))).
Proof.
  intros sh N lss y lims0 j0 c0 mx st ou P tp le m HRep Hlims_y Hsv Hlims Apool Hpool
    Hou Hmx Hs Hu' Hmx' Hd Hlo.
  pose proof (r_n HRep) as HN.
  unfold resolve_assert, f_resolve. cbn [fn_body drop_stmts first_stmt].
  (* if (u >= 0) *)
  eapply exec_if_ge.
  - ev.
  - ev.
  - reflexivity.
  - destruct ou as [u|].
    + pose proof (key_small u N (Hou u eq_refl) HN). cbn [enc_lit]. lia.
    + cbn [enc_lit]. lia.
  - intros Hnonneg. destruct ou as [u|].
    + (* a literal to assert *)
      apply (resolve_unmark_correct sh N lss y lims0 j0 c0 mx st u P tp).
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * apply Hou. reflexivity.
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * assumption.
    + (* enc_lit None is -1, not at least 0 *)
      cbn [enc_lit] in Hnonneg. lia.
  - intros Hneg. destruct ou as [u|].
    + (* the key of a literal is not negative *)
      pose proof (key_small u N (Hou u eq_refl) HN). cbn [enc_lit] in Hneg. lia.
    + (* nothing to assert: flip *)
      apply exec_skip. normal.
      apply (resolve_flip_correct sh N lss y lims0 j0 c0 st P tp).
      * assumption.
      * assumption.
      * assumption.
      * apply Hlims. rewrite Hlims_y. now left.
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * assumption.
Qed.

(* The statements of resolve after the analysis: from int mx = unmark_lower(s). *)
Definition resolve_unmark_lower: statement := drop_stmts 5 (fn_body f_resolve).

(* After the analysis of x with the decayed heuristic hd gave x1 and ou, with
   d = length (j0 :: lims0) decisions:

     {{ RepL x1, for analyze (x <| hr := hd |>) i d j0 = (x1, ou) }}
       int mx = unmark_lower(s);                                (unmark_lower_correct)
     {{ RepL x2, for unmark_lower x1 = (x2, mx), x2 with the levels of x }}
                                                                      (analysed_keeps)
       ...                                                    (resolve_assert_correct)
     {{ ResolvePost (assert_or_flip x2 j0 mx ou) }}                                *)
Lemma resolve_unmark_lower_correct: forall (sh: Shape) (N: nat)
  (lss: list (list Lit)) (x x1: Ctx) (hd: Heur) (i j0 c0: nat) (lims0 st: list nat)
  (ou: option Lit) (P: mem -> Prop) (tp: nat -> Z) (le: temp_env) (m: mem),
  RepL m sh N lss x1 ->
  analyze (x <| hr := hd |>) i (length (j0 :: lims0)) j0 = (x1, ou) ->
  (forall (u: Lit), ou = Some u -> (extract u < N)%nat) ->
  lims x = j0 :: lims0 -> saved x = c0 :: st -> LimsBelow x ->
  PoolArr m sh tp -> PoolFree sh N tp (wls x) ->
  le ! _s = Some (sptr sh) -> le ! _u = Some (vint (enc_lit ou)) ->
  le ! _d = Some (vnat (length (j0 :: lims0))) -> le ! _lo = Some (vnat j0) ->
  Exec ge le m resolve_unmark_lower
    (Returns f_resolve (ResolvePost sh N lss P
       (match unmark_lower x1 with
        | (x2, mx) => assert_or_flip x2 j0 mx ou
        end))).
Proof.
  intros sh N lss x x1 hd i j0 c0 lims0 st ou P tp le m HRep1 Han Hou Hlims_x Hsv Hlims
    Apool Hpool Hs Hu Hd Hlo.
  pose proof (r_nodup HRep1) as Hnd.
  unfold resolve_unmark_lower, f_resolve. cbn [fn_body drop_stmts].
  (* int mx = unmark_lower(s); *)
  run. call unmark_lower_fun (unmark_lower_correct sh N lss x1) by (apply HRep1).
  intros m2 v2 (-> & HRep2 & Hun2). normal. transfer Hun2 Hnd. keep_mem m2.
  (* the highest level among the lower literals is at most N *)
  assert (Hmx: (snd (unmark_lower x1) <= N)%nat).
  { apply unmark_lower_le. intros y Hy. apply (r_lvl_le HRep1).
    apply (r_lt_atoms HRep1). assumption. }
  destruct (unmark_lower x1) as [x2 mx] eqn:Hul.
  cbn [fst snd] in HRep2, Hmx |- *.
  (* x2 has the levels, the trail and the watch lists of x *)
  destruct (analysed_keeps x x1 x2 hd i (length (j0 :: lims0)) j0 mx ou Han Hul)
    as (_ & Hlims2 & Hsaved2 & Htlen2 & Hwls2).
  rewrite Hlims_x in Hlims2. rewrite Hsv in Hsaved2.
  (* if (u >= 0) { ... } and the flip *)
  run. apply (resolve_assert_correct sh N lss x2 lims0 j0 c0 mx st ou P tp).
  - apply HRep2.
  - assumption.
  - assumption.
  - (* the decision positions of x2 are those of x, on its trail *)
    intros j Hj. rewrite Htlen2. apply Hlims.
    rewrite Hlims_x, <- Hlims2. assumption.
  - assumption.
  - rewrite Hwls2. assumption.
  - assumption.
  - assumption.
  - tmp.
  - tmp.
  - tmp.
  - tmp.
  - tmp.
Qed.

(* The analysis: the statements of resolve after decay. *)
Definition resolve_analysis: statement := drop_stmts 3 (fn_body f_resolve).

(* After decay, with hd = decay (hr x) N and d = length (j0 :: lims0) decisions:

     {{ RepL (x <| hr := hd |>) /\ lims x = j0 :: lims0 /\ lower x = [] /\ the decision
        positions are on the trail /\ i < length lss }}
       int lo = s->lims[d - 1];
       int u = analyze(s, i, d, lo);                                 (analyze_correct)
     {{ RepL x1, for analyze (x <| hr := hd |>) i d j0 = (x1, ou) }}
       ...                                              (resolve_unmark_lower_correct)
     {{ ResolvePost (assert_or_flip x2 j0 mx ou), for unmark_lower x1 = (x2, mx),
        which is ResolvePost (resolve x i) }}                       (resolve_parts) *)
Lemma resolve_analysis_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (j0: nat) (lims0: list nat) (i: nat) (P: mem -> Prop) (tp: nat -> Z)
  (le: temp_env) (m: mem),
  RepL m sh N lss (x <| hr := decay (hr x) N |>) -> lims x = j0 :: lims0 ->
  lower x = [] ->
  PoolArr m sh tp ->
  PoolFree sh N tp (wls x) ->
  LimsBelow x -> (i < length lss)%nat ->
  le ! _s = Some (sptr sh) -> le ! _i = Some (vnat i) ->
  le ! _d = Some (vnat (length (j0 :: lims0))) ->
  Exec ge le m resolve_analysis
    (Returns f_resolve (ResolvePost sh N lss P (resolve x i))).
Proof.
  intros sh N lss x j0 lims0 i P tp le m HRep Hlims_x Hlower Apool Hpool Hlims Hi Hs Hi'
    Hd.
  set (hd := decay (hr x) N) in HRep.
  pose proof (r_n HRep) as HN.
  pose proof (r_nodup HRep) as Hnd.
  pose proof (r_dl_eq HRep) as Hdl.
  pose proof (r_dl_le HRep) as Hdle.
  pose proof (r_tlen_le HRep) as Htlen.
  pose proof (r_saved_len HRep) as Hslen.
  pose proof (r_nvars HRep) as Hnv.
  cbn [set_hr dl lims tlen saved nvars] in Hdl, Hdle, Htlen, Hslen, Hnv.
  rewrite Hlims_x in Hdle, Hslen. cbn [length] in Hdle.
  rewrite (resolve_parts x i j0 lims0 Hlims_x), Hdl, Hnv, Hlims_x. fold hd.
  assert (Hj0: (j0 < tlen x)%nat) by (apply Hlims; rewrite Hlims_x; now left).
  (* a cursor is saved for each decision *)
  assert (Hsv: exists (c0: nat) (st: list nat), saved x = c0 :: st).
  { destruct (saved x) as [|c0 st].
    - cbn [length] in Hslen. lia.
    - exists c0, st. reflexivity. }
  destruct Hsv as (c0 & st & Hsv).
  (* the last decision position j0, as the array holds it: entry d - 1, oldest first *)
  pose proof (r_lims HRep) as Flims.
  pose proof (a_lims HRep) as (tl & Alims & Htl).
  cbn [set_hr lims] in Htl. rewrite Hlims_x in Htl.
  assert (Hsub: Int.sub (Int.repr (Z.of_nat (length (j0 :: lims0)))) (Int.repr 1)
                = Int.repr (Z.of_nat (length lims0))).
  { rewrite sub_repr. f_equal. cbn [length]. lia. }
  assert (Htj0: tl (length lims0) = Z.of_nat j0).
  { rewrite Htl by (cbn [length]; lia). cbn [rev].
    rewrite <- length_rev, nth_middle. reflexivity. }
  unfold resolve_analysis, f_resolve. cbn [fn_body drop_stmts].
  (* int lo = s->lims[d - 1]; int u = analyze(s, i, d, lo); *)
  run. rewrite Htj0.
  call analyze_fun
    (analyze_correct sh N lss (x <| hr := hd |>) i (length (j0 :: lims0)) j0).
  - splits.
    + apply HRep.
    + assumption.
    + cbn [length]. lia.
    + lia.
  - intros m1 v1 Hpost. normal. unfold AnalyzePost in Hpost.
    destruct (analyze (x <| hr := hd |>) i (length (j0 :: lims0)) j0) as [x1 ou] eqn:Han.
    destruct Hpost as (Hou & -> & HRep1 & Hun1). transfer Hun1 Hnd. keep_mem m1.
    eapply exec_set.
    + ev.
    + normal.
      (* int mx = unmark_lower(s); ... *)
      apply (resolve_unmark_lower_correct sh N lss x x1 hd i j0 c0 lims0 st ou P tp).
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * tmp.
      * tmp.
      * tmp.
      * tmp.
Qed.

(* resolve resolves the conflict on clause i:

     {{ Rep x /\ the decision positions are on the trail /\ i < length lss }}
       int d = s->dl;
       if (d == 0) return 1;
     {{ result = 1: no decision, fail }}
       decay(s);                                                       (decay_correct)
     {{ RepL (x <| hr := hd |>), for hd = decay (hr x) N }}
       ...                                                  (resolve_analysis_correct)
     {{ ResolvePost (resolve x i) }}                                               *)
Lemma resolve_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (i: nat) (P: mem -> Prop),
  {{ m | Rep m sh N lss x /\ (LimsBelow x) /\
         (i < length lss)%nat }}
    f_resolve(sptr sh, vnat i)
  {{ m', v | ResolvePost sh N lss P (resolve x i) m' v }}.
Proof.
  intros sh N lss x i P m [[HRep [Hlower [tp [Apool Hpool]]]] [Hlims Hi]].
  pose proof (r_n HRep) as HN.
  pose proof (r_nodup HRep) as Hnd.
  pose proof (r_dl_le HRep) as Hdle.
  pose proof (r_dl HRep) as Fdl.
  remember (resolve x i) as cr eqn:Hcr.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_resolve. cbn [fn_body fn_return].
    (* int d = s->dl; if (d == 0) return 1; *)
    run. branch.
    + (* no decision: fail *)
      intros Hzero.
      assert (Hnil: lims x = []) by (apply length_zero_iff_nil; lia).
      return_int.
      right. rewrite Hcr. unfold resolve. rewrite Hnil. reflexivity.
    + intros Hnonzero. destruct (lims x) as [|j0 lims0] eqn:Hlims_x.
      * (* no decision is level 0 *)
        cbn [length] in Hnonzero. lia.
      * apply exec_skip. normal.
        (* decay(s); *)
        run. call decay_fun (decay_correct sh N lss x) by (apply HRep).
        intros m0 v0 [HRep0 Hun0]. normal. transfer Hun0 Hnd. keep_mem m0.
        rewrite Hcr.
        apply (resolve_analysis_correct sh N lss x j0 lims0 i P tp).
        -- apply HRep0.
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- rewrite Hlims_x. assumption.
        -- assumption.
        -- tmp.
        -- tmp.
        -- tmp.
Qed.

Lemma resolve_fun: FunAt _resolve f_resolve.
Proof. apply find_fun. reflexivity. Qed.
