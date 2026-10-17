(* resolve resolves a conflict (resolve_t): it fails without decisions; otherwise it
   analyses the conflict and backjumps, asserting the literal the analysis gives with the
   analysed clause as its reason, or flips the last decision; or it gives up. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Propagate Analysis Step CStep
  SolverStep.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep Assign Cut Analyze
  UnmarkLower PushReason.
Import ListNotations.

(* What C returns and leaves for an outcome of a step on the context: 0 to stop with P of
   the memory, 1 to fail, and 2 with the next context in memory. *)
Definition COutcome (S: Shape) (N: nat) (lss: list (list Lit)) (P: mem -> Prop)
  (cr: CResult) (m: mem) (v: val): Prop :=
match cr with
| CStop          => v = vint 0 /\ P m
| CFail          => v = vint 1
| CNext x' lims' => v = vint 2 /\ Rep m S N lss x' lims'
end.

(* What resolve returns: -1 when out of room, or the outcome cr. *)
Definition ResolvePost (S: Shape) (N: nat) (lss: list (list Lit)) (P: mem -> Prop)
  (cr: CResult) (m': mem) (v: val): Prop :=
  v = vint (-1) \/ COutcome S N lss P cr m' v.

(* Pushing a reason clause keeps the watch lists. *)
Lemma push_reason_wls: forall (y: Ctx) (u: Lit) (lt: list Lit),
  wls (fst (push_reason y u lt)) = wls y.
Proof.
  intros y u lt. unfold push_reason. destruct (_ && _).
  - reflexivity.
  - reflexivity.
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

(* The highest level unmark_lower finds is at most a bound on the levels of lt. *)
Lemma unmark_lower_le: forall (lv: Table nat) (mk: Table bool) (mx B: nat)
  (lt: list Lit),
  (mx <= B)%nat -> (forall (y: Lit), In y lt -> (tget lv (extract y) <= B)%nat) ->
  (snd (unmark_lower lv mk mx lt) <= B)%nat.
Proof.
  intros lv mk mx B lt. revert mk mx. induction lt as [|y lt IH]; intros mk mx Hmx Hlt.
  - assumption.
  - cbn [unmark_lower]. apply IH.
    + assert (tget lv (extract y) <= B)%nat by (apply Hlt; now left). lia.
    + intros y' Hy'. apply Hlt. now right.
Qed.

(* The end of both ways on: the assignment of the literal to assert, done by assign whose
   result is in temporary tw:

     {{ the result w of assign: 0, or 1 with RepB x' lims' /\ Arr pool tp }}
       if (!w) return -1;
       return 2;
     {{ ResolvePost (CNext x' lims') }}                                              *)
Lemma resolve_assigned: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (P: mem -> Prop) (x': Ctx) (lims': list nat) (tp: nat -> Z) (tw: ident) (w: val)
  (le: temp_env) (m: mem),
  le ! tw = Some w ->
  (w = vint 0 \/ (w = vint 1 /\ RepB m S N lss x' lims' /\
                  Arr m (b_wpool S) (2 * npool S) tp)) ->
  PoolOf S N tp (wls x') (fun (_ _: nat) => False) ->
  Exec ge le m
    (Sifthenelse (Eunop Onotbool (Etempvar tw Ctypesdefs.tint) Ctypesdefs.tint)
       (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) Ctypesdefs.tint)
                         Ctypesdefs.tint)))
       Sskip)
    (SeqK ge (Sreturn (Some (Econst_int (Int.repr 2) Ctypesdefs.tint)))
       (Returns f_resolve (ResolvePost S N lss P (CNext x' lims')))).
Proof.
  intros S N lss P x' lims' tp tw w le m Htw Hw Hpool.
  destruct Hw as [-> | (-> & HRep & Apool)].
  - (* out of room: return -1; *)
    eapply (exec_if_int _ _ _ _ 1).
    + ev.
    + reflexivity.
    + unfold Small. lia.
    + change (negb (Z.eqb 1 0)) with true. cbv beta iota. eapply exec_return.
      * ev.
      * ret. exists (vint (-1)). split.
        -- apply result_int.
        -- now left.
  - (* return 2; with the next context *)
    eapply (exec_if_int _ _ _ _ 0).
    + ev.
    + reflexivity.
    + unfold Small. lia.
    + change (negb (Z.eqb 0 0)) with false. cbv beta iota. apply exec_skip. normal.
      eapply exec_return.
      * ev.
      * exists (vint 2). split.
        -- apply result_int.
        -- right. split.
           ++ reflexivity.
           ++ split.
              ** assumption.
              ** exists tp. split.
                 --- assumption.
                 --- assumption.
Qed.

(* The statements of resolve after the backjump: flipping the last decision. *)
Definition resolve_flip: statement := drop_stmts 6 (fn_body f_resolve).

(* Flipping the last decision, at trail position j0, with the cursor c0 saved for it,
   after the analysis left the marks mk2 and the lower literals lt:

     {{ RepL (set_mrk x mk2) (j0 :: lims0) lt /\ saved x = c0 :: st }}
       s->ltlen = 0;                                              (rep_store_ltlen_zero)
       int l = s->tr[lo];
       cut(s, lo);                                                       (cut_correct)
     {{ RepB (jump x v1 j0 (cur x) (saved x) (dl x) mk2) (j0 :: lims0) }}
       s->cur = s->saved[d - 1];
       s->dl = d - 1;                                                  (rep_store_level)
     {{ RepB (jump x v1 j0 c0 st (dl x - 1) mk2) lims0 }}
       if (!assign(s, l ^ 1, 0)) return -1;                           (assign_correct)
       return 2;                                                      (resolve_assigned)
     {{ ResolvePost (flip_t x j0 lims0 mk2) }}

   where v1 = unset_range (vals x) (tr x) j0 (tlen x - j0) and l = tget (tr x) j0. *)
Lemma resolve_flip_correct {lt: list Lit}: forall (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims0: list nat) (j0 c0: nat) (st: list nat)
  (mk2: Table bool) (P: mem -> Prop) (tp: nat -> Z) (le: temp_env) (m: mem),
  RepL m S N lss (set_mrk x mk2) (j0 :: lims0) lt -> Arr m (b_wpool S) (2 * npool S) tp
    ->
  PoolOf S N tp (wls x) (fun (_ _: nat) => False) -> (j0 < tlen x)%nat ->
  saved x = c0 :: st -> le ! _s = Some (sptr S) -> le ! _lo = Some (vint (Z.of_nat j0))
    ->
  le ! _d = Some (vint (Z.of_nat (length (j0 :: lims0)))) ->
  Exec ge le m resolve_flip
    (Returns f_resolve (ResolvePost S N lss P (flip_t x j0 lims0 mk2))).
Proof.
  intros S N lss x lims0 j0 c0 st mk2 P tp le m HRep Apool Hpool Hj0 Hsv Hs Hlo Hd.
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_dl_eq _ _ _ _ _ _ _ HRep) as Hdl. cbn [set_mrk dl length] in Hdl.
  pose proof (r_saved_len _ _ _ _ _ _ _ HRep) as Hslen.
  cbn [set_mrk saved length] in Hslen. rewrite Hsv in Hslen. cbn [length] in Hslen.
  pose proof (r_ltlen _ _ _ _ _ _ _ HRep) as Fltlen.
  pose proof (r_tlen_le _ _ _ _ _ _ _ HRep) as Htlen. cbn [set_mrk tlen] in Htlen.
  pose proof (r_dl_le _ _ _ _ _ _ _ HRep) as Hdle. cbn [length] in Hdle.
  assert (Hl: (extract (tget (tr x) j0) < N)%nat).
  { pose proof (r_tr_atoms _ _ _ _ _ _ _ HRep j0) as Hat. cbn [set_mrk tr tlen] in Hat.
    apply Hat. assumption. }
  pose proof (key_small _ N Hl HN) as Hkl.
  assert (Hxor: Int.xor (Int.repr (key (tget (tr x) j0))) (Int.repr 1)
                = Int.repr (key (¬(tget (tr x) j0)))).
  { apply xor_key. lia. }
  assert (Hnl: (extract (¬(tget (tr x) j0)) < N)%nat) by (now destruct (tget (tr x) j0)).
  assert (Hsub: Int.sub (Int.repr (Z.of_nat (length (j0 :: lims0)))) (Int.repr 1)
                = Int.repr (Z.of_nat (length st))).
  { rewrite sub_repr. f_equal. cbn [length]. lia. }
  unfold resolve_flip, f_resolve. cbn [fn_body drop_stmts].
  (* s->ltlen = 0; *)
  run. eapply exec_store.
  - evl.
  - ev.
  - reflexivity.
  - reflexivity.
  - fofs. bound.
  - fofs. cbn [cast_int_int].
    destruct (fld_storable m (b_s S) 184 Mint32 _ (vint 0) Fltlen) as [m1 Hst1].
    exists m1. split.
    + apply Hst1.
    + normal.
      pose proof (rep_store_ltlen_zero m m1 S N lss _ _ HRep Hst1) as HRep1.
      assert (Apool1: Arr m1 (b_wpool S) (2 * npool S) tp).
      { apply (arr_store_other _ _ _ _ _ _ _ _ _ Apool Hst1). neq Hnd. }
      keep_mem m1.
      pose proof (r_tr _ _ _ _ _ _ _ HRep1) as Ftr1.
      pose proof (a_tr _ _ _ _ _ _ _ HRep1) as Atr1. cbn [set_mrk tr] in Atr1.
      (* int l = s->tr[lo]; cut(s, lo); *)
      run. call cut_fun. eapply call_weaken.
      { apply (cut_correct (lt := []) S N lss (set_mrk x mk2) (j0 :: lims0) j0 tp m1).
        split.
        - assumption.
        - split.
          + cbn [set_mrk tlen]. lia.
          + assumption. }
      intros m2 v [HRep2 Apool2]. normal. keep_mem m2.
      set (v1 := unset_range (vals x) (tr x) j0 (tlen x - j0)) in HRep2.
      pose proof (r_cur _ _ _ _ _ _ _ HRep2) as Fcur2.
      pose proof (r_dl _ _ _ _ _ _ _ HRep2) as Fdl2.
      pose proof (r_saved _ _ _ _ _ _ _ HRep2) as Fsaved2.
      pose proof (a_saved _ _ _ _ _ _ _ HRep2) as (tsv & Asaved & Htsv).
      cbn [jump set_mrk saved] in Htsv. rewrite Hsv in Htsv. cbn [length] in Htsv.
      assert (Htc0: tsv (length st) = Z.of_nat c0).
      { rewrite Htsv by lia. cbn [rev]. rewrite <- length_rev, nth_middle. reflexivity. }
      (* s->cur = s->saved[d - 1]; *)
      run. rewrite Htc0. eapply exec_store.
      * evl.
      * ev.
      * reflexivity.
      * reflexivity.
      * fofs. bound.
      * fofs. cbn [cast_int_int].
        destruct (fld_storable m2 (b_s S) 116 Mint32 _ (vint (Z.of_nat c0)) Fcur2)
          as [m3 Hst3].
        exists m3. split.
        -- apply Hst3.
        -- normal.
          assert
                          (Fdl3: Fld m3 (b_s S) 136 Mint32 (vint (Z.of_nat (length
                            (j0 :: lims0))))).
          { apply (fld_store_other _ _ _ _ _ _ _ _ _ _ Fdl2 Hst3). right.
            cbn [size_chunk]. lia. }
          (* s->dl = d - 1; *)
          run. eapply exec_store.
          ++ evl.
          ++ ev.
          ++ reflexivity.
          ++ reflexivity.
          ++ fofs. bound.
          ++ fofs. cbn [cast_int_int]. ints.
             destruct (fld_storable m3 (b_s S) 136 Mint32 _ (vint (Z.of_nat (length st)))
                         Fdl3) as [m4 Hst4].
             exists m4. split.
             ** apply Hst4.
             ** normal.
                pose proof (rep_store_level m2 m3 m4 S N lss _ (j0 :: lims0) 0 c0 st
                  HRep2
                              Hsv Hst3 Hst4) as HRep4.
                cbn [skipn] in HRep4.
                (* the context after the jump, as flip_t has it *)
                assert (HRep4': RepB m4 S N lss (jump x v1 j0 c0 st (dl x - 1) mk2)
                  lims0).
                { replace (dl x - 1)%nat with (length st) by lia. apply HRep4. }
                assert (Apool3: Arr m3 (b_wpool S) (2 * npool S) tp).
                { apply (arr_store_other _ _ _ _ _ _ _ _ _ Apool2 Hst3). neq Hnd. }
                assert (Apool4: Arr m4 (b_wpool S) (2 * npool S) tp).
                { apply (arr_store_other _ _ _ _ _ _ _ _ _ Apool3 Hst4). neq Hnd. }
                keep_mem m4.
                (* if (!assign(s, l ^ 1, 0)) return -1; return 2; *)
                run. call assign_fun. cbn [cast_int_int]. ints. eapply call_weaken.
                --- apply (assign_correct S N lss (jump x v1 j0 c0 st (dl x - 1) mk2)
                  lims0
                             (¬(tget (tr x) j0)) no_reason tp m4).
                    split.
                    +++ apply HRep4'.
                    +++ split.
                        *** assumption.
                        *** split.
                            ---- constructor.
                            ---- assumption.
                --- intros m5 w Hw. normal. unfold flip_t. rewrite Hsv.
                    apply (resolve_assigned S N lss P _ lims0 tp _t'5 w).
                    +++ tmp.
                    +++ assumption.
                    +++ assumption.
Qed.

(* The backjump: the statements of resolve when the analysis gives a literal to assert
   below the current level. *)
Definition resolve_jump: statement :=
  then_stmt (drop_stmts 1 (then_stmt (first_stmt (drop_stmts 5 (fn_body f_resolve))))).

(* Jumping back to level mx, below the current one, and asserting u, with the marks mk2
   and the lower literals lt the analysis left. The decision of level mx + 1 is at trail
   position j, and c0 is the cursor saved for it; st are the cursors saved before it:

     {{ RepL (set_mrk x mk2) lims lt /\ mx < length lims /\ u in the temporaries }}
       cut(s, s->lims[mx]);                                              (cut_correct)
       s->cur = s->saved[mx];
       s->dl = mx;                                                     (rep_store_level)
     {{ RepL (jump x v1 j c0 st mx mk2) lims' lt }}
       int r = push_reason(s, u);                                (push_reason_correct)
     {{ RepL x1 lims' lt, for push_reason (jump ...) u lt = (x1, r) }}
       s->ltlen = 0;                                              (rep_store_ltlen_zero)
       if (!assign(s, u, r)) return -1;                               (assign_correct)
       return 2;                                                      (resolve_assigned)
     {{ ResolvePost (CNext (assign x1 u r) lims') }}

   where v1 = unset_range (vals x) (tr x) j (tlen x - j), k = length lims - (mx + 1)
   and lims' = skipn (k + 1) lims, the positions of the levels up to mx. *)
Lemma resolve_jump_correct {lt: list Lit}: forall (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (mk2: Table bool) (u: Lit)
  (mx j c0: nat) (st: list nat) (P: mem -> Prop) (tp: nat -> Z) (le: temp_env) (m: mem),
  RepL m S N lss (set_mrk x mk2) lims lt -> Arr m (b_wpool S) (2 * npool S) tp ->
  PoolOf S N tp (wls x) (fun (_ _: nat) => False) ->
  (forall (j': nat), In j' lims -> (j' < tlen x)%nat) -> (mx < length lims)%nat ->
  (extract u < N)%nat ->
  nth_error lims (length lims - Datatypes.S mx) = Some j ->
  skipn (length lims - Datatypes.S mx) (saved x) = c0 :: st ->
  le ! _s = Some (sptr S) -> le ! _u = Some (vint (key u)) ->
  le ! _mx = Some (vint (Z.of_nat mx)) ->
  Exec ge le m resolve_jump
    (Returns f_resolve (ResolvePost S N lss P
       (match push_reason (jump x (unset_range (vals x) (tr x) j (tlen x - j)) j c0 st mx
                             mk2) u lt with
        | (x1, r) => CNext (assign x1 u r)
                       (skipn (Datatypes.S (length lims - Datatypes.S mx)) lims)
        end))).
Proof.
  intros S N lss x lims mk2 u mx j c0 st P tp le m HRep Apool Hpool Hlims Hmx Hu Hj Hsv
    Hs Hu' Hmx'.
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_saved_len _ _ _ _ _ _ _ HRep) as Hslen. cbn [set_mrk saved] in Hslen.
  pose proof (r_dl_le _ _ _ _ _ _ _ HRep) as Hdle.
  pose proof (r_tlen_le _ _ _ _ _ _ _ HRep) as Htlen. cbn [set_mrk tlen] in Htlen.
  pose proof (key_small u N Hu HN) as Hku.
  set (k := (length lims - Datatypes.S mx)%nat) in *.
  (* The decision of level mx + 1: entry mx of the arrays, oldest first. *)
  assert (Hjin: In j lims) by (apply nth_error_In with k; assumption).
  assert (Hjt: (j < tlen x)%nat) by (apply Hlims; assumption).
  assert (Hst: length st = mx).
  { assert (Hlen: length (skipn k (saved x)) = Datatypes.S (length st))
      by (rewrite Hsv; reflexivity).
    rewrite length_skipn in Hlen. unfold k in Hlen. lia. }
  assert (Hlj: nth mx (rev lims) 0%nat = j).
  { rewrite rev_nth by assumption. fold k. apply nth_error_nth. assumption. }
  assert (Hsc0: nth mx (rev (saved x)) 0%nat = c0).
  { rewrite rev_nth by lia. rewrite Hslen. fold k.
    rewrite (skipn_nth (saved x) 0%nat k) in Hsv by lia. injection Hsv as Hc0 _.
    assumption. }
  pose proof (r_lims _ _ _ _ _ _ _ HRep) as Flims.
  pose proof (a_lims _ _ _ _ _ _ _ HRep) as (tl & Alims & Htl).
  unfold resolve_jump, f_resolve.
  cbn [fn_body drop_stmts first_stmt then_stmt].
  (* cut(s, s->lims[mx]); *)
  run. rewrite (Htl mx Hmx), Hlj. call cut_fun. eapply call_weaken.
  { apply (cut_correct (lt := lt) S N lss (set_mrk x mk2) lims j tp m). split.
    - assumption.
    - split.
      + cbn [set_mrk tlen]. lia.
      + assumption. }
  intros m1 v [HRep1 Apool1]. normal. keep_mem m1.
  set (v1 := unset_range (vals x) (tr x) j (tlen x - j)).
  pose proof (r_cur _ _ _ _ _ _ _ HRep1) as Fcur1.
  pose proof (r_dl _ _ _ _ _ _ _ HRep1) as Fdl1.
  pose proof (r_saved _ _ _ _ _ _ _ HRep1) as Fsaved1.
  pose proof (a_saved _ _ _ _ _ _ _ HRep1) as (tsv & Asaved & Htsv).
  cbn [jump set_mrk saved] in Htsv.
  (* s->cur = s->saved[mx]; *)
  run. rewrite (Htsv mx) by lia. rewrite Hsc0. eapply exec_store.
  - evl.
  - ev.
  - reflexivity.
  - reflexivity.
  - fofs. bound.
  - fofs. cbn [cast_int_int].
    destruct (fld_storable m1 (b_s S) 116 Mint32 _ (vint (Z.of_nat c0)) Fcur1)
      as [m2 Hst2].
    exists m2. split.
    + apply Hst2.
    + normal.
      assert (Fdl2: Fld m2 (b_s S) 136 Mint32 (vint (Z.of_nat (length lims)))).
      { apply (fld_store_other _ _ _ _ _ _ _ _ _ _ Fdl1 Hst2). right.
        cbn [size_chunk]. lia. }
      (* s->dl = mx; *)
      run. eapply exec_store.
      * evl.
      * ev.
      * reflexivity.
      * reflexivity.
      * fofs. bound.
      * fofs. cbn [cast_int_int]. rewrite <- Hst.
        destruct (fld_storable m2 (b_s S) 136 Mint32 _ (vint (Z.of_nat (length st)))
                    Fdl2) as [m3 Hst3].
        exists m3. split.
        -- apply Hst3.
        -- normal.
           pose proof (rep_store_level m1 m2 m3 S N lss _ lims k c0 st HRep1 Hsv Hst2
                         Hst3) as HRep3.
           (* the context after the jump, as resolve_t has it, at level mx = length st *)
           set (xj := jump x v1 j c0 st (length st) mk2).
           assert (HRep3': RepL m3 S N lss xj (skipn (Datatypes.S k) lims) lt).
           { apply HRep3. }
           assert (Apool2: Arr m2 (b_wpool S) (2 * npool S) tp).
           { apply (arr_store_other _ _ _ _ _ _ _ _ _ Apool1 Hst2). neq Hnd. }
           assert (Apool3: Arr m3 (b_wpool S) (2 * npool S) tp).
           { apply (arr_store_other _ _ _ _ _ _ _ _ _ Apool2 Hst3). neq Hnd. }
           keep_mem m3.
           (* int r = push_reason(s, u); *)
           run. call push_reason_fun. eapply call_weaken.
           ++ apply (push_reason_correct (lt := lt) S N lss xj (skipn (Datatypes.S k)
             lims)
                       u).
              split.
              ** assumption.
              ** assumption.
           ++ intros m4 w (HRep4 & -> & Hr & Hun4). normal.
              transfer Hun4 Hnd. keep_mem m4.
              assert (Hwls: wls (fst (push_reason xj u lt)) = wls x)
                by (rewrite push_reason_wls; reflexivity).
              destruct (push_reason xj u lt) as [x1 r] eqn:Hpush.
              cbn [fst snd] in HRep4, Hr, Hwls.
              pose proof (r_ltlen _ _ _ _ _ _ _ HRep4) as Fltlen4.
              (* s->ltlen = 0; *)
              run. eapply exec_store.
              ** evl.
              ** ev.
              ** reflexivity.
              ** reflexivity.
              ** fofs. bound.
              ** fofs. cbn [cast_int_int].
                 destruct (fld_storable m4 (b_s S) 184 Mint32 _ (vint 0) Fltlen4)
                   as [m5 Hst5].
                 exists m5. split.
                 --- apply Hst5.
                 --- normal.
                     pose proof (rep_store_ltlen_zero m4 m5 S N lss _ _ HRep4 Hst5)
                       as HRep5.
                     assert (Apool5: Arr m5 (b_wpool S) (2 * npool S) tp).
                     { apply (arr_store_other _ _ _ _ _ _ _ _ _ Apool3 Hst5). neq Hnd. }
                     keep_mem m5.
                     (* if (!assign(s, u, r)) return -1; return 2; *)
                     run. call assign_fun. eapply call_weaken.
                     +++ apply (assign_correct S N lss x1 (skipn (Datatypes.S k) lims) u
                       r
                                  tp m5).
                         split.
                         *** assumption.
                         *** split.
                             ---- assumption.
                             ---- split.
                                  ++++ assumption.
                                  ++++ assumption.
                     +++ intros m6 w Hw. normal.
                         apply (resolve_assigned S N lss P _ _ tp _t'4 w).
                         *** tmp.
                         *** assumption.
                         *** cbn [assign wls]. rewrite Hwls. assumption.
Qed.

(* resolve resolves the conflict on clause i:

     {{ Rep x lims /\ the decision positions are on the trail /\ i < length lss }}
       int d = s->dl;
       if (d == 0) return 1;
     {{ result = 1: no decision, fail }}
       int lo = s->lims[d - 1];
       int u = analyze(s, i, d, lo);                                 (analyze_correct)
       int mx = unmark_lower(s);                                (unmark_lower_correct)
     {{ the result (mk2, mx) of clear_marks, but the mark of u }}
       if (u >= 0) {
         s->mrk[u] = 0;                                                  (rep_store_mrk)
     {{ RepL (set_mrk x mk2) lims lt, (mk2, mx) = clear_marks ... }}
         if (mx < d) { ... }                                    (resolve_jump_correct)
       }
       ...                                                      (resolve_flip_correct)
     {{ ResolvePost (resolve_t x lims i) }}                                          *)
Lemma resolve_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (i: nat) (P: mem -> Prop),
  {{ m | Rep m S N lss x lims /\ (forall (j: nat), In j lims -> (j < tlen x)%nat) /\
         (i < length lss)%nat }}
    f_resolve(sptr S, vint (Z.of_nat i))
  {{ m', v | v = vint (-1) \/ COutcome S N lss P (resolve_t x lims i) m' v }}.
Proof.
  intros S N lss x lims i P m [[HRep [tp [Apool Hpool]]] [Hlims Hi]].
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_dl_eq _ _ _ _ _ _ _ HRep) as Hdl.
  pose proof (r_dl_le _ _ _ _ _ _ _ HRep) as Hdle.
  pose proof (r_tlen_le _ _ _ _ _ _ _ HRep) as Htlen.
  pose proof (r_saved_len _ _ _ _ _ _ _ HRep) as Hslen.
  pose proof (r_dl _ _ _ _ _ _ _ HRep) as Fdl.
  remember (resolve_t x lims i) as cr eqn:Hcr.
  change (fun (m' : mem) (v : val) => v = vint (-1) \/ COutcome S N lss P cr m' v)
    with (ResolvePost S N lss P cr).
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_resolve. cbn [fn_body fn_return].
    (* int d = s->dl; if (d == 0) return 1; *)
    run. eapply (exec_if_cmp _ _ _ Ceq).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + unfold Small. lia.
    + unfold Small. lia.
    + destruct lims as [|j0 lims0].
      * (* no decision: fail *)
        cbv beta iota. eapply exec_return.
        -- ev.
        -- ret. exists (vint 1). split.
           ++ apply result_int.
           ++ right. rewrite Hcr. reflexivity.
      * replace (zcmp Ceq (Z.of_nat (length (j0 :: lims0))) 0) with false
          by (cbn [zcmp length]; symmetry; apply Z.eqb_neq; lia).
        cbv beta iota. apply exec_skip. normal.
        unfold resolve_t in Hcr. rewrite Hdl in Hcr. cbn [length] in Hdle.
        assert (Hj0: (j0 < tlen x)%nat) by (apply Hlims; now left).
        pose proof (r_lims _ _ _ _ _ _ _ HRep) as Flims.
        pose proof (a_lims _ _ _ _ _ _ _ HRep) as (tl & Alims & Htl).
        assert (Hsub: Int.sub (Int.repr (Z.of_nat (length (j0 :: lims0)))) (Int.repr 1)
                      = Int.repr (Z.of_nat (length lims0))).
        { rewrite sub_repr. f_equal. cbn [length]. lia. }
        assert (Htj0: tl (length lims0) = Z.of_nat j0).
        { rewrite Htl by (cbn [length]; lia). cbn [rev].
          rewrite <- length_rev, nth_middle. reflexivity. }
        (* int lo = s->lims[d - 1]; int u = analyze(s, i, d, lo); *)
        run. rewrite Htj0. call analyze_fun. eapply call_weaken.
        { apply (analyze_correct S N lss x (j0 :: lims0) i (length (j0 :: lims0)) j0).
          split.
          - assumption.
          - split.
            + assumption.
            + split.
              * assumption.
              * lia. }
        intros m1 v1 Hpost. normal. unfold AnalyzePost in Hpost.
        destruct (analyze x i (length (j0 :: lims0)) j0) as [[ou mk] lt] eqn:Han.
        destruct Hpost as (-> & HRep1 & Hou & Hun1). transfer Hun1 Hnd. keep_mem m1.
        (* int mx = unmark_lower(s); *)
        run. call unmark_lower_fun. eapply call_weaken.
        { apply (unmark_lower_correct (lt := lt) S N lss (set_mrk x mk) (j0 :: lims0)
          m1).
          assumption. }
        intros m2 v2 (HRep2 & -> & Hun2). normal. transfer Hun2 Hnd. keep_mem m2.
        cbn [set_mrk lvl mrk] in HRep2.
        change (lvl (set_mrk x mk)) with (lvl x). change (mrk (set_mrk x mk)) with mk.
        unfold clear_marks in Hcr.
        (* the highest level among lt is at most N *)
        assert (Hmx: (snd (unmark_lower (lvl x) mk 0 lt) <= N)%nat).
        { apply unmark_lower_le.
          - lia.
          - intros y Hy. apply (r_lvl_le _ _ _ _ _ _ _ HRep).
            apply (r_lt_atoms _ _ _ _ _ _ _ HRep1). assumption. }
        destruct (unmark_lower (lvl x) mk 0 lt) as [mk1 mx] eqn:Hul.
        cbn [fst snd] in HRep2, Hmx |- *.
        destruct (saved x) as [|c0 st] eqn:Hsv.
        { cbn [length] in Hslen. lia. }
        (* if (u >= 0) *)
        run. eapply (exec_if_cmp _ _ _ Cge).
        -- ev.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- destruct ou as [u|].
           ++ pose proof (Hou u eq_refl) as Hu. pose proof (key_small u N Hu HN).
              unfold Small. cbn [enc_lit]. lia.
           ++ unfold Small. cbn [enc_lit]. lia.
        -- unfold Small. lia.
        -- destruct ou as [u|].
           ++ (* a literal to assert: s->mrk[u] = 0; *)
              pose proof (Hou u eq_refl) as Hu. pose proof (key_small u N Hu HN) as Hku.
              replace (zcmp Cge (enc_lit (Some u)) 0) with true
                by (cbn [zcmp enc_lit]; symmetry; apply Z.leb_le; lia).
              pose proof (r_mrk _ _ _ _ _ _ _ HRep2) as Fmrk.
              pose proof (a_mrk _ _ _ _ _ _ _ HRep2) as Amrk.
              assert (Hk: (lit_key u < 2 * N)%nat) by (apply lit_key_lt; assumption).
              change (enc_lit (Some u)) with (key u).
              cbv beta iota. run. eapply exec_store.
              ** evl.
              ** ev.
              ** reflexivity.
              ** reflexivity.
              ** ofs. bound.
              ** ofs. cbn [cast_int_int].
                 destruct (arr_storable m2 (b_mrk S) (2 * N) (lit_key u) _ 0 Amrk Hk)
                   as [m3 Hst3].
                 exists m3. split.
                 --- apply Hst3.
                 --- normal.
                     assert (HRep3: RepL m3 S N lss (set_mrk x (tset mk1 (lit_key u)
                       false))
                                      (j0 :: lims0) lt).
                     { apply (rep_store_mrk m2 m3 S N lss _ _ (lit_key u) false HRep2 Hk
                                Hst3). }
                     assert (Apool3: Arr m3 (b_wpool S) (2 * npool S) tp).
                     { apply (arr_store_other _ _ _ _ _ _ _ _ _ Apool Hst3). neq Hnd. }
                     keep_mem m3.
                     (* if (mx < d) *)
                     eapply (exec_if_cmp _ _ _ Clt).
                     +++ ev.
                     +++ ev.
                     +++ reflexivity.
                     +++ reflexivity.
                     +++ unfold Small. lia.
                     +++ unfold Small. cbn [length]. lia.
                     +++ cbn [zcmp]. destruct (Nat.ltb_spec mx (length (j0 :: lims0)))
                           as [Hlt | Hge].
                         *** (* below the current level: the backjump *)
                             replace (Z.of_nat mx <? Z.of_nat (length (j0 :: lims0)))
                               with true by (symmetry; apply Z.ltb_lt; lia).
                             cbv beta iota. apply returns_seq.
                             set (k := (length (j0 :: lims0) - Datatypes.S mx)%nat) in *.
                             replace (mx <? length (j0 :: lims0))%nat with true in Hcr
                               by (symmetry; now apply Nat.ltb_lt).
                             rewrite (nth_error_nth' (j0 :: lims0) (n := k) 0%nat) in Hcr
                               by (unfold k; lia).
                             rewrite (skipn_nth (c0 :: st) 0%nat k) in Hcr
                               by (unfold k; cbn [length] in *; lia).
                             rewrite Hcr.
                             apply (resolve_jump_correct S N lss x (j0 :: lims0)
                                      (tset mk1 (lit_key u) false) u mx _ _ _ P tp).
                             ---- assumption.
                             ---- assumption.
                             ---- assumption.
                             ---- assumption.
                             ---- assumption.
                             ---- assumption.
                             ---- apply nth_error_nth'. unfold k. lia.
                             ---- rewrite Hsv. apply skipn_nth. cbn [length] in *.
                                  unfold k. lia.
                             ---- tmp.
                             ---- tmp.
                             ---- tmp.
                         *** (* not below: flip *)
                             replace (Z.of_nat mx <? Z.of_nat (length (j0 :: lims0)))
                               with false by (symmetry; apply Z.ltb_ge; lia).
                             replace (mx <? length (j0 :: lims0))%nat with false in Hcr
                               by (symmetry; now apply Nat.ltb_ge).
                             cbv beta iota. apply exec_skip. normal. normal.
                             rewrite Hcr.
                             apply (resolve_flip_correct (lt := lt) S N lss x lims0 j0
                               c0 st
                                      (tset mk1 (lit_key u) false) P tp).
                             ---- assumption.
                             ---- assumption.
                             ---- assumption.
                             ---- assumption.
                             ---- assumption.
                             ---- tmp.
                             ---- tmp.
                             ---- tmp.
           ++ (* nothing to assert: flip *)
              replace (zcmp Cge (enc_lit None) 0) with false by reflexivity.
              cbv beta iota. apply exec_skip. normal.
              rewrite Hcr.
              apply (resolve_flip_correct (lt := lt) S N lss x lims0 j0 c0 st mk1 P tp).
              ** assumption.
              ** assumption.
              ** assumption.
              ** assumption.
              ** assumption.
              ** tmp.
              ** tmp.
              ** tmp.
Qed.

Lemma resolve_fun: exists (b: block),
  Genv.find_symbol ge _resolve = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_resolve).
Proof. apply find_fun. reflexivity. Qed.
