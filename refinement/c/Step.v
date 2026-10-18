(* step computes one step on the context (cstep), or gives up. *)
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
From compcert Require Import Ctypesdefs.
From compcert Require Import Clight.
From compcert Require Import ClightBigstep.

From RocqSAT Require Import Lit.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import State.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import Measure.
From RocqSAT Require Import Trans.
From RocqSAT.refinement Require Import Tactics.
From RocqSAT.refinement Require Import Table.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Search.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import Heur.
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement Require Import Step.
From RocqSAT.refinement Require Import SolverStep.
From RocqSAT.refinement.c Require Import Arrays.
From RocqSAT.refinement.c Require Import Logic.
From RocqSAT.refinement.c Require Import Common.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Rep.
From RocqSAT.refinement.c Require Import RepHeur.
From RocqSAT.refinement.c Require Import LitValue.
From RocqSAT.refinement.c Require Import Assign.
From RocqSAT.refinement.c Require Import Visit.
From RocqSAT.refinement.c Require Import Propagate.
From RocqSAT.refinement.c Require Import CheckShorts.
From RocqSAT.refinement.c Require Import SkipFrom.
From RocqSAT.refinement.c Require Import Phase.
From RocqSAT.refinement.c Require Import Pick.
From RocqSAT.refinement.c Require Import Resolve.

(* What C returns for an outcome is an int. *)
Lemma coutcome_vint: forall (sh: Shape) (N: nat) (lss: list (list Lit)) (P: mem -> Prop)
  (cr: CResult) (m: mem) (v: val),
  COutcome sh N lss P cr m v -> exists (z: Z), v = vint z.
Proof.
  intros sh N lss P [| |x'] m v Hv; cbn [COutcome] in Hv.
  - destruct Hv as [-> _]. now exists 0.
  - now exists 1.
  - destruct Hv as [-> _]. now exists 2.
Qed.

(* cstep in the parts that step computes one after the other: after the short clauses
   of x, propagation from x1; after propagation, a decision of x2 on the literal the
   heuristic picks, or else at the next unassigned literal of x3 from its cursor, or a
   stop when nothing was assigned since x. *)
Definition cstep_cursor (x x3: Ctx): CResult :=
  let c := next_undef x3 in
  if Nat.ltb c (nlits x3)
  then CNext (assign (open_level x3 c) (phase (phs x3) (tget (alls x3) c)) no_reason)
  else if Nat.eqb (tlen x3) (tlen x) then CStop else CNext (x3 <| cur := c |>).

Definition cstep_decide (x x2: Ctx): CResult :=
  match pick (vals x2) (hr x2) (nvars x2) with
  | (h, Some l0) =>
    CNext (assign (open_level (x2 <| hr := h |>) (cur x2)) (phase (phs x2) l0) no_reason)
  | (h, None)    => cstep_cursor x (x2 <| hr := h |>)
  end.

Definition cstep_propagate (x x1: Ctx): CResult :=
  match propagate (S (nvars x1)) (x1 <| shorts := [] |>) with
  | (x2, Some i) => resolve x2 i
  | (x2, None)   => cstep_decide x x2
  end.

Lemma cstep_parts: forall (x: Ctx),
  cstep x =
    match check_shorts (shorts x) x with
    | (x1, Some i) => resolve x1 i
    | (x1, None)   => cstep_propagate x x1
    end.
Proof. reflexivity. Qed.

(* The tests after check_shorts and after propagate, as clightgen writes them, with t
   the temporary for the result of resolve:

     if (c < 0) return -1; if (c > 0) return resolve(s, c - 1); rest *)
Definition on_conflict (t: ident) (rest: statement): statement :=
  Ssequence
    (Sifthenelse (Ebinop Olt (Etempvar _c tint) (Econst_int (Int.repr 0) tint) tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
      Sskip)
    (Ssequence
      (Sifthenelse (Ebinop Ogt (Etempvar _c tint) (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Scall (Some t)
            (Evar _resolve
              (Tfunction (tptr (Tstruct _solver noattr) :: tint :: nil) tint cc_default))
            (Etempvar _s (tptr (Tstruct _solver noattr)) ::
             Ebinop Osub (Etempvar _c tint) (Econst_int (Int.repr 1) tint) tint :: nil))
          (Sreturn (Some (Etempvar t tint))))
        Sskip)
      rest).

(* The parts of the body of step: from s->nshorts = 0, from int l0 = pick(s), the then
   branch of if (l0 >= 0), from int k = skip_from(s), the then branch of
   if (k < s->nlits), and after that if. *)
Definition step_propagate: statement := drop_stmts 4 (fn_body f_step).
Definition step_pick: statement := drop_stmts 8 (fn_body f_step).
Definition step_pick_decide: statement :=
  then_stmt (first_stmt (drop_stmts 9 (fn_body f_step))).
Definition step_choose: statement := drop_stmts 10 (fn_body f_step).
Definition step_decide: statement :=
  then_stmt (drop_stmts 1 (first_stmt (drop_stmts 11 (fn_body f_step)))).
Definition step_end: statement := drop_stmts 12 (fn_body f_step).

(* The end of both decisions: assign(s, l, 0) with the literal in temporary tl and its
   result in temporary tw. *)
Definition assign_stmt (tw tl: ident): statement :=
  Ssequence
    (Ssequence
      (Scall (Some tw)
        (Evar _assign
          (Tfunction (tptr (Tstruct _solver noattr) :: tint :: tint :: nil) tint
             cc_default))
        (Etempvar _s (tptr (Tstruct _solver noattr)) :: Etempvar tl tint ::
         Econst_int (Int.repr 0) tint :: nil))
      (Sifthenelse (Eunop Onotbool (Etempvar tw tint) tint)
        (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
        Sskip))
    (Sreturn (Some (Econst_int (Int.repr 2) tint))).

Section Parts.
  Context (sh: Shape) (N: nat) (lss: list (list Lit)).

  (* What step returns from the context x for the result cr of the model: what resolve
     returns, where a stop leaves the trail of x in the memory. *)
  Definition StepPost (x: Ctx) (cr: CResult): mem -> val -> Prop :=
    ResolvePost sh N lss (fun (m'': mem) => TrailIn m'' sh N (trail x)) cr.

  (* What check_shorts and propagate return for the conflict r they found in y: -1 when
     out of room, or the encoding of r, with y in memory and r a clause of lss. *)
  Definition ConflictOut (y: Ctx) (r: option nat) (m: mem) (v: val): Prop :=
    v = vint (-1) \/
      (v = vint (enc_conf r) /\ Rep m sh N lss y /\
       (forall (i: nat), r = Some i -> (i < length lss)%nat)).

  (* Where step decides, after a step from x reached y: y is represented and consistent
     and extends x, and the temporaries hold s and the trail length t0 of x. *)
  Record StepFrom {m: mem} {le: temp_env} {f: CNF} {x y: Ctx}: Prop := {
    sf_rep: Rep m sh N lss y;
    sf_core: StepCore (trail y) f y;
    sf_ext: Extends (trail x) (trail y);
    sf_tlen: (tlen x <= N)%nat;
    sf_s: le ! _s = Some (sptr sh);
    sf_t0: le ! _t0 = Some (vnat (tlen x));
  }.
  Arguments StepFrom : clear implicits.

  (* The tests for a conflict found in y, in a step from x: out of room, or a conflict on
     clause i to resolve, or none, and then rest runs.

       {{ ConflictOut y r c }}
         if (c < 0) return -1;
       {{ result = -1 (out of room) }}
         if (c > 0) return resolve(s, c - 1);                          (resolve_correct)
       {{ result = what resolve returns, for the conflict r = Some i, c - 1 = i }}
       {{ c = 0: no conflict, r = None /\ Rep y }}
         rest                                                                          *)
  Lemma on_conflict_correct: forall (x y: Ctx) (r: option nat) (cr: CResult) (t: ident)
    (rest: statement) (v: val) (le: temp_env) (m: mem),
    le ! _s = Some (sptr sh) -> le ! _c = Some v -> ConflictOut y r m v -> LimsBelow y ->
    (forall (i: nat), r = Some i -> cr = resolve y i) ->
    (r = None -> Rep m sh N lss y ->
     Exec ge le m rest (Returns f_step (StepPost x cr))) ->
    Exec ge le m (on_conflict t rest) (Returns f_step (StepPost x cr)).
  Proof.
    intros x y r cr t rest v le m Hs Hc Hv Hon Hres Hrest.
    unfold on_conflict. destruct Hv as [-> | (-> & HRep & Hcls)].
    - (* c = -1: out of room; return -1; *)
      run. branch (-1) 0.
      + intros _. return_int.
        now left.
      + intros Hge. lia.
    - destruct r as [i|]; cbn [enc_conf].
      + (* c = i + 1: a conflict on clause i; return resolve(s, c - 1); *)
        rewrite (Hres i eq_refl).
        pose proof (Hcls i eq_refl) as Hi_lt.
        pose proof (r_lss_small (proj1 HRep)) as Hlss.
        assert (Hi: Int.sub (Int.repr (enc_conf (Some i))) (Int.repr 1)
                    = Int.repr (Z.of_nat i)).
        { cbn [enc_conf]. rewrite sub_repr. f_equal. lia. }
        run. branch (Z.of_nat i + 1) 0.
        * intros Hlt. lia.
        * intros _. run. branch (Z.of_nat i + 1) 0.
          -- intros _.
             run. eapply (exec_call_triple resolve_fun
                            (resolve_correct sh N lss y i
                               (fun (m'': mem) => TrailIn m'' sh N (trail x)))).
             ++ reflexivity.
             ++ (* the argument c - 1 is i *)
                unfold vnat, vint. rewrite <- Hi. evs.
             ++ split.
                ** assumption.
                ** split; assumption.
             ++ intros m' v Hv. normal.
                assert (Hz: exists (z: Z), v = vint z).
                { destruct Hv as [-> | Hv].
                  - now exists (-1).
                  - now apply coutcome_vint in Hv. }
                destruct Hz as [z ->]. return_int.
                assumption.
          -- intros Hle. lia.
      + (* c = 0: no conflict; the rest runs *)
        run. branch 0 0.
        * intros Hlt. lia.
        * intros _. run. branch 0 0.
          -- intros Hgt. lia.
          -- intros _. run. apply Hrest.
             ++ reflexivity.
             ++ assumption.
  Qed.

  (* Assigning the decision l, after its decision level is open:

       {{ RepL xo /\ lower xo = [] /\ Arr pool tp /\ l = key l' }}
         if (!assign(s, l, 0)) return -1;                               (assign_correct)
       {{ result = -1 (out of room) }}
         return 2;
       {{ result = 2 /\ Rep (assign xo l' no_reason) }}                            *)
  Lemma step_assign_correct: forall (x xo: Ctx) (l: Lit) (tp: nat -> Z) (tw tl: ident)
    (rest: statement) (le: temp_env) (m: mem),
    RepL m sh N lss xo -> lower xo = [] -> PoolArr m sh tp ->
    PoolFree sh N tp (wls xo) -> (extract l < N)%nat ->
    le ! _s = Some (sptr sh) -> le ! tl = Some (vint (key l)) ->
    Exec ge le m (assign_stmt tw tl)
      (SeqK ge rest
         (Returns f_step (StepPost x (CNext (assign xo l no_reason))))).
  Proof.
    intros x xo l tp tw tl rest le m HRep Hlow Apool Hpool Hl Hs Hlv.
    unfold assign_stmt.
    run.
    call assign_fun (assign_correct sh N lss xo l no_reason tp).
    - splits.
      + assumption.
      + assumption.
      + (* a decision has no reason *)
        cbn [ReasonBelow]. constructor.
      + assumption.
    - intros m' v Hv. normal. destruct Hv as [-> | (-> & HRep' & Apool')].
      + (* assign gave up: return -1; *)
        branch 1.
        * intros _. return_int.
          now left.
        * intros Heq. lia.
      + (* return 2; *)
        branch 0.
        * intros Hne. lia.
        * intros _. run. return_int.
          right. split.
          -- reflexivity.
          -- split.
             ++ assumption.
             ++ split.
                ** (* assign keeps the lower literals *)
                   cbn [assign lower]. assumption.
                ** exists tp. split; assumption.
  Qed.

  (* Deciding at the unassigned literal of alls at the cursor k: the decision level
     opens, and the literal with its phase is assigned.

       {{ Rep x2 /\ k < nlits /\ the literal alls[k] is unassigned }}
         int l = phase(s, s->alls[k]);                                   (phase_correct)
         s->cur = k;
         s->saved[s->dl] = k;
         s->lims[s->dl] = s->tlen;
         s->dl = s->dl + 1;                                             (rep_store_open)
       {{ RepL (open_level x2 k) /\ l = key (phase ...) }}
         ...                                                     (step_assign_correct) *)
  Lemma step_decide_correct: forall (f: CNF) (x x2: Ctx) (k: nat) (le: temp_env)
    (m: mem),
    Rep m sh N lss x2 -> StepCore (trail x2) f x2 -> (k < nlits x2)%nat ->
    lookup (vals x2) (tget (alls x2) k) = None ->
    le ! _s = Some (sptr sh) -> le ! _k = Some (vnat k) ->
    Exec ge le m step_decide
      (SeqK ge step_end (Returns f_step (StepPost x
        (CNext (assign (open_level x2 k) (phase (phs x2) (tget (alls x2) k))
           no_reason))))).
  Proof.
    intros f x x2 k le m (HRep & Hlow & tp & Apool & Hpool) Hcore2 Hk
      Hundef Hs Hkv.
    pose proof (lims_on_trail Hcore2) as [_ Hlen2].
    pose proof HRep as HRep'. destruct HRep'.
    destruct a_alls as (ta & Aalls & Hta). destruct a_saved as (tsv & Asaved & Htsv).
    destruct a_lims as (tl & Alims & Htl). unpack.
    assert (Hl: (extract (tget (alls x2) k) < N)%nat) by (apply r_alls_atoms; lia).
    assert (Hla: (extract (phase (phs x2) (tget (alls x2) k)) < N)%nat)
      by (rewrite extract_phase; assumption).
    assert (Hlu: lookup (vals x2) (phase (phs x2) (tget (alls x2) k)) = None)
      by (apply phase_undef; assumption).
    pose proof (trail_room N _ Hcore2 r_tr_atoms Hlu Hla) as Hroom.
    assert (Hdl: (length (lims x2) < N)%nat) by lia.
    assert (Hkle: (k <= nlits x2)%nat) by lia.
    assert (Hdl1: Int.add (Int.repr (Z.of_nat (length (lims x2)))) (Int.repr 1) =
                  Int.repr (Z.of_nat (S (length (lims x2))))).
    { rewrite add_repr by lia. f_equal. lia. }
    unfold step_decide, f_step. cbn [fn_body drop_stmts first_stmt then_stmt].
    (* int l = phase(s, s->alls[k]); *)
    run. rewrite (Hta k) by lia.
    call phase_fun (phase_correct sh N lss x2 (tget (alls x2) k)).
    - split; assumption.
    - intros m' v [-> ->]. normal. run.
      (* s->cur = k; *)
      store r_cur as m1 Hst1.
      carry Hst1 r_nodup. keep_mem m1.
      (* s->saved[s->dl] = k; *)
      run. store Asaved Hdl as m2 Hst2.
      carry Hst2 r_nodup. keep_mem m2.
      (* s->lims[s->dl] = s->tlen; *)
      run. store Alims Hdl as m3 Hst3.
      carry Hst3 r_nodup. keep_mem m3.
      (* s->dl = s->dl + 1; *)
      run. store r_dl as m4 Hst4.
      cbn [cast_int_int] in Hst4. rewrite Hdl1 in Hst4.
      normal. carry Hst4 r_nodup.
      pose proof (rep_store_open m m1 m2 m3 m4 k
                    HRep Hkle Hdl Hst1 Hst2 Hst3 Hst4)
        as HRepo.
      apply (step_assign_correct x _ _ tp _t'10 _l__1).
      + apply HRepo.
      + (* opening a level keeps the lower literals *)
        cbn [open_level lower]. assumption.
      + assumption.
      + apply Hpool.
      + assumption.
      + tmp.
      + tmp.
  Qed.

  (* Choosing a decision, after propagation without a conflict:

       {{ StepFrom x x2 }}
         int k = skip_from(s);                                       (skip_from_correct)
       {{ k = the next unassigned literal of alls from the cursor, or nlits }}
         if (k < s->nlits) { ... }                                 (step_decide_correct)
         if (s->tlen == t0) return 0;
       {{ result = 0: nothing was assigned, so the trail is still that of x }}
         s->cur = k;                                                     (rep_store_cur)
         return 2;
       {{ result = 2 /\ Rep (x2 <| cur := k |>) }}                                     *)
  Lemma step_choose_correct: forall (f: CNF) (x x2: Ctx) (le: temp_env) (m: mem),
    StepFrom m le f x x2 ->
    Exec ge le m step_choose (Returns f_step (StepPost x (cstep_cursor x x2))).
  Proof.
    intros f x x2 le m [HRep2 Hcore2 Hext Htx Hs Ht0].
    pose proof HRep2 as (HRep & Hlow & tp & Apool & Hpool).
    unfold step_choose, f_step. cbn [fn_body drop_stmts].
    (* int k = skip_from(s); *)
    run. call skip_from_fun (skip_from_correct sh N lss x2).
    - assumption.
    - intros m' v [-> ->]. normal.
      destruct (next_undef_spec f x2 (sc_cursor Hcore2)) as [Hc Hundef].
      unfold cstep_cursor. cbv zeta.
      remember (next_undef x2) as k eqn:Hk.
      pose proof (proj1 Hc) as Hkn.
      pose proof HRep as HRep'. destruct HRep'. unpack.
      (* if (k < s->nlits) *)
      run. branch.
      + (* a literal to decide on *)
        intros Hlt.
        replace (Nat.ltb k (nlits x2)) with true by (symmetry; apply Nat.ltb_lt; lia).
        apply (step_decide_correct f x).
        * assumption.
        * assumption.
        * lia.
        * apply Hundef. lia.
        * tmp.
        * tmp.
      + (* all literals assigned *)
        intros Hge.
        replace (Nat.ltb k (nlits x2)) with false by (symmetry; apply Nat.ltb_ge; lia).
        run.
        (* if (s->tlen == t0) return 0; *)
        branch.
        * (* nothing was assigned: the trail is that of x *)
          intros Htlen. assert (Heq: tlen x2 = tlen x) by lia.
          replace (Nat.eqb (tlen x2) (tlen x)) with true
            by (symmetry; now apply Nat.eqb_eq).
          return_int.
          assert (Htrail: trail x2 = trail x).
          { apply extends_same_length.
            - assumption.
            - rewrite !trail_length. assumption. }
          destruct (core_trail (core_of_step Hcore2)) as [_ Htr2].
          right. split.
          -- reflexivity.
          -- rewrite <- Htrail. split.
             ++ rewrite trail_length. assumption.
             ++ exists (fun (j: nat) => key (tget (tr x2) j)). split.
                ** assumption.
                ** intros j Hj. rewrite trail_length in Hj.
                   cbv beta. rewrite Htr2 by lia.
                   reflexivity.
        * (* s->cur = k; return 2; *)
          intros Htlen.
          replace (Nat.eqb (tlen x2) (tlen x)) with false
            by (symmetry; apply Nat.eqb_neq; lia).
          run. store r_cur as m1 Hst1.
          return_int.
          right. split.
          -- reflexivity.
          -- split.
             ++ apply (rep_store_cur m m1 k HRep).
                ** lia.
                ** assumption.
             ++ split.
                ** (* setting the cursor keeps the lower literals *)
                   cbn [set_cur lower]. assumption.
                ** exists tp. split.
                   --- apply (arr_store_other Apool Hst1). neq r_nodup.
                   --- assumption.
  Qed.

  (* Deciding on the unassigned literal l0 of f the heuristic picked: the decision level
     opens at the cursor, and l0 with its phase is assigned.

       {{ Rep y /\ l0 is unassigned, of an atom below N /\ l0 = key l0 }}
         int l = phase(s, l0);                                           (phase_correct)
         s->saved[s->dl] = s->cur;
         s->lims[s->dl] = s->tlen;
         s->dl = s->dl + 1;                                         (rep_store_open_cur)
       {{ RepL (open_level y (cur y)) /\ l = key (phase ...) }}
         ...                                                     (step_assign_correct) *)
  Lemma step_pick_decide_correct: forall (f: CNF) (x y: Ctx) (l0: Lit) (rest: statement)
    (le: temp_env) (m: mem),
    Rep m sh N lss y -> StepCore (trail y) f y -> (extract l0 < N)%nat ->
    lookup (vals y) l0 = None ->
    le ! _s = Some (sptr sh) -> le ! _l0 = Some (vint (key l0)) ->
    Exec ge le m step_pick_decide
      (SeqK ge rest (Returns f_step (StepPost x
        (CNext (assign (open_level y (cur y)) (phase (phs y) l0) no_reason))))).
  Proof.
    intros f x y l0 rest le m (HRep & Hlow & tp & Apool & Hpool) Hcore2
      Hl Hundef Hs Hl0v.
    pose proof (lims_on_trail Hcore2) as [_ Hlen2].
    pose proof HRep as HRep'. destruct HRep'.
    destruct a_saved as (tsv & Asaved & Htsv). destruct a_lims as (tl & Alims & Htl).
    unpack.
    assert (Hla: (extract (phase (phs y) l0) < N)%nat)
      by (rewrite extract_phase; assumption).
    assert (Hlu: lookup (vals y) (phase (phs y) l0) = None)
      by (apply phase_undef; assumption).
    pose proof (trail_room N _ Hcore2 r_tr_atoms Hlu Hla) as Hroom.
    assert (Hdl: (length (lims y) < N)%nat) by lia.
    assert (Hdl1: Int.add (Int.repr (Z.of_nat (length (lims y)))) (Int.repr 1) =
                  Int.repr (Z.of_nat (S (length (lims y))))).
    { rewrite add_repr by lia. f_equal. lia. }
    unfold step_pick_decide, f_step. cbn [fn_body drop_stmts first_stmt then_stmt].
    (* int l = phase(s, l0); *)
    run. call phase_fun (phase_correct sh N lss y l0).
    - split; assumption.
    - intros m' v [-> ->]. normal.
      (* s->saved[s->dl] = s->cur; *)
      run. store Asaved Hdl as m2 Hst2.
      carry Hst2 r_nodup. keep_mem m2.
      (* s->lims[s->dl] = s->tlen; *)
      run. store Alims Hdl as m3 Hst3.
      carry Hst3 r_nodup. keep_mem m3.
      (* s->dl = s->dl + 1; *)
      run. store r_dl as m4 Hst4.
      cbn [cast_int_int] in Hst4. rewrite Hdl1 in Hst4.
      normal. carry Hst4 r_nodup.
      pose proof (rep_store_open_cur m m2 m3 m4
                    HRep Hdl Hst2 Hst3 Hst4) as HRepo.
      apply (step_assign_correct x _ _ tp _t'7 _l).
      + apply HRepo.
      + (* opening a level keeps the lower literals *)
        cbn [open_level lower]. assumption.
      + assumption.
      + apply Hpool.
      + assumption.
      + tmp.
      + tmp.
  Qed.

  (* Choosing a decision, after propagation without a conflict: the heuristic picks a
     literal, and changes to h on the way.

       {{ StepFrom x x2 }}
         int l0 = pick(s);                                                (pick_correct)
       {{ Rep (x2 <| hr := h |>) /\ l0 = enc_lit ol, for pick ... = (h, ol) }}
         if (l0 >= 0) { ... }                                 (step_pick_decide_correct)
       {{ ol = None }}
         ...                                                     (step_choose_correct) *)
  Lemma step_pick_correct: forall (f: CNF) (x x2: Ctx) (le: temp_env) (m: mem),
    StepFrom m le f x x2 ->
    Exec ge le m step_pick (Returns f_step (StepPost x (cstep_decide x x2))).
  Proof.
    intros f x x2 le m [(HRep & Hlow & tp & Apool & Hpool) Hcore2 Hext Htx Hs Ht0].
    pose proof (r_n HRep) as HN.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (r_nvars HRep) as Hnv.
    unfold cstep_decide. rewrite Hnv.
    unfold step_pick, f_step. cbn [fn_body drop_stmts].
    (* int l0 = pick(s); *)
    run. call pick_fun (pick_correct sh N lss x2).
    - assumption.
    - intros m1 v Hpost. normal. eapply exec_set.
      + ev.
      + normal.
        (* the heuristic changed, but not its literals to decide on *)
        pose proof (pick_dlit (vals x2) (hr x2) N) as Hd.
        destruct (pick (vals x2) (hr x2) N) as [h ol] eqn:Hpick.
        cbn [fst] in Hd. destruct Hpost as ((HRep1 & Hun1) & ->).
        transfer Hun1 Hnd. keep_mem m1.
        pose proof (step_core_heur (trail x2) f x2 h Hcore2 Hd) as Hcore3.
        destruct ol as [l0|].
        * (* a literal picked: decide on it *)
          destruct (pick_unassigned (trail x2) f x2 N h l0 Hcore2 Hpick) as [Hundef0 Hl].
          rewrite Hnv in Hl. pose proof (key_small l0 N Hl HN) as Hkey.
          (* if (l0 >= 0) *)
          run. eapply exec_if_ge.
          -- ev.
          -- ev.
          -- reflexivity.
          -- cbn [enc_lit]. lia.
          -- intros _.
             apply (step_pick_decide_correct f x (x2 <| hr := h |>) l0).
             ++ split.
                ** assumption.
                ** split.
                   --- (* a new heuristic keeps the lower literals *)
                       cbn [set_hr lower]. assumption.
                   --- exists tp. split.
                       +++ assumption.
                       +++ apply Hpool.
             ++ assumption.
             ++ assumption.
             ++ assumption.
             ++ tmp.
             ++ tmp.
          -- cbn [enc_lit]. intros Hlt. lia.
        * (* nothing picked: decide by the cursor *)
          (* if (l0 >= 0) *)
          run. eapply exec_if_ge.
          -- ev.
          -- ev.
          -- reflexivity.
          -- cbn [enc_lit]. lia.
          -- cbn [enc_lit]. intros Hge. lia.
          -- intros _. apply exec_skip. normal.
             apply (step_choose_correct f x (x2 <| hr := h |>)). constructor.
             ++ split.
                ** assumption.
                ** split.
                   --- (* a new heuristic keeps the lower literals *)
                       cbn [set_hr lower]. assumption.
                   --- exists tp. split.
                       +++ assumption.
                       +++ apply Hpool.
             ++ assumption.
             ++ assumption.
             ++ assumption.
             ++ tmp.
             ++ tmp.
  Qed.

  (* After the short clauses, without a conflict among them: they are cleared, and
     propagation runs.

       {{ StepFrom x x1 }}
         s->nshorts = 0;                                              (rep_store_shorts)
       {{ Rep (x1 <| shorts := [] |>) }}
         c = propagate(s);                                           (propagate_correct)
         if (c < 0) return -1;
         if (c > 0) return resolve(s, c - 1);                      (on_conflict_correct)
       {{ Rep x2, after propagation without a conflict }}
         ...                                                       (step_pick_correct) *)
  Lemma step_propagate_correct: forall (f: CNF) (x x1: Ctx) (le: temp_env) (m: mem),
    StepFrom m le f x x1 -> WellFormed (state (trail x1) f) -> NoEmpty x1 ->
    Exec ge le m step_propagate (Returns f_step (StepPost x (cstep_propagate x x1))).
  Proof.
    intros f x x1 le m [(HRep & Hlow & tp & Apool & Hpool) Hcore1 Hext1 Htx Hs Ht0]
      Hwf1 Hne1.
    destruct (propagate_trail (trail x1) f x1 Hcore1 Hwf1 Hne1) as [Hcore2 Hext2].
    pose proof (r_nodup HRep) as Hnd.
    pose proof (r_nvars HRep) as Hnv.
    pose proof (r_nshorts HRep) as Fns.
    pose proof (a_shorts HRep) as (tsh & Ash & _).
    unfold cstep_propagate. rewrite Hnv in Hcore2, Hext2 |- *.
    unfold step_propagate, f_step. cbn [fn_body drop_stmts].
    (* s->nshorts = 0; *)
    run. store Fns as m1 Hst1.
    assert (HRep1: RepL m1 sh N lss (x1 <| shorts := [] |>)).
    { apply (rep_store_shorts m m1 [] tsh HRep Ash).
      - intros q Hq. cbn [length] in Hq. lia.
      - cbn [length]. lia.
      - intros i [].
      - apply Hst1. }
    assert (Apool1: PoolArr m1 sh tp).
    { apply (arr_store_other Apool Hst1). neq Hnd. }
    (* c = propagate(s); *)
    run. call propagate_fun (propagate_correct sh N lss (x1 <| shorts := [] |>)).
    - split.
      + assumption.
      + split.
        * (* clearing the short clauses keeps the lower literals *)
          cbn [set_shorts lower]. assumption.
        * exists tp. split.
          -- assumption.
          -- apply Hpool.
    - intros m2 v Hv. normal. eapply exec_set.
      + ev.
      + normal.
        destruct (propagate (S N) (x1 <| shorts := [] |>)) as [x2 r2] eqn:Hp.
        cbn [fst snd] in *.
        pose proof (lims_on_trail Hcore2) as [Hon2 _].
        (* if (c < 0) return -1; if (c > 0) return resolve(s); *)
        apply (on_conflict_correct x x2 r2 _ _ _ v).
        * tmp.
        * tmp.
        * assumption.
        * assumption.
        * intros i ->. reflexivity.
        * intros -> HRep2.
          apply (step_pick_correct f x x2). constructor.
          -- assumption.
          -- assumption.
          -- now apply extends_trans with (trail x1).
          -- assumption.
          -- tmp.
          -- tmp.
  Qed.

  (* step makes the step of cstep on the represented context x, or gives up: it returns
     -1 when out of room, 0 to stop (the trail of x stays), 1 for fail, and 2 with the
     next context.

       {{ Rep x /\ StepInv (state (trail x) f) x }}
         int t0 = s->tlen;
         int c = check_shorts(s);                                 (check_shorts_correct)
         if (c < 0) return -1;
         if (c > 0) return resolve(s, c - 1);                      (on_conflict_correct)
       {{ Rep x1, after the short clauses without a conflict }}
         ...                                                    (step_propagate_correct)
       {{ StepPost x (cstep x) }}                                (cstep_parts) *)
  Lemma step_correct: forall (x: Ctx) (f: CNF),
    {{ m | Rep m sh N lss x /\ StepInv (state (trail x) f) x }}
      f_step(sptr sh)
    {{ m', v | StepPost x (cstep x) m' v }}.
  Proof.
    intros x f m (HRep & Hinv).
    destruct (check_shorts_trail (trail x) f x Hinv)
      as (Hcore1 & Hext1 & Hwf1 & Hnonempty1).
    pose proof (Rep.r_tlen_le (proj1 HRep)) as Htx.
    eapply call_simple.
    - reflexivity.
    - reflexivity.
    - unfold f_step. cbn [fn_body fn_return].
      pose proof (r_tlen (proj1 HRep)) as Ftlen.
      (* int t0 = s->tlen; int c = check_shorts(s); *)
      run. clear Ftlen.
      call check_shorts_fun (check_shorts_correct sh N lss x).
      + assumption.
      + intros m1 v Hv. normal. eapply exec_set.
        * ev.
        * normal. rewrite cstep_parts.
          destruct (check_shorts (shorts x) x) as [x1 r1] eqn:Hcs. cbn [fst snd] in *.
          pose proof (lims_on_trail Hcore1) as [Hon1 _].
          (* if (c < 0) return -1; if (c > 0) return resolve(s); *)
          apply (on_conflict_correct x x1 r1 _ _ _ v).
          -- tmp.
          -- tmp.
          -- assumption.
          -- assumption.
          -- intros i ->. reflexivity.
          -- intros -> HRep1.
             apply (step_propagate_correct f x x1).
             ++ constructor.
                ** assumption.
                ** assumption.
                ** assumption.
                ** assumption.
                ** tmp.
                ** tmp.
             ++ assumption.
             ++ now apply Hnonempty1.
  Qed.

End Parts.

Lemma step_fun: FunAt _step f_step.
Proof. apply find_fun. reflexivity. Qed.
