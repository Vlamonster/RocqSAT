(* step computes one step on the context (cstep), or gives up. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs Ctypes
  Ctypesdefs Cop Clight ClightBigstep.
From RocqSAT Require Import Lit CNF Assignment Evaluation State WellFormed Trans Measure.
From RocqSAT.refinement Require Import Table Lookup Watches Search Heur Propagate Step
  CStep SolverStep.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep RepHeur LitValue Assign
  Visit Propagate CheckShorts SkipFrom Phase Pick Resolve.
Import ListNotations.

Section Room.
  Open Scope nat_scope.
  (* An unassigned literal has an atom that is not on the trail. *)
  Lemma undef_not_atom: forall (m: PA) (l: Lit),
    l_eval m l = None -> ~ In (extract l) (atoms m).
  Proof.
    intros m l Hundef Hin. apply PA.Lemmas.in_atoms in Hin as [y [Hy Hext]].
    apply Neg.extract_eq in Hext.
    assert (Hdef: exists (b: bool), l_eval m l = Some b).
    - apply l_eval_some_iff. destruct Hext as [-> | ->].
      + now left.
      + now right.
    - destruct Hdef as [b Hb]. congruence.
  Qed.

  (* The atoms of a trail that only assigns unassigned literals are distinct. *)
  Lemma fresh_nodup: forall (m: PA), Fresh m -> NoDup (atoms m).
  Proof.
    intros m. induction m as [|m IH l|m IH l]; simpl; intros Hfresh.
    - constructor.
    - destruct Hfresh as [Hfresh Hundef]. constructor.
      + now apply undef_not_atom.
      + now apply IH.
    - destruct Hfresh as [Hfresh Hundef]. constructor.
      + now apply undef_not_atom.
      + now apply IH.
  Qed.

  (* With an unassigned literal, a trail over atoms below N is shorter than N. *)
  Lemma room: forall (m: PA) (l: Lit) (N: nat),
    Fresh m -> l_eval m l = None -> extract l < N ->
    (forall (y: Lit), y ∈ m -> extract y < N) -> S (PA.length m) <= N.
  Proof.
    intros m l N Hfresh Hundef Hl Hatoms.
    rewrite <- PA.Lemmas.length_atoms. rewrite <- (length_seq N 0).
    apply (NoDup_incl_length (l := extract l :: atoms m)).
    - constructor.
      + now apply undef_not_atom.
      + now apply fresh_nodup.
    - intros p [<- | Hp].
      + apply in_seq. lia.
      + apply PA.Lemmas.in_atoms in Hp as [y [Hy <-]]. apply in_seq.
        apply Hatoms in Hy. lia.
  Qed.

  (* Every literal of a trail is in its list of literals. *)
  Lemma trail_lits_in: forall (m: PA) (y: Lit), y ∈ m -> In y (trail_lits m).
  Proof.
    intros m y. induction m as [|m IH l|m IH l]; cbn.
    - easy.
    - intros [<- | Hy]; apply in_or_app.
      + right. now left.
      + left. now apply IH.
    - intros [<- | Hy]; apply in_or_app.
      + right. now left.
      + left. now apply IH.
  Qed.

  (* Decision positions are on the trail, one per decision. *)
  Lemma lims_lt: forall (lims: list nat) (m: PA) (j: nat),
    LimsOf lims m -> In j lims -> j < PA.length m.
  Proof.
    intros lims m. revert lims.
    induction m as [|m IH l|m IH l]; intros lims j Hlims Hj; simpl in Hlims |- *.
    - now subst lims.
    - apply (IH lims j) in Hlims.
      + lia.
      + assumption.
    - destruct lims as [|j' lims].
      + contradiction.
      + destruct Hlims as [-> Hlims]. destruct Hj as [<- | Hj].
        * lia.
        * apply (IH lims j) in Hlims.
          -- lia.
          -- assumption.
  Qed.

  (* There are at most as many decisions as literals on the trail. *)
  Lemma lims_length: forall (lims: list nat) (m: PA),
    LimsOf lims m -> length lims <= PA.length m.
  Proof.
    intros lims m. revert lims.
    induction m as [|m IH l|m IH l]; intros lims Hlims; simpl in Hlims |- *.
    - now subst lims.
    - apply IH in Hlims. lia.
    - destruct lims as [|j lims].
      + contradiction.
      + destruct Hlims as [-> Hlims]. apply IH in Hlims. simpl. lia.
  Qed.
End Room.

(* The contexts a step reaches are consistent with states, with the same positions of
   decisions. *)
Section Reached.
  (* The part of the invariant of a step about the trail and the values. *)
  Lemma step_core: forall (m: PA) (f: CNF) (x: Ctx), StepCore m f x -> Core m f x.
  Proof.
    intros m f x Hcore. apply pi_core. apply sc_prop. assumption.
  Qed.

  (* After check_shorts: a trail m1 that extends m and is consistent with the context,
     with the same decision positions; without a conflict, no clause is empty. *)
  Lemma reached_shorts: forall (m: PA) (f: CNF) (x: Ctx) (lims: list nat),
    StepInv (state m f) x -> LimsOf lims m ->
    exists (m1: PA), StepCore m1 f (fst (check_shorts_t (shorts x) x)) /\
      LimsOf lims m1 /\ Extends m m1 /\ WellFormed (state m1 f) /\
      (snd (check_shorts_t (shorts x) x) = None ->
       forall (i: nat), tget (cmap (fst (check_shorts_t (shorts x) x))) i <> Some []).
  Proof.
    intros m f x lims [Hcore [Hwf _]] Hlims.
    destruct (check_shorts (shorts x) m x) as [[m1 x1] r1] eqn:Hcheck.
    destruct (front_shorts m m1 f x x1 r1 Hcore Hcheck)
      as (Hder1 & Hext1 & Hcore1 & Hnone1 & _).
    rewrite (check_shorts_free _ _ _ _ _ _ Hcheck). cbn [fst snd]. exists m1. split.
    - assumption.
    - split.
      + now apply (lims_extends lims m).
      + split.
        * assumption.
        * split.
          -- now apply (derivation_well_formed DPLL_BJ m m1 f f).
          -- assumption.
  Qed.

  (* After propagate: a trail m2 that extends m1 and is consistent with the context,
     with the same decision positions. *)
  Lemma reached_prop: forall (m1: PA) (f: CNF) (x1: Ctx) (lims: list nat),
    StepCore m1 f x1 -> WellFormed (state m1 f) -> LimsOf lims m1 ->
    (forall (i: nat), tget (cmap x1) i <> Some []) ->
    exists (m2: PA),
      StepCore m2 f (fst (propagate_t (Datatypes.S (nvars x1)) (clear_shorts x1))) /\
      LimsOf lims m2 /\ Extends m1 m2.
  Proof.
    intros m1 f x1 lims Hcore1 Hwf1 Hlims1 Hnonempty.
    destruct (propagate (Datatypes.S (nvars x1)) m1 (clear_shorts x1))
      as [[m2 x2] r2] eqn:Hprop.
    destruct (front_prop m1 m2 f x1 x2 r2 Hcore1 Hwf1 Hnonempty Hprop)
      as (_ & Hext2 & Hcore2 & _).
    rewrite (propagate_free _ _ _ _ _ _ Hprop). cbn [fst]. exists m2. split.
    - assumption.
    - split.
      + now apply (lims_extends lims m1).
      + assumption.
  Qed.

  (* The positions of the decisions are on the trail. *)
  Lemma lims_on_trail: forall (m: PA) (f: CNF) (x: Ctx) (lims: list nat),
    StepCore m f x -> LimsOf lims m ->
    (forall (j: nat), In j lims -> (j < tlen x)%nat) /\ (length lims <= tlen x)%nat.
  Proof.
    intros m f x lims Hcore Hlims.
    destruct (core_trail _ _ _ (step_core _ _ _ Hcore)) as [Hlen _].
    rewrite trail_lits_length in Hlen. split.
    - intros j Hj. rewrite Hlen. now apply (lims_lt lims).
    - rewrite Hlen. now apply lims_length.
  Qed.

  (* With an unassigned literal of an atom below N, a trail of atoms below N has room. *)
  Lemma trail_room: forall (m: PA) (f: CNF) (x: Ctx) (N: nat) (l: Lit),
    StepCore m f x ->
    (forall (j: nat), (j < tlen x)%nat -> (extract (tget (tr x) j) < N)%nat) ->
    lookup (vals x) l = None -> (extract l < N)%nat -> (tlen x < N)%nat.
  Proof.
    intros m f x N l Hcore Hatoms Hl HlN.
    destruct (step_core _ _ _ Hcore) as [Hvals Hfresh [Hlen Htr] _ _].
    rewrite trail_lits_length in Hlen. rewrite Hlen. apply (room m l N Hfresh).
    - now rewrite <- Hvals.
    - assumption.
    - intros y Hy. apply trail_lits_in in Hy.
      apply In_nth with (d := Pos 0%nat) in Hy as [j [Hj <-]].
      rewrite trail_lits_length in Hj. rewrite <- Htr by lia. apply Hatoms. lia.
  Qed.
End Reached.

(* A phase only chooses the sign of a literal. *)
Lemma extract_phase: forall (ph: Values) (l: Lit), extract (phase ph l) = extract l.
Proof.
  intros ph l. destruct (phase_cases ph l) as [-> | ->].
  - reflexivity.
  - now destruct l.
Qed.

(* What C returns for an outcome is an int. *)
Lemma coutcome_vint: forall (S: Shape) (N: nat) (lss: list (list Lit)) (P: mem -> Prop)
  (cr: CResult) (m: mem) (v: val),
  COutcome S N lss P cr m v -> exists (z: Z), v = vint z.
Proof.
  intros S N lss P [| |x' lims'] m v Hv; cbn [COutcome] in Hv.
  - destruct Hv as [-> _]. now exists 0.
  - now exists 1.
  - destruct Hv as [-> _]. now exists 2.
Qed.

(* cstep in the parts that step computes one after the other: after the short clauses
   of x, propagation from x1; after propagation, a decision of x2 on the literal the
   heuristic picks, or else at the next unassigned literal of x3 from its cursor, or a
   stop when nothing was assigned since x. *)
Definition cstep_cursor (x x3: Ctx) (lims: list nat): CResult :=
  let c := skip_from (vals x3) (alls x3) (nlits x3) (nlits x3 - cur x3) (cur x3) in
  if Nat.ltb c (nlits x3)
  then CNext (assign (open_level x3 c) (phase (phs x3) (tget (alls x3) c)) no_reason)
         (tlen x3 :: lims)
  else if Nat.eqb (tlen x3) (tlen x) then CStop else CNext (with_cursor x3 c) lims.

Definition cstep_decide (x x2: Ctx) (lims: list nat): CResult :=
  match pick (vals x2) (hr x2) (nvars x2) with
  | (h, Some l0) =>
    CNext (assign (open_level (with_heur x2 h) (cur x2)) (phase (phs x2) l0) no_reason)
      (tlen x2 :: lims)
  | (h, None)    => cstep_cursor x (with_heur x2 h) lims
  end.

Definition cstep_propagate (x x1: Ctx) (lims: list nat): CResult :=
  match propagate_t (Datatypes.S (nvars x1)) (clear_shorts x1) with
  | (x2, Some i) => resolve_t x2 lims i
  | (x2, None)   => cstep_decide x x2 lims
  end.

Lemma cstep_parts: forall (x: Ctx) (lims: list nat),
  cstep x lims =
    match check_shorts_t (shorts x) x with
    | (x1, Some i) => resolve_t x1 lims i
    | (x1, None)   => cstep_propagate x x1 lims
    end.
Proof. reflexivity. Qed.

(* What step returns for the result cr of the model: -1 when it is out of room, or the
   outcome of cr, where a stop leaves the trail pm in the memory. *)
Definition StepPost (S: Shape) (N: nat) (lss: list (list Lit)) (pm: PA) (cr: CResult)
  (m': mem) (v: val): Prop :=
  v = vint (-1) \/ COutcome S N lss (fun (m'': mem) => TrailIn m'' S N pm) cr m' v.

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

(* The tests for a conflict found in x: out of room, or a conflict on clause i to
   resolve, or none, and then rest runs.

     {{ c = -1 \/ (c = enc_conf r /\ Rep x lims /\ (r = Some i -> i < length lss)) }}
       if (c < 0) return -1;
     {{ result = -1 (out of room) }}
       if (c > 0) return resolve(s, c - 1);                          (resolve_correct)
     {{ result = what resolve returns, for the conflict r = Some i, c - 1 = i }}
     {{ c = 0: no conflict, r = None /\ Rep x lims }}
       rest                                                                            *)
Lemma on_conflict_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (pm: PA)
  (x: Ctx) (lims: list nat) (r: option nat) (cr: CResult) (t: ident) (rest: statement)
  (v: val) (le: temp_env) (m: mem),
  le ! _s = Some (sptr S) -> le ! _c = Some v ->
  v = vint (-1) \/
    (v = vint (enc_conf r) /\ Rep m S N lss x lims /\
     (forall (i: nat), r = Some i -> (i < length lss)%nat)) ->
  (forall (j: nat), In j lims -> (j < tlen x)%nat) ->
  (forall (i: nat), r = Some i -> cr = resolve_t x lims i) ->
  (r = None -> Rep m S N lss x lims ->
   Exec ge le m rest (Returns f_step (StepPost S N lss pm cr))) ->
  Exec ge le m (on_conflict t rest) (Returns f_step (StepPost S N lss pm cr)).
Proof.
  intros S N lss pm x lims r cr t rest v le m Hs Hc Hv Hon Hres Hrest.
  unfold on_conflict. destruct Hv as [-> | (-> & HRep & Hcls)].
  - (* c = -1: out of room; return -1; *)
    run. eapply (exec_if_cmp _ _ _ Clt _ _ (-1) 0).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + unfold Small. lia.
    + unfold Small. lia.
    + change (zcmp Clt (-1) 0) with true. cbv beta iota. eapply exec_return.
      * ev.
      * ret. exists (vint (-1)). split.
        -- apply result_int.
        -- now left.
  - destruct r as [i|]; cbn [enc_conf].
    + (* c = i + 1: a conflict on clause i; return resolve(s, c - 1); *)
      rewrite (Hres i eq_refl).
      pose proof (Hcls i eq_refl) as Hi_lt.
      pose proof (r_lss_small _ _ _ _ _ _ _ (proj1 HRep)) as Hlss.
      assert (Hi: Int.sub (Int.repr (enc_conf (Some i))) (Int.repr 1)
                  = Int.repr (Z.of_nat i)).
      { cbn [enc_conf]. rewrite sub_repr. f_equal. lia. }
      run. eapply (exec_if_cmp _ _ _ Clt _ _ (Z.of_nat i + 1) 0).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * replace (zcmp Clt (Z.of_nat i + 1) 0) with false
          by (symmetry; cbn [zcmp]; apply Z.ltb_ge; lia).
        cbv beta iota. run.
        eapply (exec_if_cmp _ _ _ Cgt _ _ (Z.of_nat i + 1) 0).
        -- ev.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- unfold Small. lia.
        -- unfold Small. lia.
        -- replace (zcmp Cgt (Z.of_nat i + 1) 0) with true
             by (symmetry; cbn [zcmp]; apply Z.ltb_lt; lia).
           cbv beta iota.
           run. call resolve_fun. cbn [cast_int_int]. rewrite Hi. eapply call_weaken.
           ++ apply (resolve_correct S N lss x lims i
                       (fun (m'': mem) => TrailIn m'' S N pm)).
              split.
              ** assumption.
              ** split.
                 --- assumption.
                 --- assumption.
           ++ intros m' v Hv. normal.
              assert (Hz: exists (z: Z), v = vint z).
              { destruct Hv as [-> | Hv].
                - now exists (-1).
                - now apply coutcome_vint in Hv. }
              destruct Hz as [z ->]. eapply exec_return.
              ** ev.
              ** ret. exists (vint z). split.
                 --- apply result_int.
                 --- assumption.
    + (* c = 0: no conflict; the rest runs *)
      run. eapply (exec_if_cmp _ _ _ Clt _ _ 0 0).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * change (zcmp Clt 0 0) with false. cbv beta iota. run.
        eapply (exec_if_cmp _ _ _ Cgt _ _ 0 0).
        -- ev.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- unfold Small. lia.
        -- unfold Small. lia.
        -- change (zcmp Cgt 0 0) with false. cbv beta iota. run.
           apply Hrest.
           ++ reflexivity.
           ++ assumption.
Qed.

(* Assigning the decision l, after its decision level is open:

     {{ RepB xo lims' /\ Arr pool tp /\ l = key l' }}
       if (!assign(s, l, 0)) return -1;                               (assign_correct)
     {{ result = -1 (out of room) }}
       return 2;
     {{ result = 2 /\ Rep (assign xo l' no_reason) lims' }}                            *)
Lemma step_assign_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (pm: PA)
  (xo: Ctx) (lims': list nat) (l: Lit) (tp: nat -> Z) (tw tl: ident) (rest: statement)
  (le: temp_env) (m: mem),
  RepB m S N lss xo lims' -> Arr m (b_wpool S) (2 * npool S) tp ->
  PoolOf S N tp (wls xo) (fun (_ _: nat) => False) -> (extract l < N)%nat ->
  le ! _s = Some (sptr S) -> le ! tl = Some (vint (key l)) ->
  Exec ge le m (assign_stmt tw tl)
    (SeqK ge rest
       (Returns f_step (StepPost S N lss pm (CNext (assign xo l no_reason) lims')))).
Proof.
  intros S N lss pm xo lims' l tp tw tl rest le m HRep Apool Hpool Hl Hs Hlv.
  unfold assign_stmt.
  run. call assign_fun. eapply call_weaken.
  - apply (assign_correct S N lss xo lims' l no_reason tp). split.
    + assumption.
    + split.
      * assumption.
      * split.
        -- (* a decision has no reason *)
           cbn [ReasonBelow]. constructor.
        -- assumption.
  - intros m' v Hv. normal. destruct Hv as [-> | (-> & HRep' & Apool')].
    + (* assign gave up: return -1; *)
      eapply (exec_if_int _ _ _ _ 1).
      * ev.
      * reflexivity.
      * unfold Small. lia.
      * change (negb (Z.eqb 1 0)) with true. cbv beta iota. eapply exec_return.
        -- ev.
        -- ret. exists (vint (-1)). split.
           ++ apply result_int.
           ++ now left.
    + (* return 2; *)
      eapply (exec_if_int _ _ _ _ 0).
      * ev.
      * reflexivity.
      * unfold Small. lia.
      * change (negb (Z.eqb 0 0)) with false. cbv beta iota. run. eapply exec_return.
        -- ev.
        -- ret. exists (vint 2). split.
           ++ apply result_int.
           ++ right. split.
              ** reflexivity.
              ** split.
                 --- assumption.
                 --- exists tp. split.
                     +++ assumption.
                     +++ assumption.
Qed.

(* Deciding at the unassigned literal of alls at the cursor k: the decision level opens,
   and the literal with its phase is assigned.

     {{ Rep x2 lims /\ k < nlits /\ the literal alls[k] is unassigned }}
       int l = phase(s, s->alls[k]);                                   (phase_correct)
       s->cur = k;
       s->saved[s->dl] = k;
       s->lims[s->dl] = s->tlen;
       s->dl = s->dl + 1;                                             (rep_store_open)
     {{ RepB (open_level x2 k) (tlen x2 :: lims) /\ l = key (phase ...) }}
       ...                                                       (step_assign_correct) *)
Lemma step_decide_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (pm pm2: PA)
  (f: CNF) (x2: Ctx) (lims: list nat) (k: nat) (le: temp_env) (m: mem),
  Rep m S N lss x2 lims -> StepCore pm2 f x2 -> LimsOf lims pm2 -> (k < nlits x2)%nat ->
  lookup (vals x2) (tget (alls x2) k) = None ->
  le ! _s = Some (sptr S) -> le ! _k = Some (vint (Z.of_nat k)) ->
  Exec ge le m step_decide
    (SeqK ge step_end (Returns f_step (StepPost S N lss pm
      (CNext (assign (open_level x2 k) (phase (phs x2) (tget (alls x2) k)) no_reason)
         (tlen x2 :: lims))))).
Proof.
  intros S N lss pm pm2 f x2 lims k le m [HRep (tp & Apool & Hpool)] Hcore2 Hlims2 Hk
    Hundef Hs Hkv.
  pose proof (lims_on_trail _ _ _ _ Hcore2 Hlims2) as [_ Hlen2].
  pose proof HRep as HRep'. destruct HRep'.
  destruct a_alls as (ta & Aalls & Hta). destruct a_saved as (tsv & Asaved & Htsv).
  destruct a_lims as (tl & Alims & Htl). unpack.
  assert (Hl: (extract (tget (alls x2) k) < N)%nat) by (apply r_alls_atoms; lia).
  assert (Hla: (extract (phase (phs x2) (tget (alls x2) k)) < N)%nat)
    by (rewrite extract_phase; assumption).
  assert (Hlu: lookup (vals x2) (phase (phs x2) (tget (alls x2) k)) = None)
    by (apply phase_undef; assumption).
  pose proof (trail_room _ _ _ N _ Hcore2 r_tr_atoms Hlu Hla) as Hroom.
  assert (Hdl: (length lims < N)%nat) by lia.
  assert (Hkle: (k <= nlits x2)%nat) by lia.
  assert (Hdl1: Int.add (Int.repr (Z.of_nat (length lims))) (Int.repr 1) =
                Int.repr (Z.of_nat (Datatypes.S (length lims)))).
  { rewrite add_repr by lia. f_equal. lia. }
  unfold step_decide, f_step. cbn [fn_body drop_stmts first_stmt then_stmt].
  (* int l = phase(s, s->alls[k]); *)
  run. rewrite (Hta k) by lia. call phase_fun. eapply call_weaken.
  - apply (phase_correct S N lss x2 lims (tget (alls x2) k)). split.
    + assumption.
    + assumption.
  - intros m' v [-> ->]. normal. run.
    (* s->cur = k; *)
    eapply exec_store.
    + evl.
    + ev.
    + reflexivity.
    + reflexivity.
    + fofs. bound.
    + fofs. cbn [cast_int_int].
      destruct (fld_storable m (b_s S) 116 Mint32 _ (vint (Z.of_nat k)) r_cur)
        as [m1 Hst1].
      exists m1. split.
      * apply Hst1.
      * normal. carry Hst1 r_nodup. keep_mem m1.
        (* s->saved[s->dl] = k; *)
        run. eapply exec_store.
        -- evl.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- ofs. bound.
        -- ofs. cbn [cast_int_int].
           destruct (arr_storable m1 (b_saved S) N (length lims) tsv (Z.of_nat k)
                       Asaved Hdl) as [m2 Hst2].
           exists m2. split.
           ++ apply Hst2.
           ++ normal. carry Hst2 r_nodup. keep_mem m2.
              (* s->lims[s->dl] = s->tlen; *)
              run. eapply exec_store.
              ** evl.
              ** ev.
              ** reflexivity.
              ** reflexivity.
              ** ofs. bound.
              ** ofs. cbn [cast_int_int].
                 destruct (arr_storable m2 (b_lims S) N (length lims) tl
                             (Z.of_nat (tlen x2)) Alims Hdl) as [m3 Hst3].
                 exists m3. split.
                 --- apply Hst3.
                 --- normal. carry Hst3 r_nodup. keep_mem m3.
                     (* s->dl = s->dl + 1; *)
                     run. eapply exec_store.
                     +++ evl.
                     +++ ev.
                     +++ reflexivity.
                     +++ reflexivity.
                     +++ fofs. bound.
                     +++ fofs. cbn [cast_int_int]. ints.
                         destruct (fld_storable m3 (b_s S) 136 Mint32 _
                                     (vint (Z.of_nat (Datatypes.S (length lims)))) r_dl)
                           as [m4 Hst4].
                         exists m4. split.
                         *** apply Hst4.
                         *** normal. carry Hst4 r_nodup.
                             pose proof (rep_store_open m m1 m2 m3 m4 S N lss x2 lims k
                                           HRep Hkle Hdl Hst1 Hst2 Hst3 Hst4)
                               as HRepo.
                             apply (step_assign_correct S N lss pm _ _ _ tp _t'10 _l__1).
                             ---- apply HRepo.
                             ---- assumption.
                             ---- apply Hpool.
                             ---- assumption.
                             ---- tmp.
                             ---- tmp.
Qed.

(* Choosing a decision, after propagation without a conflict:

     {{ Rep x2 lims /\ t0 = tlen x }}
       int k = skip_from(s);                                       (skip_from_correct)
     {{ k = the next unassigned literal of alls from the cursor, or nlits }}
       if (k < s->nlits) { ... }                                 (step_decide_correct)
       if (s->tlen == t0) return 0;
     {{ result = 0: nothing was assigned, so the trail is still pm }}
       s->cur = k;                                                     (rep_store_cur)
       return 2;
     {{ result = 2 /\ Rep (with_cursor x2 k) lims }}                                   *)
Lemma step_choose_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (pm pm2: PA)
  (f: CNF) (x x2: Ctx) (lims: list nat) (le: temp_env) (m: mem),
  Rep m S N lss x2 lims -> StepCore pm2 f x2 -> LimsOf lims pm2 -> Extends pm pm2 ->
  PA.length pm = tlen x -> (tlen x <= N)%nat ->
  le ! _s = Some (sptr S) ->
  le ! _t0 = Some (vint (Z.of_nat (tlen x))) ->
  Exec ge le m step_choose
    (Returns f_step (StepPost S N lss pm (cstep_cursor x x2 lims))).
Proof.
  intros S N lss pm pm2 f x x2 lims le m HRep2 Hcore2 Hlims2 Hext Hlen Htx Hs Ht0.
  pose proof HRep2 as [HRep (tp & Apool & Hpool)].
  unfold step_choose, f_step. cbn [fn_body drop_stmts].
  (* int k = skip_from(s); *)
  run. call skip_from_fun. eapply call_weaken.
  - apply (skip_from_correct S N lss x2 lims). assumption.
  - intros m' v [-> ->]. normal.
    destruct (skip_from_spec (vals x2) f (alls x2) (nlits x2) (nlits x2 - cur x2)
                (cur x2)) as [Hc Hundef].
    { lia. }
    { apply Hcore2. }
    unfold cstep_cursor. cbv zeta.
    remember (skip_from (vals x2) (alls x2) (nlits x2) (nlits x2 - cur x2) (cur x2))
      as k eqn:Hk.
    pose proof (proj1 Hc) as Hkn.
    pose proof HRep as HRep'. destruct HRep'. unpack.
    (* if (k < s->nlits) *)
    run. eapply (exec_if_cmp _ _ _ Clt).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + unfold Small. lia.
    + unfold Small. lia.
    + destruct (Nat.lt_ge_cases k (nlits x2)) as [Hlt | Hge].
      * (* a literal to decide on *)
        replace (zcmp Clt (Z.of_nat k) (Z.of_nat (nlits x2))) with true
          by (symmetry; cbn [zcmp]; apply Z.ltb_lt; lia).
        replace (Nat.ltb k (nlits x2)) with true by (symmetry; now apply Nat.ltb_lt).
        cbv beta iota. apply (step_decide_correct S N lss pm pm2 f).
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- now apply Hundef.
        -- tmp.
        -- tmp.
      * (* all literals assigned *)
        replace (zcmp Clt (Z.of_nat k) (Z.of_nat (nlits x2))) with false
          by (symmetry; cbn [zcmp]; apply Z.ltb_ge; lia).
        replace (Nat.ltb k (nlits x2)) with false by (symmetry; now apply Nat.ltb_ge).
        cbv beta iota. run.
        (* if (s->tlen == t0) return 0; *)
        eapply (exec_if_cmp _ _ _ Ceq).
        -- ev.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- unfold Small. lia.
        -- unfold Small. lia.
        -- destruct (Nat.eqb_spec (tlen x2) (tlen x)) as [Heq | Hneq].
           ++ (* nothing was assigned: the trail is pm *)
              rewrite Heq.
              replace (zcmp Ceq (Z.of_nat (tlen x)) (Z.of_nat (tlen x))) with true
                by (symmetry; cbn [zcmp]; apply Z.eqb_refl).
              cbv beta iota. eapply exec_return.
              ** ev.
              ** ret. exists (vint 0). split.
                 --- apply result_int.
                 --- destruct (core_trail _ _ _ (step_core _ _ _ Hcore2)) as [Hl2 Htr2].
                     rewrite trail_lits_length in Hl2.
                     assert (Hpm: pm2 = pm).
                     { apply extends_same_length.
                       - assumption.
                       - congruence. }
                     subst pm2. right. split.
                     +++ reflexivity.
                     +++ split.
                         *** rewrite Hlen, <- Heq. assumption.
                         *** exists (fun (j: nat) => key (tget (tr x2) j)). split.
                             ---- assumption.
                             ---- intros j Hj. cbv beta. rewrite Htr2 by lia.
                                  reflexivity.
           ++ (* s->cur = k; return 2; *)
              replace (zcmp Ceq (Z.of_nat (tlen x2)) (Z.of_nat (tlen x))) with false
                by (symmetry; cbn [zcmp]; apply Z.eqb_neq; lia).
              cbv beta iota. run. eapply exec_store.
              ** evl.
              ** ev.
              ** reflexivity.
              ** reflexivity.
              ** fofs. bound.
              ** fofs. cbn [cast_int_int].
                 destruct (fld_storable m (b_s S) 116 Mint32 _ (vint (Z.of_nat k)) r_cur)
                   as [m1 Hst1].
                 exists m1. split.
                 --- apply Hst1.
                 --- normal. eapply exec_return.
                     +++ ev.
                     +++ exists (vint 2). split.
                         *** apply result_int.
                         *** right. split.
                             ---- reflexivity.
                             ---- split.
                                  ++++ apply (rep_store_cur m m1 S N lss x2 lims k HRep).
                                       **** lia.
                                       **** assumption.
                                  ++++ exists tp. split.
                                       **** apply (arr_store_other _ _ _ _ _ _ _ _ _
                                                     Apool Hst1).
                                            neq r_nodup.
                                       **** assumption.
Qed.

(* The literal the heuristic picks is an unassigned literal of f, so of an atom below
   the number of atoms. *)
Lemma picked_lit: forall (pm: PA) (f: CNF) (x: Ctx) (fuel: nat) (h: Heur) (l0: Lit),
  StepCore pm f x -> pick (vals x) (hr x) fuel = (h, Some l0) ->
  lookup (vals x) l0 = None /\ (extract l0 < nvars x)%nat.
Proof.
  intros pm f x fuel h l0 Hcore Hpick.
  destruct (pick_some _ _ _ _ _ Hpick) as [Hundef [a Ha]].
  pose proof (sc_dlit _ _ _ Hcore a l0 Ha) as Hl0.
  pose proof (max_atom_f_le f l0 (extract l0) Hl0 eq_refl) as Hmax.
  pose proof (sc_bound _ _ _ Hcore) as Hbound.
  split.
  - assumption.
  - lia.
Qed.

(* Deciding on the unassigned literal l0 of f the heuristic picked: the decision level
   opens at the cursor, and l0 with its phase is assigned.

     {{ Rep y lims /\ l0 is unassigned, of an atom below N /\ l0 = key l0 }}
       int l = phase(s, l0);                                           (phase_correct)
       s->saved[s->dl] = s->cur;
       s->lims[s->dl] = s->tlen;
       s->dl = s->dl + 1;                                         (rep_store_open_cur)
     {{ RepB (open_level y (cur y)) (tlen y :: lims) /\ l = key (phase ...) }}
       ...                                                       (step_assign_correct) *)
Lemma step_pick_decide_correct: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (pm pm2: PA) (f: CNF) (y: Ctx) (lims: list nat) (l0: Lit) (rest: statement)
  (le: temp_env) (m: mem),
  Rep m S N lss y lims -> StepCore pm2 f y -> LimsOf lims pm2 -> (extract l0 < N)%nat ->
  lookup (vals y) l0 = None ->
  le ! _s = Some (sptr S) -> le ! _l0 = Some (vint (key l0)) ->
  Exec ge le m step_pick_decide
    (SeqK ge rest (Returns f_step (StepPost S N lss pm
      (CNext (assign (open_level y (cur y)) (phase (phs y) l0) no_reason)
         (tlen y :: lims))))).
Proof.
  intros S N lss pm pm2 f y lims l0 rest le m [HRep (tp & Apool & Hpool)] Hcore2 Hlims2
    Hl Hundef Hs Hl0v.
  pose proof (lims_on_trail _ _ _ _ Hcore2 Hlims2) as [_ Hlen2].
  pose proof HRep as HRep'. destruct HRep'.
  destruct a_saved as (tsv & Asaved & Htsv). destruct a_lims as (tl & Alims & Htl).
  unpack.
  assert (Hla: (extract (phase (phs y) l0) < N)%nat)
    by (rewrite extract_phase; assumption).
  assert (Hlu: lookup (vals y) (phase (phs y) l0) = None)
    by (apply phase_undef; assumption).
  pose proof (trail_room _ _ _ N _ Hcore2 r_tr_atoms Hlu Hla) as Hroom.
  assert (Hdl: (length lims < N)%nat) by lia.
  assert (Hdl1: Int.add (Int.repr (Z.of_nat (length lims))) (Int.repr 1) =
                Int.repr (Z.of_nat (Datatypes.S (length lims)))).
  { rewrite add_repr by lia. f_equal. lia. }
  unfold step_pick_decide, f_step. cbn [fn_body drop_stmts first_stmt then_stmt].
  (* int l = phase(s, l0); *)
  run. call phase_fun. eapply call_weaken.
  - apply (phase_correct S N lss y lims l0). split.
    + assumption.
    + assumption.
  - intros m' v [-> ->]. normal.
    (* s->saved[s->dl] = s->cur; *)
    run. eapply exec_store.
    + evl.
    + ev.
    + reflexivity.
    + reflexivity.
    + ofs. bound.
    + ofs. cbn [cast_int_int].
      destruct (arr_storable m (b_saved S) N (length lims) tsv (Z.of_nat (cur y))
                  Asaved Hdl) as [m2 Hst2].
      exists m2. split.
      * apply Hst2.
      * normal. carry Hst2 r_nodup. keep_mem m2.
        (* s->lims[s->dl] = s->tlen; *)
        run. eapply exec_store.
        -- evl.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- ofs. bound.
        -- ofs. cbn [cast_int_int].
           destruct (arr_storable m2 (b_lims S) N (length lims) tl
                       (Z.of_nat (tlen y)) Alims Hdl) as [m3 Hst3].
           exists m3. split.
           ++ apply Hst3.
           ++ normal. carry Hst3 r_nodup. keep_mem m3.
              (* s->dl = s->dl + 1; *)
              run. eapply exec_store.
              ** evl.
              ** ev.
              ** reflexivity.
              ** reflexivity.
              ** fofs. bound.
              ** fofs. cbn [cast_int_int]. ints.
                 destruct (fld_storable m3 (b_s S) 136 Mint32 _
                             (vint (Z.of_nat (Datatypes.S (length lims)))) r_dl)
                   as [m4 Hst4].
                 exists m4. split.
                 --- apply Hst4.
                 --- normal. carry Hst4 r_nodup.
                     pose proof (rep_store_open_cur m m2 m3 m4 S N lss y lims
                                   HRep Hdl Hst2 Hst3 Hst4) as HRepo.
                     apply (step_assign_correct S N lss pm _ _ _ tp _t'7 _l).
                     +++ apply HRepo.
                     +++ assumption.
                     +++ apply Hpool.
                     +++ assumption.
                     +++ tmp.
                     +++ tmp.
Qed.

(* Choosing a decision, after propagation without a conflict: the heuristic picks a
   literal, and changes to h on the way.

     {{ Rep x2 lims /\ t0 = tlen x }}
       int l0 = pick(s);                                                (pick_correct)
     {{ Rep (with_heur x2 h) lims /\ l0 = enc_lit ol, for pick ... = (h, ol) }}
       if (l0 >= 0) { ... }                                 (step_pick_decide_correct)
     {{ ol = None }}
       ...                                                       (step_choose_correct) *)
Lemma step_pick_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (pm pm2: PA)
  (f: CNF) (x x2: Ctx) (lims: list nat) (le: temp_env) (m: mem),
  Rep m S N lss x2 lims -> StepCore pm2 f x2 -> LimsOf lims pm2 -> Extends pm pm2 ->
  PA.length pm = tlen x -> (tlen x <= N)%nat ->
  le ! _s = Some (sptr S) ->
  le ! _t0 = Some (vint (Z.of_nat (tlen x))) ->
  Exec ge le m step_pick
    (Returns f_step (StepPost S N lss pm (cstep_decide x x2 lims))).
Proof.
  intros S N lss pm pm2 f x x2 lims le m [HRep (tp & Apool & Hpool)] Hcore2 Hlims2 Hext
    Hlen Htx Hs Ht0.
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_nvars _ _ _ _ _ _ _ HRep) as Hnv.
  unfold cstep_decide. rewrite Hnv.
  unfold step_pick, f_step. cbn [fn_body drop_stmts].
  (* int l0 = pick(s); *)
  run. call pick_fun. eapply call_weaken.
  - apply (pick_correct (lt := []) S N lss x2 lims). assumption.
  - intros m1 v Hpost. normal. eapply exec_set.
    + ev.
    + normal.
      (* the heuristic changed, but not its literals to decide on *)
      pose proof (pick_dlit (vals x2) (hr x2) N) as Hd.
      destruct (pick (vals x2) (hr x2) N) as [h ol] eqn:Hpick.
      cbn [fst] in Hd. destruct Hpost as (HRep1 & -> & Hun1).
      transfer Hun1 Hnd. keep_mem m1.
      pose proof (step_core_heur pm2 f x2 h Hcore2 Hd) as Hcore3.
      (* if (l0 >= 0) *)
      run. eapply (exec_if_cmp _ _ _ Cge).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * destruct ol as [l0|].
        -- destruct (picked_lit pm2 f x2 N h l0 Hcore2 Hpick) as [_ Hl].
           rewrite Hnv in Hl. pose proof (key_small l0 N Hl HN).
           unfold Small. cbn [enc_lit]. lia.
        -- unfold Small. cbn [enc_lit]. lia.
      * unfold Small. lia.
      * destruct ol as [l0|].
        -- (* a literal picked: decide on it *)
           destruct (picked_lit pm2 f x2 N h l0 Hcore2 Hpick) as [Hundef0 Hl].
           rewrite Hnv in Hl. pose proof (key_small l0 N Hl HN) as Hkey.
           replace (zcmp Cge (enc_lit (Some l0)) 0) with true
             by (cbn [zcmp enc_lit]; symmetry; apply Z.leb_le; lia).
           cbv beta iota.
           apply (step_pick_decide_correct S N lss pm pm2 f (with_heur x2 h) lims l0).
           ++ split.
              ** assumption.
              ** exists tp. split.
                 --- assumption.
                 --- apply Hpool.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ tmp.
           ++ tmp.
        -- (* nothing picked: decide by the cursor *)
           replace (zcmp Cge (enc_lit None) 0) with false by reflexivity.
           cbv beta iota. apply exec_skip. normal.
           apply (step_choose_correct S N lss pm pm2 f x (with_heur x2 h) lims).
           ++ split.
              ** assumption.
              ** exists tp. split.
                 --- assumption.
                 --- apply Hpool.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ tmp.
           ++ tmp.
Qed.

(* After the short clauses, without a conflict among them: they are cleared, and
   propagation runs.

     {{ Rep x1 lims /\ t0 = tlen x }}
       s->nshorts = 0;                                              (rep_store_shorts)
     {{ Rep (clear_shorts x1) lims }}
       c = propagate(s);                                           (propagate_correct)
       if (c < 0) return -1;
       if (c > 0) return resolve(s, c - 1);                      (on_conflict_correct)
     {{ Rep x2 lims, after propagation without a conflict }}
       ...                                                         (step_pick_correct) *)
Lemma step_propagate_correct: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (pm pm1: PA) (f: CNF) (x x1: Ctx) (lims: list nat) (le: temp_env) (m: mem),
  Rep m S N lss x1 lims -> StepCore pm1 f x1 -> WellFormed (state pm1 f) ->
  LimsOf lims pm1 -> Extends pm pm1 -> (forall (i: nat), tget (cmap x1) i <> Some []) ->
  PA.length pm = tlen x -> (tlen x <= N)%nat ->
  le ! _s = Some (sptr S) ->
  le ! _t0 = Some (vint (Z.of_nat (tlen x))) ->
  Exec ge le m step_propagate
    (Returns f_step (StepPost S N lss pm (cstep_propagate x x1 lims))).
Proof.
  intros S N lss pm pm1 f x x1 lims le m [HRep (tp & Apool & Hpool)] Hcore1 Hwf1 Hlims1
    Hext1 Hne1 Hlen Htx Hs Ht0.
  destruct (reached_prop pm1 f x1 lims Hcore1 Hwf1 Hlims1 Hne1)
    as (pm2 & Hcore2 & Hlims2 & Hext2).
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_nvars _ _ _ _ _ _ _ HRep) as Hnv.
  pose proof (r_nshorts _ _ _ _ _ _ _ HRep) as Fns.
  pose proof (a_shorts _ _ _ _ _ _ _ HRep) as (tsh & Ash & _).
  unfold cstep_propagate. rewrite Hnv in Hcore2 |- *.
  unfold step_propagate, f_step. cbn [fn_body drop_stmts].
  (* s->nshorts = 0; *)
  run. eapply exec_store.
  - evl.
  - ev.
  - reflexivity.
  - reflexivity.
  - fofs. bound.
  - fofs. cbn [cast_int_int].
    destruct (fld_storable m (b_s S) 96 Mint32 _ (vint 0) Fns) as [m1 Hst1].
    exists m1. split.
    + apply Hst1.
    + normal.
      assert (HRep1: RepB m1 S N lss (clear_shorts x1) lims).
      { apply (rep_store_shorts m m1 S N lss x1 lims [] tsh HRep Ash).
        - intros q Hq. cbn [length] in Hq. lia.
        - cbn [length]. lia.
        - intros i [].
        - apply Hst1. }
      assert (Apool1: Arr m1 (b_wpool S) (2 * npool S) tp).
      { apply (arr_store_other _ _ _ _ _ _ _ _ _ Apool Hst1). neq Hnd. }
      (* c = propagate(s); *)
      run. call propagate_fun. eapply call_weaken.
      * apply (propagate_correct S N lss (clear_shorts x1) lims). split.
        -- assumption.
        -- exists tp. split.
           ++ assumption.
           ++ apply Hpool.
      * intros m2 v Hv. normal. eapply exec_set.
        -- ev.
        -- normal.
           destruct (propagate_t (Datatypes.S N) (clear_shorts x1)) as [x2 r2] eqn:Hp.
           cbn [fst snd] in *.
           pose proof (lims_on_trail _ _ _ _ Hcore2 Hlims2) as [Hon2 _].
           (* if (c < 0) return -1; if (c > 0) return resolve(s); *)
           apply (on_conflict_correct S N lss pm x2 lims r2 _ _ _ v).
           ++ tmp.
           ++ tmp.
           ++ assumption.
           ++ assumption.
           ++ intros i ->. reflexivity.
           ++ intros -> HRep2.
              apply (step_pick_correct S N lss pm pm2 f).
              ** assumption.
              ** assumption.
              ** assumption.
              ** now apply extends_trans with pm1.
              ** assumption.
              ** assumption.
              ** tmp.
              ** tmp.
Qed.

(* step makes the step of cstep on the represented context x, or gives up: it returns
   -1 when out of room, 0 to stop (the trail is pm), 1 for fail, and 2 with the next
   context.

     {{ Rep x lims /\ StepInv (state pm f) x /\ LimsOf lims pm }}
       int t0 = s->tlen;
       int c = check_shorts(s);                                 (check_shorts_correct)
       if (c < 0) return -1;
       if (c > 0) return resolve(s, c - 1);                      (on_conflict_correct)
     {{ Rep x1 lims, after the short clauses without a conflict }}
       ...                                                    (step_propagate_correct)
     {{ StepPost pm (cstep x lims) }}                                  (cstep_parts) *)
Lemma step_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (pm: PA) (f: CNF),
  {{ m | Rep m S N lss x lims /\ StepInv (state pm f) x /\ LimsOf lims pm }}
    f_step(sptr S)
  {{ m', v | v = vint (-1) \/
             COutcome S N lss (fun (m'': mem) => TrailIn m'' S N pm) (cstep x lims)
               m' v }}.
Proof.
  intros S N lss x lims pm f m (HRep & Hinv & Hlims).
  destruct (reached_shorts pm f x lims Hinv Hlims)
    as (pm1 & Hcore1 & Hlims1 & Hext1 & Hwf1 & Hnonempty1).
  pose proof (Rep.r_tlen_le _ _ _ _ _ _ _ (proj1 HRep)) as Htx.
  assert (Hlen: PA.length pm = tlen x).
  { destruct Hinv as [Hcore _].
    destruct (core_trail _ _ _ (step_core _ _ _ Hcore)) as [Hl _].
    rewrite trail_lits_length in Hl. symmetry. assumption. }
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_step. cbn [fn_body fn_return].
    pose proof (r_tlen _ _ _ _ _ _ _ (proj1 HRep)) as Ftlen.
    (* int t0 = s->tlen; int c = check_shorts(s); *)
    run. clear Ftlen. call check_shorts_fun. eapply call_weaken.
    + apply (check_shorts_correct S N lss x lims). assumption.
    + intros m1 v Hv. normal. eapply exec_set.
      * ev.
      * normal. rewrite cstep_parts.
        destruct (check_shorts_t (shorts x) x) as [x1 r1] eqn:Hcs. cbn [fst snd] in *.
        pose proof (lims_on_trail _ _ _ _ Hcore1 Hlims1) as [Hon1 _].
        (* if (c < 0) return -1; if (c > 0) return resolve(s); *)
        apply (on_conflict_correct S N lss pm x1 lims r1 _ _ _ v).
        -- tmp.
        -- tmp.
        -- assumption.
        -- assumption.
        -- intros i ->. reflexivity.
        -- intros -> HRep1.
           apply (step_propagate_correct S N lss pm pm1 f).
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ now apply Hnonempty1.
           ++ assumption.
           ++ assumption.
           ++ tmp.
           ++ tmp.
Qed.

Lemma step_fun: exists (b: block),
  Genv.find_symbol ge _step = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_step).
Proof. apply find_fun. reflexivity. Qed.
