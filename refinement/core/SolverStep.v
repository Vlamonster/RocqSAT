From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Relations.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import State.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import Entails.
From RocqSAT Require Import Trans.
From RocqSAT Require Import Strategy.
From RocqSAT.rules Require Import Fail.
From RocqSAT.rules Require Import Backtrack.
From RocqSAT.rules Require Import Backjump.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Search.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import Heur.
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement Require Import Analysis.
From RocqSAT.refinement Require Import Step.

(* The solver, whose step cstep the C solver computes on the context: check the short
   clauses, propagate with two watched literals (Propagate.v) and decide on the literal
   the heuristic picks, or else at the cursor (Step.v); on a conflict, fail without
   decisions, and otherwise analyse it (Analysis.v) and backjump, asserting the literal
   the analysis gives, with the analysed clause as its reason if there is room; when the
   analysis gives no literal, flip the last decision. The state is the trail of the
   context (trail): cstep_spec says what a step does to it, and step_strategy that the
   solver is a strategy for DPLL_BJ. *)

Section SplitLevels.
  (* m split as ⟨mt; d ++ n⟩ at the decision d with k decisions after it. *)
  Fixpoint split_levels (k: nat) (m: PA): option (PA * Lit * PA) :=
  match m with
  | ⟨⟩      => None
  | ⟨m', x⟩ =>
    match split_levels k m' with
    | Some (mt, d, n) => Some (mt, d, ⟨n, x⟩)
    | None            => None
    end
  | ⟨m'; x⟩ =>
    match k with
    | 0    => Some (m', x, ⟨⟩)
    | S k' =>
      match split_levels k' m' with
      | Some (mt, d, n) => Some (mt, d, ⟨n; x⟩)
      | None            => None
      end
    end
  end.

  (* split_levels k m splits m. *)
  Lemma split_levels_spec: forall (k: nat) (m mt n: PA) (d: Lit),
    split_levels k m = Some (mt, d, n) -> m = ⟨mt; d ++ n⟩.
  Proof.
    intros k m. revert k.
    induction m as [|m IH x|m IH x]; intros k mt n d Hsplit; simpl in Hsplit.
    - discriminate.
    - destruct (split_levels k m) as [[[mt' d'] n']|] eqn:Hm.
      + injection Hsplit as <- <- <-. apply IH in Hm as ->. reflexivity.
      + discriminate.
    - destruct k as [|k].
      + now injection Hsplit as <- <- <-.
      + destruct (split_levels k m) as [[[mt' d'] n']|] eqn:Hm.
        * injection Hsplit as <- <- <-. apply IH in Hm as ->. reflexivity.
        * discriminate.
  Qed.

  (* split_levels k leaves k decisions after the split. *)
  Lemma split_levels_decisions: forall (k: nat) (m mt n: PA) (d: Lit),
    split_levels k m = Some (mt, d, n) -> decisions n = k.
  Proof.
    intros k m. revert k.
    induction m as [|m IH x|m IH x]; intros k mt n d Hsplit; simpl in Hsplit.
    - discriminate.
    - destruct (split_levels k m) as [[[mt' d'] n']|] eqn:Hm.
      + injection Hsplit as <- <- <-. simpl. now apply (IH k mt' n' d').
      + discriminate.
    - destruct k as [|k].
      + now injection Hsplit as <- <- <-.
      + destruct (split_levels k m) as [[[mt' d'] n']|] eqn:Hm.
        * injection Hsplit as <- <- <-. simpl. f_equal. now apply (IH k mt' n' d').
        * discriminate.
  Qed.
  #[global] Arguments split_levels_decisions {k m mt n d}.

  (* The positions of the decisions where split_levels splits. *)
  Lemma split_levels_lims: forall (k: nat) (m mt n: PA) (d: Lit) (lims: list nat),
    LimsOf lims m -> split_levels k m = Some (mt, d, n) ->
    nth_error lims k = Some (PA.length mt) /\ LimsOf (skipn (S k) lims) mt.
  Proof.
    intros k m. revert k.
    induction m as [|m IH x|m IH x]; intros k mt n d lims Hlims Hsplit;
      simpl in Hlims, Hsplit.
    - discriminate.
    - destruct (split_levels k m) as [[[mt' d'] n']|] eqn:Hm.
      + injection Hsplit as -> -> <-. now apply (IH k mt n' d lims).
      + discriminate.
    - destruct lims as [|j lims].
      + contradiction.
      + destruct Hlims as [-> Hlims]. destruct k as [|k].
        * injection Hsplit as <- <- <-. now split.
        * destruct (split_levels k m) as [[[mt' d'] n']|] eqn:Hm.
          -- injection Hsplit as -> -> <-. now apply (IH k mt n' d lims).
          -- discriminate.
  Qed.
  #[global] Arguments split_levels_lims {k m mt n d lims}.

  (* Without a split at k, there is no decision position k either. *)
  Lemma split_levels_lims_none: forall (k: nat) (m: PA) (lims: list nat),
    LimsOf lims m -> split_levels k m = None -> nth_error lims k = None.
  Proof.
    intros k m. revert k.
    induction m as [|m IH x|m IH x]; intros k lims Hlims Hsplit; simpl in Hlims, Hsplit.
    - subst lims. now destruct k.
    - destruct (split_levels k m) as [[[mt' d'] n']|] eqn:Hm.
      + discriminate.
      + now apply IH.
    - destruct lims as [|j lims].
      + contradiction.
      + destruct Hlims as [_ Hlims]. destruct k as [|k].
        * discriminate.
        * destruct (split_levels k m) as [[[mt' d'] n']|] eqn:Hm.
          -- discriminate.
          -- simpl. now apply IH.
  Qed.
  #[global] Arguments split_levels_lims_none {k m lims}.
End SplitLevels.

(* The outcome of a step on the context: stop, fail, or the next context. *)
Inductive CResult: Type :=
| CStop
| CFail
| CNext (x: Ctx).

(* Flip the last decision, at trail position j0: without lower literals, go back to the
   level before it and assert its negation. *)
Definition flip (x: Ctx) (j0: nat): CResult :=
match saved x with
| c0 :: st =>
  CNext (assign (back (x <| lower := [] |>) j0 c0 st (dl x - 1) (tl (lims x)))
           (¬tget (tr x) j0) no_reason)
| []       => CStop
end.

(* Resolve a conflict on clause i: fail without decisions; otherwise decay the bump and
   analyse the conflict from the last decision, at trail position j0, and unmark the lower
   literals; with a literal u to assert, unmark it and go back to the level mx the
   analysis gives, asserting u with the analysed clause as its reason; flip the last
   decision when there is no such literal or level. *)
Definition resolve (x: Ctx) (i: nat): CResult :=
match lims x with
| []          => CFail
| j0 :: lims0 =>
  match analyze (x <| hr := decay (hr x) (nvars x) |>) i (dl x) j0 with
  | (x1, ou) =>
    match unmark_lower x1 with
    | (x2, mx) =>
      match ou with
      | Some u =>
        let x3 := x2 <| mrk := tset (mrk x2) (lit_key u) false |> in
        if mx <? dl x then
          match nth_error (lims x) (dl x - S mx) with
          | Some j =>
            match skipn (dl x - S mx) (saved x) with
            | c0 :: st =>
              match push_reason (back x3 j c0 st mx (skipn (S (dl x - S mx)) (lims x))) u
              with
              | (x4, r) => CNext (assign (x4 <| lower := [] |>) u r)
              end
            | []       => flip x3 j0
            end
          | None   => flip x3 j0
          end
        else flip x3 j0
      | None   => flip x2 j0
      end
    end
  end
end.

(* One step: check the short clauses and propagate; on a conflict resolve, and otherwise
   decide on the literal pick gives, or else at the cursor, or stop when nothing is left
   to decide and the trail did not grow. *)
Definition cstep (x: Ctx): CResult :=
match check_shorts (shorts x) x with
| (x1, Some i) => resolve x1 i
| (x1, None)   =>
  match propagate (S (nvars x1)) (x1 <| shorts := [] |>) with
  | (x2, Some i) => resolve x2 i
  | (x2, None)   =>
    match pick (vals x2) (hr x2) (nvars x2) with
    | (h, Some l0) =>
      CNext (assign (open_level (x2 <| hr := h |>) (cur x2)) (phase (phs x2) l0)
               no_reason)
    | (h, None)    =>
      let x3 := x2 <| hr := h |> in
      let c := next_undef x3 in
      if c <? nlits x3 then
        CNext (assign (open_level x3 c) (phase (phs x3) (tget (alls x3) c)) no_reason)
      else if Nat.eqb (tlen x3) (tlen x) then CStop else CNext (x3 <| cur := c |>)
    end
  end
end.

(* The marks without that of the literal to assert, if there is one. *)
Definition unmark_opt (mk: Table bool) (ou: option Lit): Table bool :=
match ou with
| Some u => tset mk (lit_key u) false
| None   => mk
end.

(* Unmarking the lower literals changes only the marks. *)
Lemma unmark_lower_analysed: forall (x1 x2: Ctx) (mx: nat),
  unmark_lower x1 = (x2, mx) -> Analysed x1 x2 /\ lower x2 = lower x1.
Proof.
  intros x1 x2 mx Hun. unfold unmark_lower in Hun.
  apply unmark_lits_spec in Hun as [Hx2 _]. split.
  - split.
    + rewrite Hx2. reflexivity.
    + rewrite Hx2. reflexivity.
  - rewrite Hx2. reflexivity.
Qed.

(* The level unmark_lower gives bounds the levels of the lower literals. *)
Lemma unmark_lower_levels: forall (x1 x2: Ctx) (mx: nat),
  unmark_lower x1 = (x2, mx) -> forall (y: Lit), In y (lower x1) -> level x1 y <= mx.
Proof.
  intros x1 x2 mx Hun. unfold unmark_lower in Hun.
  apply unmark_lits_spec in Hun as (_ & _ & _ & Hle & _). assumption.
Qed.

(* If only the lower literals and the literal to assert are marked, unmarking both
   leaves no literal marked. *)
Lemma unmark_lower_unmarked: forall (x1 x2: Ctx) (ou: option Lit) (mx: nat),
  (forall (y: Lit), tget (mrk x1) (lit_key y) = true -> In y (lower x1) \/ ou = Some y) ->
  unmark_lower x1 = (x2, mx) -> Unmarked (unmark_opt (mrk x2) ou).
Proof.
  intros x1 x2 ou mx Hmarked Hun. unfold unmark_lower in Hun.
  destruct (unmark_lits_spec (lower x1) x1 x2 0 mx Hun) as (_ & Hcleared & Hother & _).
  assert (Hmk2: forall (y: Lit), tget (mrk x2) (lit_key y) = true -> ou = Some y).
  { intros y Hy. destruct (in_dec Lit.eq_dec y (lower x1)) as [Hin | Hnot_in].
    - rewrite Hcleared in Hy by assumption. discriminate.
    - rewrite Hother in Hy.
      + destruct (Hmarked y Hy) as [Hin | Hou].
        * contradiction.
        * assumption.
      + intros z Hz Heq. apply lit_key_inj in Heq. congruence. }
  destruct ou as [u|]; cbn [unmark_opt].
  - intros y. rewrite tget_tset.
    destruct (Nat.eq_dec (lit_key u) (lit_key y)) as [Heq | Hne].
    + reflexivity.
    + destruct (tget (mrk x2) (lit_key y)) eqn:Hy.
      * apply Hmk2 in Hy. injection Hy as ->. contradiction.
      * reflexivity.
  - intros y. destruct (tget (mrk x2) (lit_key y)) eqn:Hy.
    + apply Hmk2 in Hy. discriminate.
    + reflexivity.
Qed.

(* What a step with outcome cr does from the state m f: it stops only at a final state,
   it fails by a strict derivation, and it goes on by one to a consistent context, whose
   trail is the next state. *)
Definition StepOk (m: PA) (f: CNF) (cr: CResult): Prop :=
match cr with
| CStop    => Final Basic (state m f)
| CFail    => state m f ==>+[DPLL_BJ] fail
| CNext x' =>
  state m f ==>+[DPLL_BJ] state (trail x') f /\ StepInv (state (trail x') f) x'
end.

(* A strict derivation to a state consistent with x' is a step to x'. *)
Lemma next_ok: forall (m m': PA) (f: CNF) (x': Ctx),
  WellFormed (state m f) -> Entails f m -> state m f ==>+[DPLL_BJ] state m' f ->
  StepCore m' f x' -> StepOk m f (CNext x').
Proof.
  intros m m' f x' Hwf Hentails Hplus Hcore. cbn [StepOk].
  rewrite <- (step_core_trail Hcore). split.
  - assumption.
  - now apply (step_inv_after m m' f x').
Qed.

(* What resolving a conflict in the state m f with outcome cr does: it never stops, it
   fails by a step, and it goes on by a step to a consistent context. *)
Definition ResolveOk (m: PA) (f: CNF) (cr: CResult): Prop :=
match cr with
| CStop    => False
| CFail    => state m f ==>[DPLL_BJ] fail
| CNext x' => exists (m': PA), state m f ==>[DPLL_BJ] state m' f /\ StepCore m' f x'
end.

(* Going back without lower literals is going back and then dropping them. *)
Lemma back_lower: forall (x: Ctx) (lt: list Lit) (j c: nat) (st: list nat) (d: nat)
  (ls: list nat),
  back (x <| lower := lt |>) j c st d ls = (back x j c st d ls) <| lower := lt |>.
Proof. reflexivity. Qed.

(* Flipping the last decision l, at position PA.length m' of the trail, after an analysis
   of x that left the context xa: a Backjump step, to a consistent context. *)
Lemma flip_spec: forall (m' n: PA) (f: CNF) (x xa: Ctx) (l: Lit) (c: Clause),
  StepInv (state ⟨m'; l ++ n⟩ f) x -> NoDecisions n -> Analysed x xa ->
  Unmarked (mrk xa) -> c ∈ f -> c_eval ⟨m'; l ++ n⟩ c = Some false ->
  exists (x': Ctx), flip xa (PA.length m') = CNext x' /\
    state ⟨m'; l ++ n⟩ f ==>[DPLL_BJ] state ⟨m', (¬l)⟩ f /\ StepCore ⟨m', (¬l)⟩ f x'.
Proof.
  intros m' n f x xa l c [Hcore [Hwf Hentails]] Hno_dec Hxa Hmk Hc_in_f Hc_false.
  pose proof Hcore
    as [[[Hvals Hfresh Htrail _ _ Hdl _] _ _ _ _ _] _ _ Hsaved _ _ _ _ _ _ Hlims].
  (* the analysis keeps what flip reads *)
  pose proof Hxa as [Hxa_eq _].
  assert (Hsv: saved xa = saved x) by (rewrite Hxa_eq; reflexivity).
  assert (Htr: tr xa = tr x) by (rewrite Hxa_eq; reflexivity).
  assert (Hdla: dl xa = dl x) by (rewrite Hxa_eq; reflexivity).
  assert (Hla: lims xa = lims x) by (rewrite Hxa_eq; reflexivity).
  destruct (saved_c_split f (alls x) (nlits x) m' n l (saved x) Hsaved)
    as (c1 & st1 & Hskip & Hc1 & Hst1).
  rewrite no_decisions_zero in Hskip by assumption. simpl in Hskip.
  unfold flip. rewrite Hsv, Hskip. eexists. split.
  - reflexivity.
  - destruct (fresh_split m' n l Hfresh) as [_ Hl]. split.
    + apply (t_step Backjump).
      * right. right. right. now left.
      * apply backtrack_backjump.
        -- assumption.
        -- assumption.
        -- now apply (r_backtrack m' n f c l).
    + (* l is at position PA.length m', and the levels from it on go *)
      destruct (trail_of_snoc (tr x) _ m' ⟨m'; l⟩ l eq_refl
        (trail_of_prefix (tr x) (tlen x) ⟨m'; l⟩ n Htrail)) as (_ & Htl & _).
      assert (Hdl': dl x - 1 = decisions m').
      { rewrite Hdl, decisions_app, (no_decisions_zero n Hno_dec). simpl. lia. }
      rewrite Htr, Htl, Hdla, Hla, Hdl', back_lower.
      apply (jump_core m' n f x xa l (¬l) c1 st1 (tl (lims x))).
      * assumption.
      * assumption.
      * assumption.
      * now apply l_eval_neg_none_iff in Hl.
      * assumption.
      * assumption.
      * (* the positions of the decisions before l *)
        destruct (lims_split (lims x) m' n l Hlims) as (lims' & Hskip_l & Hlims' & _).
        rewrite no_decisions_zero in Hskip_l by assumption. simpl in Hskip_l.
        now rewrite Hskip_l.
      * left. split.
        -- reflexivity.
        -- reflexivity.
Qed.

(* Resolving a conflict on a false clause is a Fail or Backjump step, to a consistent
   context. *)
Lemma resolve_spec: forall (m: PA) (f: CNF) (x: Ctx) (i: nat),
  StepInv (state m f) x -> ClauseFalse x i -> ResolveOk m f (resolve x i).
Proof.
  intros m f x i Hinv Hconflict. pose proof Hinv as [Hcore [Hwf Hentails]].
  pose proof Hconflict as [ls [Hi Hfalse]].
  pose proof Hcore as [Hprop _ _ Hsaved _ _ Hmarks _ [Hslots _ _] Hdlit Hlims Hlow].
  pose proof (sc_prop Hcore) as [Hcore0 _ _ _ _ _].
  pose proof Hcore0 as [Hvals Hfresh Htrail Hsound _ Hdl Htrace].
  unfold resolve. pose proof Hi as Hi'. apply Hsound in Hi' as [c [Hc_in_f Hiff]].
  assert (Hc_false: c_eval m c = Some false).
  { apply c_eval_false_iff. intros l Hl. rewrite <- Hvals. apply Hfalse.
    now apply Hiff. }
  destruct (split_last_decision m) as [[m' l]|] eqn:Hsplit.
  2: { (* Fail: without decisions there are no positions of decisions *)
    apply PA.split_last_decision_none_iff in Hsplit.
    rewrite (lims_none (lims x) m Hlims Hsplit).
    cbn [ResolveOk]. apply (t_step Fail).
    - now left.
    - now apply (r_fail m f c). }
  apply PA.split_last_decision_some_iff in Hsplit as [n [-> Hno_dec]].
  (* the last decision l is at position PA.length m' *)
  destruct (lims_split (lims x) m' n l Hlims) as (lims' & Hskip_l & _ & _).
  rewrite no_decisions_zero in Hskip_l by assumption. simpl in Hskip_l.
  rewrite Hskip_l in Hlims |- *.
  assert (Hd: dl x = S (decisions m')).
  { rewrite Hdl, decisions_app, (no_decisions_zero n Hno_dec). simpl. lia. }
  rewrite Hd.
  (* The analysis, from the decayed heuristic *)
  destruct (analyze (x <| hr := decay (hr x) (nvars x) |>) i (S (decisions m'))
              (PA.length m')) as [x1 ou] eqn:Han.
  destruct (analyze_spec f x m' n l Hcore0 Hno_dec Hslots (decay (hr x) (nvars x)) i
              x1 ou Hconflict Hmarks Hlow Han)
    as (Hmarked & Hlower & Hassert).
  assert (Hx1: Analysed x x1).
  { apply analysed_trans with (x <| hr := decay (hr x) (nvars x) |>).
    - split.
      + reflexivity.
      + apply decay_dlit.
    - now apply analyze_analysed in Han. }
  destruct (unmark_lower x1) as [x2 mx] eqn:Hun.
  destruct (unmark_lower_analysed x1 x2 mx Hun) as [Hx12 Hlow2].
  pose proof (unmark_lower_levels x1 x2 mx Hun) as Hle.
  pose proof (unmark_lower_unmarked x1 x2 ou mx Hmarked Hun) as Hmk2.
  rewrite <- Hlow2 in Hlower, Hassert, Hle.
  assert (Hx2: Analysed x x2) by now apply analysed_trans with x1.
  (* Without a jump, the last decision is flipped. *)
  assert (Hfallback: forall (xa: Ctx), Analysed x xa -> Unmarked (mrk xa) ->
            ResolveOk ⟨m'; l ++ n⟩ f (flip xa (PA.length m'))).
  { intros xa Hxa Hmka.
    destruct (flip_spec m' n f x xa l c Hinv Hno_dec Hxa Hmka Hc_in_f Hc_false)
      as (x' & Hflip & Hstep & Hcore').
    rewrite Hflip. now exists ⟨m', (¬l)⟩. }
  destruct ou as [u|].
  2: { apply Hfallback.
       - assumption.
       - assumption. }
  cbv zeta.
  set (x3 := x2 <| mrk := tset (mrk x2) (lit_key u) false |>).
  assert (Hx3: Analysed x x3).
  { apply analysed_trans with x2.
    - assumption.
    - split.
      + reflexivity.
      + reflexivity. }
  destruct (mx <? S (decisions m')) eqn:Hmx.
  2: { apply Hfallback.
       - assumption.
       - assumption. }
  apply Nat.ltb_lt in Hmx.
  destruct (split_levels (S (decisions m') - S mx) ⟨m'; l ++ n⟩)
    as [[[mt d] n']|] eqn:Hsplit.
  2: { rewrite (split_levels_lims_none Hlims Hsplit). apply Hfallback.
       - assumption.
       - assumption. }
  destruct (split_levels_lims Hlims Hsplit) as [Hnth Hlims_mt].
  rewrite Hnth.
  destruct (skipn (S (decisions m') - S mx) (saved x)) as [|c0 st] eqn:Hskip.
  1: { apply Hfallback.
       - assumption.
       - assumption. }
  (* The backjump: the analysed clause asserts u at level mx *)
  pose proof (split_levels_decisions Hsplit) as Hdec_n.
  apply split_levels_spec in Hsplit.
  assert (Hdec_mt: decisions mt = mx).
  { pose proof (f_equal decisions Hsplit) as Hdec.
    rewrite !decisions_app, (no_decisions_zero n Hno_dec) in Hdec.
    simpl in Hdec. lia. }
  destruct (Hassert u eq_refl) as [Hent_u (q & Hq & Hu_eq)].
  assert (Hu_false: l_eval ⟨m'; l ++ n⟩ u = Some false).
  { rewrite Hu_eq. apply (trail_neg_false _ f x).
    - assumption.
    - lia. }
  assert (Hu_lv: level x u = S (decisions m')).
  { rewrite Hu_eq, extract_neg. apply (seg_level f x m' n l Hcore0 Hno_dec). lia. }
  pose proof Hx1 as [Hx1_eq _].
  assert (Hlv1: lvl x1 = lvl x) by (rewrite Hx1_eq; reflexivity).
  rewrite Hlv1 in Hle.
  rewrite Hsplit in Hvals, Hfresh, Htrace, Hlower, Hu_false, Hc_false, Hwf, Hcore,
    Hsaved.
  destruct (push_reason (back x3 (PA.length mt) c0 st mx
                           (skipn (S (S (decisions m') - S mx)) (PA.length m' :: lims')))
              u) as [x4 r] eqn:Hpush.
  assert (Hlt_false: forall (y: Lit), In y (lower x2) -> l_eval mt y = Some false).
  { intros y Hy.
    apply (false_before mt n' d y Hfresh Htrace).
    - now apply Hlower.
    - rewrite Hdec_mt. now apply Hle. }
  assert (Hu_undef: l_eval mt u = None).
  { apply (undef_before mt n' d u Hfresh Htrace).
    - assumption.
    - lia. }
  rewrite Hsplit. cbn [ResolveOk]. exists ⟨mt, u⟩. split.
  - apply (t_step Backjump).
    + right. right. right. now left.
    + apply (r_backjump mt n' f c (clause_of (lower x2 ++ [u])) d u).
      * assumption.
      * assumption.
      * now apply entailed_consequence.
      * apply clause_of_spec, in_or_app. right. now left.
      * apply c_eval_false_iff. intros y Hy. apply Clause.remove_spec in Hy as [Hy Hne].
        apply clause_of_spec, in_app_iff in Hy as [Hy | [Hy | []]].
        -- now apply Hlt_false.
        -- now symmetry in Hy.
      * assumption.
      * destruct Hwf as [_ Hbounded]. apply l_eval_false_in, Hbounded in Hu_false.
        rewrite Neg.involutive in Hu_false. now apply or_comm.
  - destruct (saved_c_split f (alls x) (nlits x) mt n' d (saved x) Hsaved)
      as (c1 & st1 & Hskip1 & Hc1 & Hst1).
    rewrite Hdec_n, Hskip in Hskip1. injection Hskip1 as <- <-.
    apply (jump_core mt n' f x x3 d u c0 st
             (skipn (S (S (decisions m') - S mx)) (PA.length m' :: lims')) x4 r).
    + assumption.
    + assumption.
    + apply Hmk2.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + right. split.
      * now rewrite Hdec_mt.
      * split.
        -- apply (entailed_incl f (lower x2 ++ [u])).
           ++ assumption.
           ++ intros y Hy. apply in_app_iff in Hy as [Hy | [<- | []]].
              ** right. apply Hy.
              ** now left.
        -- apply Hlt_false.
Qed.

(* Resolving a conflict reached by a derivation from m is a step from m. *)
Lemma after_resolve: forall (m m1: PA) (f: CNF) (x1: Ctx) (i: nat),
  WellFormed (state m f) ->
  Entails f m ->
  state m f ==>*[DPLL_BJ] state m1 f ->
  StepCore m1 f x1 ->
  (ClauseFalse x1 i) ->
  StepOk m f (resolve x1 i).
Proof.
  intros m m1 f x1 i Hwf Hentails Hder Hcore Hfalse.
  assert (Hinv1: StepInv (state m1 f) x1).
  { split.
    - assumption.
    - split.
      + now apply (derivation_well_formed DPLL_BJ m m1 f f).
      + now apply (derivation_entails DPLL_BJ m m1 f f). }
  pose proof (resolve_spec m1 f x1 i Hinv1 Hfalse) as Hres.
  destruct (resolve x1 i) as [| |x']; cbn [ResolveOk] in Hres.
  - contradiction.
  - apply clos_rt_t with (state m1 f).
    + assumption.
    + now apply Relation_Operators.t_step.
  - destruct Hres as [m' [Hstep Hcore']]. apply (next_ok m m' f x').
    + assumption.
    + assumption.
    + apply clos_rt_t with (state m1 f).
      * assumption.
      * now apply Relation_Operators.t_step.
    + assumption.
Qed.

(* A step of the solver: a strict derivation to a consistent context, a final state when
   it stops, or a derivation of fail. *)
Theorem cstep_spec: forall (m: PA) (f: CNF) (x: Ctx),
  StepInv (state m f) x -> StepOk m f (cstep x).
Proof.
  intros m f x [Hcore [Hwf Hentails]]. unfold cstep.
  destruct (check_shorts (shorts x) x) as [x1 r1] eqn:Hcheck.
  destruct (check_shorts_step m f x x1 r1 Hcore Hcheck)
    as (m1 & Hder1 & Hext1 & Hcore1 & Hnone1 & Hsome1).
  destruct r1 as [i|].
  - apply (after_resolve m m1 f x1 i).
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + now apply Hsome1.
  - assert (Hwf1: WellFormed (state m1 f)).
    + now apply (derivation_well_formed DPLL_BJ m m1 f f).
    + destruct (propagate (S (nvars x1)) (x1 <| shorts := [] |>)) as [x2 r2] eqn:Hprop.
      destruct (propagate_step m1 f x1 x2 r2 Hcore1 Hwf1 (Hnone1 eq_refl) Hprop)
        as (m2 & Hder2 & Hext2 & Hcore2 & Hshorts2 & Hnonempty2 & Hnone2 & Hsome2).
      assert (Hder: state m f ==>*[DPLL_BJ] state m2 f).
      * now apply rt_trans with (state m1 f).
      * destruct r2 as [i|].
        -- apply (after_resolve m m2 f x2 i).
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ now apply Hsome2.
        -- destruct (pick (vals x2) (hr x2) (nvars x2)) as [h ol] eqn:Hpick.
           (* The heuristic changed, but not its literals to decide on *)
           pose proof (pick_dlit (vals x2) (hr x2) (nvars x2)) as Hd.
           rewrite Hpick in Hd. cbn [fst] in Hd.
           pose proof (step_core_heur m2 f x2 h Hcore2 Hd) as Hcore3.
           destruct ol as [l0|].
           (* Decide the literal the heap gives *)
           ++ destruct (pick_some Hpick) as [Hundef0 [b Hb]].
              destruct (decide_lit_spec m2 f (x2 <| hr := h |>) (cur x2) l0 Hcore3
                          (Hnone2 eq_refl) Hshorts2 Hnonempty2 (sc_cursor Hcore2)
                          (sc_dlit Hcore2 b l0 Hb) Hundef0)
                as [Hdecide Hcore4].
              apply (next_ok m ⟨m2; (phase (phs x2) l0)⟩ f).
              ** assumption.
              ** assumption.
              ** apply clos_rt_t with (state m2 f).
                 --- assumption.
                 --- now apply Relation_Operators.t_step.
              ** apply Hcore4.
           (* Otherwise decide by the cursor *)
           ++ set (x3 := x2 <| hr := h |>) in Hcore3 |- *.
              destruct (next_undef_spec f x3) as [Hc Hundef].
              ** apply Hcore3.
              ** set (c := next_undef x3) in Hc, Hundef |- *.
                 destruct (c <? nlits x3) eqn:Hlt.
                 (* Decide *)
                 --- apply Nat.ltb_lt in Hlt.
                     destruct (decide_spec m2 f x3 c Hcore3 (Hnone2 eq_refl) Hshorts2
                                 Hnonempty2 Hc Hlt (Hundef Hlt))
                       as [Hdecide Hcore4].
                     apply (next_ok m ⟨m2; (phase (phs x3) (tget (alls x3) c))⟩ f).
                     +++ assumption.
                     +++ assumption.
                     +++ apply clos_rt_t with (state m2 f).
                         *** assumption.
                         *** now apply Relation_Operators.t_step.
                     +++ apply Hcore4.
                 --- (* the trail did not grow: m2 is m, and it is final *)
                     assert (Hlen: tlen x3 = PA.length m2 /\ tlen x = PA.length m).
                     { destruct Hcore as [[[_ _ [Hlen _] _ _ _ _] _ _ _ _ _]
                                          _ _ _ _ _ _ _ _ _ _].
                       destruct Hcore3 as [[[_ _ [Hlen3 _] _ _ _ _] _ _ _ _ _]
                                           _ _ _ _ _ _ _ _ _ _].
                       rewrite <- !trail_lits_length. now split. }
                     destruct (Nat.eqb (tlen x3) (tlen x)) eqn:Hsame.
                     (* Stop *)
                     +++ apply Nat.eqb_eq in Hsame. apply Nat.ltb_ge in Hlt.
                         assert (Heq: m2 = m).
                         *** apply extends_same_length.
                             ---- now apply extends_trans with m1.
                             ---- destruct Hlen as [Hlen3 Hlen]. congruence.
                         *** subst m2. cbn [StepOk].
                             destruct (final_state m f x3 c Hcore3 (Hnone2 eq_refl)
                                         Hnonempty2 Hc) as [H1 H2].
                             ---- lia.
                             ---- now apply final_basic_of.
                     (* Only propagations *)
                     +++ apply (next_ok m m2 f).
                         *** assumption.
                         *** assumption.
                         *** apply derivation_strict.
                             ---- assumption.
                             ---- intros Heq. injection Heq as Heq.
                                  apply Nat.eqb_neq in Hsame. apply Hsame.
                                  destruct Hlen as [Hlen3 Hlen].
                                  now rewrite Hlen3, Hlen, Heq.
                         *** destruct Hcore3
                               as [Hprop3 Hcomplete3 _ Hsaved3 Hempty3 Hshort3 Hmarks3
                                   Hbound3 Hslots3 Hdlit3 Hlims3 Hlow3].
                             split.
                             ---- now apply (prop_inv_ext m2 f x3).
                             ---- assumption.
                             ---- assumption.
                             ---- assumption.
                             ---- assumption.
                             ---- assumption.
                             ---- assumption.
                             ---- assumption.
                             ---- apply (slots_grow f x3).
                                  ++++ assumption.
                                  ++++ reflexivity.
                                  ++++ reflexivity.
                                  ++++ reflexivity.
                                  ++++ simpl. lia.
                             ---- assumption.
                             ---- assumption.
                             ---- assumption.
Qed.

(* The step of the solver on states: the state after a step is the trail of the next
   context. *)
Definition step (p: State * Ctx): option (State * Ctx) :=
match p with
| (fail, _)      => None
| (state _ f, x) =>
  match cstep x with
  | CStop    => None
  | CFail    => Some (fail, x)
  | CNext x' => Some (state (trail x') f, x')
  end
end.

(* The solver step is a strategy for DPLL_BJ. *)
Theorem step_strategy: Strategy DPLL_BJ StepInv step.
Proof.
  split.
  - reflexivity.
  - split.
    + intros [|m f] x Hinv Hstep.
      * intros [s' Htrans]. inversion Htrans.
      * pose proof (cstep_spec m f x Hinv) as Hok. cbn [step] in Hstep.
        destruct (cstep x) as [| |x'].
        -- assumption.
        -- discriminate.
        -- discriminate.
    + intros [|m f] s' x x' Hinv Hstep.
      * discriminate.
      * pose proof (cstep_spec m f x Hinv) as Hok. cbn [step] in Hstep.
        destruct (cstep x) as [| |x1].
        -- discriminate.
        -- injection Hstep as <- <-. split.
           ++ assumption.
           ++ reflexivity.
        -- injection Hstep as <- <-. assumption.
Qed.

(* The analysis and unmarking the lower literals change only the marks, the lower
   literals and the heuristic. *)
Lemma resolve_analysed: forall (x x1 x2: Ctx) (hd: Heur) (i d lo mx: nat)
  (ou: option Lit),
  analyze (x <| hr := hd |>) i d lo = (x1, ou) -> unmark_lower x1 = (x2, mx) ->
  x2 = x <| mrk := mrk x2 |> <| lower := lower x2 |> <| hr := hr x2 |>.
Proof.
  intros x x1 x2 hd i d lo mx ou Han Hul.
  apply analyze_analysed in Han. destruct Han as [Hx1 _].
  unfold unmark_lower in Hul. apply unmark_lits_spec in Hul. destruct Hul as [Hx2 _].
  assert (Hlower: lower x2 = lower x1) by (rewrite Hx2; reflexivity).
  assert (Hhr: hr x2 = hr x1) by (rewrite Hx2; reflexivity).
  rewrite Hlower, Hhr. rewrite Hx2 at 1. rewrite Hx1 at 1.
  destruct x. reflexivity.
Qed.
