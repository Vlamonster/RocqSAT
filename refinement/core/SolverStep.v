From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
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
From RocqSAT.refinement Require Import Tactics.
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

(* The last decision l of the trail is at position PA.length m', after the positions
   of the decisions of m', on level S (decisions m'). *)
Lemma last_decision: forall (m' n: PA) (f: CNF) (x: Ctx) (l: Lit),
  StepCore ⟨m'; l ++ n⟩ f x -> NoDecisions n ->
  (exists (lims': list nat), lims x = PA.length m' :: lims' /\ LimsOf lims' m') /\
  dl x = S (decisions m').
Proof.
  intros m' n f x l [[[_ _ _ _ _ Hdl _] _ _ _ _ _] _ _ _ _ _ _ _ _ _ Hlims _] Hno_dec.
  split.
  - destruct (lims_split (lims x) m' n l Hlims) as (lims' & Hskip_l & Hlims' & _).
    rewrite no_decisions_zero in Hskip_l by assumption. simpl in Hskip_l.
    now exists lims'.
  - rewrite Hdl, decisions_app, (no_decisions_zero n Hno_dec). simpl. lia.
Qed.

(* Flipping the last decision l, at position PA.length m' of the trail, after an analysis
   of x that left the context xa: a Backjump step, to a consistent context. *)
Lemma flip_spec: forall (m' n: PA) (f: CNF) (x xa: Ctx) (l: Lit) (c: Clause),
  StepInv (state ⟨m'; l ++ n⟩ f) x -> NoDecisions n -> Analysed x xa ->
  Unmarked (mrk xa) -> c ∈ f -> c_eval ⟨m'; l ++ n⟩ c = Some false ->
  exists (x': Ctx), flip xa (PA.length m') = CNext x' /\
    state ⟨m'; l ++ n⟩ f ==>[DPLL_BJ] state ⟨m', (¬l)⟩ f /\ StepCore ⟨m', (¬l)⟩ f x'.
Proof.
  intros m' n f x xa l c [Hcore [Hwf Hentails]] Hno_dec Hxa Hmk Hc_in_f Hc_false.
  pose proof Hcore as [[[_ Hfresh Htrail _ _ _ _] _ _ _ _ _] _ _ Hsaved].
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
      destruct (last_decision m' n f x l Hcore Hno_dec)
        as [(lims' & Hlims_eq & Hlims') Hdl'].
      rewrite Htr, Htl, Hdla, Hla, Hdl', Nat.sub_1_r, Nat.pred_succ, back_lower.
      apply (jump_core m' n f x xa l (¬l) c1 st1 (tl (lims x))).
      * assumption.
      * assumption.
      * assumption.
      * now apply l_eval_neg_none_iff in Hl.
      * assumption.
      * assumption.
      * (* the positions of the decisions before l *)
        now rewrite Hlims_eq.
      * left. split; reflexivity.
Qed.

(* Flipping the last decision resolves the conflict. *)
Lemma flip_ok: forall (m' n: PA) (f: CNF) (x xa: Ctx) (l: Lit) (c: Clause),
  StepInv (state ⟨m'; l ++ n⟩ f) x -> NoDecisions n -> Analysed x xa ->
  Unmarked (mrk xa) -> c ∈ f -> c_eval ⟨m'; l ++ n⟩ c = Some false ->
  ResolveOk ⟨m'; l ++ n⟩ f (flip xa (PA.length m')).
Proof.
  intros m' n f x xa l c Hinv Hno_dec Hxa Hmk Hc_in_f Hc_false.
  destruct (flip_spec m' n f x xa l c Hinv Hno_dec Hxa Hmk Hc_in_f Hc_false)
    as (x' & Hflip & Hstep & Hcore').
  rewrite Hflip. now exists ⟨m', (¬l)⟩.
Qed.

(* The analysis from the decayed heuristic, then unmarking the lower literals: the
   context changes only as an analysis does, only the literal to assert stays marked,
   the lower literals are false and of level at most mx, and with the literal u to
   assert, they form an entailed clause and u is the negation of a literal of the last
   level. *)
Lemma analyze_unmark_spec: forall (m' n: PA) (f: CNF) (x x1 x2: Ctx) (l: Lit)
  (i mx: nat) (ou: option Lit),
  StepCore ⟨m'; l ++ n⟩ f x -> NoDecisions n -> ClauseFalse x i ->
  analyze (x <| hr := decay (hr x) (nvars x) |>) i (S (decisions m')) (PA.length m')
    = (x1, ou) ->
  unmark_lower x1 = (x2, mx) ->
  Analysed x x2 /\ Unmarked (unmark_opt (mrk x2) ou) /\
  (forall (y: Lit), In y (lower x2) ->
     l_eval ⟨m'; l ++ n⟩ y = Some false /\ level x y <= mx) /\
  (forall (u: Lit), ou = Some u ->
     Entailed f (lower x2 ++ [u]) /\ OnLevel x m' (tlen x) u).
Proof.
  intros m' n f x x1 x2 l i mx ou Hcore Hno_dec Hconflict Han Hun.
  pose proof Hcore as [[Hcore0 _ _ _ _ _] _ _ _ _ _ Hmarks _ [Hslots _ _] _ _ Hlow].
  destruct (analyze_spec f x m' n l Hcore0 Hno_dec Hslots (decay (hr x) (nvars x)) i
              x1 ou Hconflict Hmarks Hlow Han)
    as (Hmarked & Hlower & Hassert).
  assert (Hx1: Analysed x x1).
  { apply analysed_trans with (x <| hr := decay (hr x) (nvars x) |>).
    - split.
      + reflexivity.
      + apply decay_dlit.
    - now apply analyze_analysed in Han. }
  destruct (unmark_lower_analysed x1 x2 mx Hun) as [Hx12 Hlow2].
  (* the analysis keeps the levels *)
  pose proof Hx1 as [Hx1_eq _].
  assert (Hlv1: lvl x1 = lvl x) by (rewrite Hx1_eq; reflexivity).
  splits.
  - now apply analysed_trans with x1.
  - now apply (unmark_lower_unmarked x1 x2 ou mx).
  - intros y Hy. rewrite Hlow2 in Hy. split.
    + now apply Hlower.
    + rewrite <- Hlv1. now apply (unmark_lower_levels x1 x2 mx).
  - intros u Hu. rewrite Hlow2. now apply Hassert.
Qed.

(* The literal u the analysis asserts, the negation of a literal of the last level, is
   false in the trail and undefined before the decision d of an earlier level. *)
Lemma asserted_undef: forall (m' n mt n': PA) (f: CNF) (x: Ctx) (l d u: Lit),
  Core ⟨m'; l ++ n⟩ f x -> NoDecisions n -> OnLevel x m' (tlen x) u ->
  ⟨m'; l ++ n⟩ = ⟨mt; d ++ n'⟩ -> decisions mt < S (decisions m') ->
  l_eval ⟨mt; d ++ n'⟩ u = Some false /\ l_eval mt u = None.
Proof.
  intros m' n mt n' f x l d u Hcore0 Hno_dec (q & Hq & Hu_eq) Hsplit Hlt.
  assert (Hu_false: l_eval ⟨m'; l ++ n⟩ u = Some false).
  { rewrite Hu_eq. apply (trail_neg_false _ f x).
    - assumption.
    - lia. }
  assert (Hu_lv: level x u = S (decisions m')).
  { rewrite Hu_eq, extract_neg. apply (seg_level f x m' n l Hcore0 Hno_dec). lia. }
  rewrite Hsplit in Hcore0, Hu_false.
  pose proof Hcore0 as [_ Hfresh _ _ _ _ Htrace]. split.
  - assumption.
  - apply (undef_before mt n' d u Hfresh Htrace).
    + assumption.
    + lia.
Qed.

(* The lower literals, false in the trail and of level at most that of mt, are false
   in mt. *)
Lemma lower_false: forall (mt n: PA) (f: CNF) (x: Ctx) (d: Lit) (lt: list Lit),
  Core ⟨mt; d ++ n⟩ f x ->
  (forall (y: Lit), In y lt ->
     l_eval ⟨mt; d ++ n⟩ y = Some false /\ level x y <= decisions mt) ->
  forall (y: Lit), In y lt -> l_eval mt y = Some false.
Proof.
  intros mt n f x d lt [_ Hfresh _ _ _ _ Htrace] Hlower y Hy.
  destruct (Hlower y Hy) as [Hy_false Hy_le].
  apply (false_before mt n d y Hfresh Htrace).
  - assumption.
  - assumption.
Qed.

(* Removing u from the clause of the literals lt and u leaves a clause false in m when
   the literals lt are. *)
Lemma clause_of_remove_false: forall (m: PA) (lt: list Lit) (u: Lit),
  (forall (y: Lit), In y lt -> l_eval m y = Some false) ->
  c_eval m (Clause.remove u (clause_of (lt ++ [u]))) = Some false.
Proof.
  intros m lt u Hlt_false. apply c_eval_false_iff. intros y Hy.
  apply Clause.remove_spec in Hy as [Hy Hne].
  apply clause_of_spec, in_app_iff in Hy as [Hy | [Hy | []]].
  - now apply Hlt_false.
  - now symmetry in Hy.
Qed.

(* Backjumping from the conflict on the false clause c to the level of mt, asserting u
   with the lower literals of the analysis that left xa: they are false in mt, u is
   undefined there, and together they form an entailed clause. A Backjump step, to a
   consistent context. *)
Lemma backjump_spec: forall (mt n: PA) (f: CNF) (x xa x': Ctx) (d u: Lit) (c: Clause)
  (c0: nat) (st ls: list nat) (r: Reason),
  StepInv (state ⟨mt; d ++ n⟩ f) x -> Analysed x xa -> Unmarked (mrk xa) ->
  c ∈ f -> c_eval ⟨mt; d ++ n⟩ c = Some false ->
  Entailed f (lower xa ++ [u]) ->
  (forall (y: Lit), In y (lower xa) -> l_eval mt y = Some false) ->
  l_eval ⟨mt; d ++ n⟩ u = Some false -> l_eval mt u = None ->
  skipn (decisions n) (saved x) = c0 :: st -> LimsOf ls mt ->
  push_reason (back xa (PA.length mt) c0 st (decisions mt) ls) u = (x', r) ->
  ResolveOk ⟨mt; d ++ n⟩ f (CNext (assign (x' <| lower := [] |>) u r)).
Proof.
  intros mt n f x xa x' d u c c0 st ls r [Hcore [Hwf Hentails]] Hxa Hmk Hc_in_f
    Hc_false Hent_u Hlt_false Hu_false Hu_undef Hskip Hlims Hpush.
  cbn [ResolveOk]. exists ⟨mt, u⟩. split.
  - (* the Backjump step, with the clause of the lower literals and u *)
    apply (t_step Backjump).
    + right. right. right. now left.
    + apply (r_backjump mt n f c (clause_of (lower xa ++ [u])) d u).
      * assumption.
      * assumption.
      * now apply entailed_consequence.
      * apply clause_of_spec, in_or_app. right. now left.
      * now apply clause_of_remove_false.
      * assumption.
      * destruct Hwf as [_ Hbounded]. apply l_eval_false_in, Hbounded in Hu_false.
        rewrite Neg.involutive in Hu_false. now apply or_comm.
  - (* the context after going back, with the analysed clause as reason of u *)
    destruct (saved_c_split f (alls x) (nlits x) mt n d (saved x) (sc_saved Hcore))
      as (c1 & st1 & Hskip1 & Hc1 & Hst1).
    rewrite Hskip in Hskip1. injection Hskip1 as <- <-.
    apply (jump_core mt n f x xa d u c0 st ls x' r).
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + right. splits.
      * assumption.
      * apply (entailed_incl f (lower xa ++ [u])).
        -- assumption.
        -- intros y Hy. apply in_app_iff in Hy as [Hy | [<- | []]].
           ++ right. apply Hy.
           ++ now left.
      * apply Hlt_false.
Qed.

(* Splitting the trail ⟨m'; l ++ n⟩ with S (decisions m') - S mx decisions after the
   split leaves mx decisions before it. *)
Lemma split_levels_below: forall (m' n mt n': PA) (l d: Lit) (mx: nat),
  NoDecisions n -> mx < S (decisions m') ->
  split_levels (S (decisions m') - S mx) ⟨m'; l ++ n⟩ = Some (mt, d, n') ->
  ⟨m'; l ++ n⟩ = ⟨mt; d ++ n'⟩ /\ decisions mt = mx.
Proof.
  intros m' n mt n' l d mx Hno_dec Hmx Hsplit.
  pose proof (split_levels_decisions Hsplit) as Hdec_n.
  apply split_levels_spec in Hsplit. split.
  - assumption.
  - pose proof (f_equal decisions Hsplit) as Hdec.
    rewrite !decisions_app, (no_decisions_zero n Hno_dec) in Hdec.
    simpl in Hdec. lia.
Qed.

(* Changing the marks after an analysis is still an analysis. *)
Lemma analysed_set_mrk: forall (x xa: Ctx) (mk: Table bool),
  Analysed x xa -> Analysed x (xa <| mrk := mk |>).
Proof.
  intros x xa mk Hxa. apply analysed_trans with xa.
  - assumption.
  - split; reflexivity.
Qed.

(* Resolving a conflict on clause i, the false clause c of f, after the last decision l:
   analyse the conflict (analyze_unmark_spec), then backjump to the level the analysis
   gives (backjump_spec); in every case without a jump (no literal to assert, no lower
   level, no decision position or saved cursor for it), flip l (flip_ok). *)
Lemma resolve_decided: forall (m' n: PA) (f: CNF) (x: Ctx) (l: Lit) (c: Clause)
  (i: nat),
  StepInv (state ⟨m'; l ++ n⟩ f) x -> NoDecisions n -> ClauseFalse x i ->
  c ∈ f -> c_eval ⟨m'; l ++ n⟩ c = Some false ->
  ResolveOk ⟨m'; l ++ n⟩ f (resolve x i).
Proof.
  intros m' n f x l c i Hinv Hno_dec Hconflict Hc_in_f Hc_false.
  pose proof Hinv as [Hcore _].
  pose proof Hcore as [[Hcore0 _ _ _ _ _] _ _ _ _ _ _ _ _ _ Hlims _].
  destruct (last_decision m' n f x l Hcore Hno_dec) as [(lims' & Hlims_eq & _) Hd].
  unfold resolve. rewrite Hlims_eq in Hlims |- *. rewrite Hd.
  (* the analysis, then unmarking the lower literals *)
  destruct (analyze (x <| hr := decay (hr x) (nvars x) |>) i (S (decisions m'))
              (PA.length m')) as [x1 ou] eqn:Han.
  destruct (unmark_lower x1) as [x2 mx] eqn:Hun.
  destruct (analyze_unmark_spec m' n f x x1 x2 l i mx ou Hcore Hno_dec Hconflict Han Hun)
    as (Hx2 & Hmk2 & Hlower & Hassert).
  destruct ou as [u|].
  - (* a literal u to assert: unmark it *)
    cbv zeta. set (x3 := x2 <| mrk := tset (mrk x2) (lit_key u) false |>).
    assert (Hx3: Analysed x x3) by now apply analysed_set_mrk.
    destruct (mx <? S (decisions m')) eqn:Hmx.
    + (* a level mx to go back to, at the decision d of the split ⟨mt; d ++ n'⟩ *)
      apply Nat.ltb_lt in Hmx.
      destruct (split_levels (S (decisions m') - S mx) ⟨m'; l ++ n⟩)
        as [[[mt d] n']|] eqn:Hsplit.
      * destruct (split_levels_lims Hlims Hsplit) as [Hnth Hlims_mt].
        rewrite Hnth.
        set (ls := skipn (S (S (decisions m') - S mx)) (PA.length m' :: lims'))
          in Hlims_mt |- *.
        destruct (skipn (S (decisions m') - S mx) (saved x)) as [|c0 st] eqn:Hskip.
        -- apply (flip_ok m' n f x x3 l c); assumption.
        -- (* Backjump to mt, with mx = decisions mt *)
           pose proof (split_levels_decisions Hsplit) as Hdec_n.
           destruct (split_levels_below m' n mt n' l d mx Hno_dec Hmx Hsplit)
             as [Hm_eq Hdec_mt].
           destruct (Hassert u eq_refl) as [Hent_u Hon].
           assert (Hmt_lt: decisions mt < S (decisions m')) by lia.
           destruct (asserted_undef m' n mt n' f x l d u Hcore0 Hno_dec Hon Hm_eq
                       Hmt_lt)
             as [Hu_false Hu_undef].
           rewrite <- Hdec_mt in Hlower.
           rewrite Hm_eq in Hcore0, Hlower, Hinv, Hc_false |- *.
           destruct (push_reason (back x3 (PA.length mt) c0 st mx ls) u)
             as [x4 r] eqn:Hpush.
           apply (backjump_spec mt n' f x x3 x4 d u c c0 st ls r).
           ++ assumption.
           ++ assumption.
           ++ apply Hmk2.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ now apply (lower_false mt n' f x d).
           ++ assumption.
           ++ assumption.
           ++ now rewrite Hdec_n.
           ++ assumption.
           ++ now rewrite Hdec_mt.
      * rewrite (split_levels_lims_none Hlims Hsplit).
        apply (flip_ok m' n f x x3 l c); assumption.
    + apply (flip_ok m' n f x x3 l c); assumption.
  - (* no literal to assert *)
    apply (flip_ok m' n f x x2 l c); assumption.
Qed.

(* Resolving a conflict on a false clause c: without decisions a Fail step, and
   otherwise a Backjump step after the last decision (resolve_decided), to a consistent
   context. *)
Lemma resolve_spec: forall (m: PA) (f: CNF) (x: Ctx) (i: nat),
  StepInv (state m f) x -> ClauseFalse x i -> ResolveOk m f (resolve x i).
Proof.
  intros m f x i Hinv Hconflict. pose proof Hinv as [Hcore _].
  pose proof Hconflict as [ls [Hi Hfalse]].
  pose proof (pi_core (sc_prop Hcore)) as [Hvals _ _ Hsound _ _ _].
  (* the conflict clause is a clause c of f, false in m *)
  apply Hsound in Hi as [c [Hc_in_f Hiff]].
  assert (Hc_false: c_eval m c = Some false).
  { apply c_eval_false_iff. intros l Hl. rewrite <- Hvals. apply Hfalse.
    now apply Hiff. }
  destruct (split_last_decision m) as [[m' l]|] eqn:Hsplit.
  - (* the last decision l *)
    apply PA.split_last_decision_some_iff in Hsplit as [n [-> Hno_dec]].
    now apply (resolve_decided m' n f x l c i).
  - (* Fail: without decisions there are no positions of decisions *)
    apply PA.split_last_decision_none_iff in Hsplit.
    unfold resolve. rewrite (lims_none (lims x) m (sc_lims Hcore) Hsplit).
    cbn [ResolveOk]. apply (t_step Fail).
    + now left.
    + now apply (r_fail m f c).
Qed.

(* A derivation to m1 followed by a step to a state consistent with x' is a step to
   x'. *)
Lemma next_after: forall (m m1 m': PA) (f: CNF) (x': Ctx),
  WellFormed (state m f) -> Entails f m -> state m f ==>*[DPLL_BJ] state m1 f ->
  state m1 f ==>[DPLL_BJ] state m' f -> StepCore m' f x' -> StepOk m f (CNext x').
Proof.
  intros m m1 m' f x' Hwf Hentails Hder Hstep Hcore'. apply (next_ok m m').
  - assumption.
  - assumption.
  - apply clos_rt_t with (state m1 f).
    + assumption.
    + now apply Relation_Operators.t_step.
  - assumption.
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
  - destruct Hres as [m' [Hstep Hcore']]. now apply (next_after m m1 m' f x').
Qed.

(* The trail table holds as many literals as the trail. *)
Lemma step_core_tlen: forall (m: PA) (f: CNF) (x: Ctx),
  StepCore m f x -> tlen x = PA.length m.
Proof.
  intros m f x [[[_ _ [Hlen _] _ _ _ _] _ _ _ _ _] _ _ _ _ _ _ _ _ _ _ _].
  now rewrite <- trail_lits_length.
Qed.

(* Moving the cursor to a position that is a cursor too keeps the invariant. *)
Lemma step_core_cursor: forall (m: PA) (f: CNF) (x: Ctx) (c: nat),
  StepCore m f x -> CursorAt f x c -> StepCore m f (x <| cur := c |>).
Proof.
  intros m f x c [Hprop Hcomplete _ Hsaved Hempty Hshort Hmarks Hbound Hslots Hdlit
    Hlims Hlow] Hc.
  split.
  - now apply (prop_inv_ext m f x).
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - apply (slots_grow f x).
    + assumption.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + simpl. lia.
  - assumption.
  - assumption.
  - assumption.
Qed.

(* When the cursor finds nothing to decide and the trail did not grow since m, the
   state m is final. *)
Lemma stop_final: forall (m m2: PA) (f: CNF) (x x2: Ctx) (c: nat),
  StepCore m f x -> Extends m m2 -> StepCore m2 f x2 -> qhead x2 = tlen x2 ->
  (forall (i: nat), tget (cmap x2) i <> Some []) -> CursorAt f x2 c ->
  nlits x2 <= c -> tlen x2 = tlen x -> StepOk m f CStop.
Proof.
  intros m m2 f x x2 c Hcore Hext Hcore2 Hq Hnonempty Hc Hend Hsame.
  (* the trail did not grow, so m2 is m *)
  assert (Heq: m2 = m).
  { apply extends_same_length.
    - assumption.
    - rewrite <- (step_core_tlen m2 f x2 Hcore2), <- (step_core_tlen m f x Hcore).
      assumption. }
  subst m2. cbn [StepOk].
  destruct (final_state m f x2 c Hcore2 Hq Hnonempty Hc) as [Hno_false Hall].
  - lia.
  - now apply final_basic_of.
Qed.

(* When the trail grew by propagations only, moving the cursor to c is a step. *)
Lemma propagated_ok: forall (m m2: PA) (f: CNF) (x x2: Ctx) (c: nat),
  WellFormed (state m f) -> Entails f m -> StepCore m f x ->
  state m f ==>*[DPLL_BJ] state m2 f -> StepCore m2 f x2 -> CursorAt f x2 c ->
  tlen x2 <> tlen x -> StepOk m f (CNext (x2 <| cur := c |>)).
Proof.
  intros m m2 f x x2 c Hwf Hentails Hcore Hder Hcore2 Hc Hgrew.
  apply (next_ok m m2 f).
  - assumption.
  - assumption.
  - apply derivation_strict.
    + assumption.
    + intros Heq. injection Heq as Heq. apply Hgrew.
      rewrite (step_core_tlen m2 f x2 Hcore2), (step_core_tlen m f x Hcore).
      now rewrite Heq.
  - now apply step_core_cursor.
Qed.

(* A step of the solver: a strict derivation to a consistent context, a final state when
   it stops, or a derivation of fail. The step runs three phases, each a derivation:
   check the short clauses, propagate, and decide; a conflict in either of the first two
   is resolved (after_resolve); the decision is on the literal pick gives, or at the
   cursor, and without one the solver stops (stop_final) or goes on with the
   propagations alone (propagated_ok). *)
Theorem cstep_spec: forall (m: PA) (f: CNF) (x: Ctx),
  StepInv (state m f) x -> StepOk m f (cstep x).
Proof.
  intros m f x [Hcore [Hwf Hentails]]. unfold cstep.
  (* 1. Check the short clauses *)
  destruct (check_shorts (shorts x) x) as [x1 r1] eqn:Hcheck.
  destruct (check_shorts_step m f x x1 r1 Hcore Hcheck)
    as (m1 & Hder1 & Hext1 & Hcore1 & Hnone1 & Hsome1).
  assert (Hwf1: WellFormed (state m1 f)).
  { now apply (derivation_well_formed DPLL_BJ m m1 f f). }
  destruct r1 as [i|].
  - (* a short clause is false *)
    apply (after_resolve m m1 f x1 i Hwf Hentails Hder1 Hcore1). now apply Hsome1.
  - (* 2. Propagate *)
    destruct (propagate (S (nvars x1)) (x1 <| shorts := [] |>)) as [x2 r2] eqn:Hprop.
    destruct (propagate_step m1 f x1 x2 r2 Hcore1 Hwf1 (Hnone1 eq_refl) Hprop)
      as (m2 & Hder2 & Hext2 & Hcore2 & Hshorts2 & Hnonempty2 & Hnone2 & Hsome2).
    assert (Hder: state m f ==>*[DPLL_BJ] state m2 f).
    { now apply rt_trans with (state m1 f). }
    assert (Hext: Extends m m2) by now apply extends_trans with m1.
    destruct r2 as [i|].
    + (* a conflict *)
      apply (after_resolve m m2 f x2 i Hwf Hentails Hder Hcore2). now apply Hsome2.
    + (* 3. Decide; the heuristic changed, but not its literals to decide on *)
      destruct (pick (vals x2) (hr x2) (nvars x2)) as [h ol] eqn:Hpick.
      pose proof (pick_dlit (vals x2) (hr x2) (nvars x2)) as Hd.
      rewrite Hpick in Hd. cbn [fst] in Hd.
      pose proof (step_core_heur m2 f x2 h Hcore2 Hd) as Hcore3.
      destruct ol as [l0|].
      * (* on the literal the heap gives *)
        destruct (pick_some Hpick) as [Hundef0 [b Hb]].
        destruct (decide_lit_spec m2 f (x2 <| hr := h |>) (cur x2) l0 Hcore3
                    (Hnone2 eq_refl) Hshorts2 Hnonempty2 (sc_cursor Hcore2)
                    (sc_dlit Hcore2 b l0 Hb) Hundef0)
          as [Hdecide Hcore4].
        now apply (next_after m m2 ⟨m2; (phase (phs x2) l0)⟩ f).
      * (* otherwise at the cursor *)
        set (x3 := x2 <| hr := h |>) in Hcore3 |- *.
        destruct (next_undef_spec f x3 (sc_cursor Hcore3)) as [Hc Hundef].
        set (c := next_undef x3) in Hc, Hundef |- *.
        destruct (c <? nlits x3) eqn:Hlt.
        -- apply Nat.ltb_lt in Hlt.
           destruct (decide_spec m2 f x3 c Hcore3 (Hnone2 eq_refl) Hshorts2
                       Hnonempty2 Hc Hlt (Hundef Hlt))
             as [Hdecide Hcore4].
           now apply (next_after m m2 ⟨m2; (phase (phs x3) (tget (alls x3) c))⟩ f).
        -- (* nothing left to decide *)
           apply Nat.ltb_ge in Hlt.
           destruct (Nat.eqb (tlen x3) (tlen x)) eqn:Hsame.
           ++ (* Stop: the trail did not grow *)
              apply Nat.eqb_eq in Hsame.
              now apply (stop_final m m2 f x x3 c Hcore Hext Hcore3 (Hnone2 eq_refl)
                           Hnonempty2 Hc Hlt).
           ++ (* only propagations *)
              apply Nat.eqb_neq in Hsame.
              now apply (propagated_ok m m2 f x x3 c).
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
