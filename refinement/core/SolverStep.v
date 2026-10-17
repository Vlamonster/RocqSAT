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
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement Require Import Analysis.
From RocqSAT.refinement Require Import Step.
From RocqSAT.refinement Require Import CStep.

(* The solver, whose step the C solver computes: check the short clauses, propagate with
   two watched literals (Propagate.v) and decide at the cursor (Step.v); on a conflict,
   fail without decisions, and otherwise analyse it (Analysis.v) and backjump, asserting
   the literal the analysis gives, with the analysed clause as its reason if there is
   room; when the analysis gives no literal, flip the last decision. step_strategy; cstep
   computes the same step from the context alone (CStep.v), cstep_spec. *)

Section Backjump.
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

  (* The literals from the decision d of ⟨mt; d ++ n⟩ on have a level above the
     decisions of mt. *)
  Lemma trace_seg_ge: forall (cm: ClauseMap) (rsn: Table Reason) (lv: Table nat)
    (rcl: Table (list Lit)) (rps: Table nat) (nr: nat) (mt n: PA) (d z: Lit),
    TraceOk cm rsn lv rcl rps nr ⟨mt; d ++ n⟩ -> z = d \/ z ∈ n ->
    S (decisions mt) <= tget lv (extract z).
  Proof.
    intros cm rsn lv rcl rps nr mt n d z.
    induction n as [|n IH t|n IH t]; cbn [PA.app TraceOk]; intros Htrace Hz.
    - destruct Htrace as (Hlv & _). destruct Hz as [-> | []]. lia.
    - destruct Htrace as (Hlv & _ & Htrace). destruct Hz as [-> | [<- | Hz]].
      + apply IH.
        * assumption.
        * now left.
      + rewrite Hlv, decisions_app. simpl. lia.
      + apply IH.
        * assumption.
        * now right.
    - destruct Htrace as (Hlv & Htrace). destruct Hz as [-> | [<- | Hz]].
      + apply IH.
        * assumption.
        * now left.
      + rewrite Hlv, decisions_app. simpl. lia.
      + apply IH.
        * assumption.
        * now right.
  Qed.

  (* A false literal of a level up to the decisions of mt is false in mt already. *)
  Lemma false_before: forall (cm: ClauseMap) (rsn: Table Reason) (lv: Table nat)
    (rcl: Table (list Lit)) (rps: Table nat) (nr: nat) (mt n: PA) (d y: Lit),
    Fresh ⟨mt; d ++ n⟩ -> TraceOk cm rsn lv rcl rps nr ⟨mt; d ++ n⟩ ->
    l_eval ⟨mt; d ++ n⟩ y = Some false -> tget lv (extract y) <= decisions mt ->
    l_eval mt y = Some false.
  Proof.
    intros cm rsn lv rcl rps nr mt n d y Hfresh Htrace Hy Hlv.
    apply l_eval_false_in in Hy. apply PA.in_app_iff in Hy as [Hin | [Heq | Hin]].
    - exfalso.
      pose proof (trace_seg_ge cm rsn lv rcl rps nr mt n d (¬y) Htrace (or_intror Hin)).
      rewrite extract_neg in *. lia.
    - exfalso. assert (Hd: ¬y = d \/ ¬y ∈ n) by (left; now symmetry).
      pose proof (trace_seg_ge cm rsn lv rcl rps nr mt n d (¬y) Htrace Hd).
      rewrite extract_neg in *. lia.
    - rewrite <- (Neg.involutive y), l_eval_neg, fresh_in_true.
      + reflexivity.
      + apply (fresh_split mt n d Hfresh).
      + assumption.
  Qed.

  (* A false literal of a level above the decisions of mt is unassigned in mt. *)
  Lemma undef_before: forall (cm: ClauseMap) (rsn: Table Reason) (lv: Table nat)
    (rcl: Table (list Lit)) (rps: Table nat) (nr: nat) (mt n: PA) (d u: Lit),
    Fresh ⟨mt; d ++ n⟩ -> TraceOk cm rsn lv rcl rps nr ⟨mt; d ++ n⟩ ->
    l_eval ⟨mt; d ++ n⟩ u = Some false -> decisions mt < tget lv (extract u) ->
    l_eval mt u = None.
  Proof.
    intros cm rsn lv rcl rps nr mt n d u Hfresh Htrace Hu Hlv.
    destruct (l_eval mt u) as [[|]|] eqn:Hmt.
    - exfalso. apply l_eval_true_in in Hmt.
      assert (Hin: u ∈ ⟨mt; d ++ n⟩) by (apply PA.in_app_iff; right; now right).
      rewrite fresh_in_true in Hu by assumption. discriminate.
    - exfalso. apply l_eval_false_in in Hmt.
      pose proof (trace_app _ _ _ _ _ _ ⟨mt; d⟩ n Htrace) as [_ Htrace_mt].
      pose proof (trace_le _ _ _ _ _ _ mt (¬u) Htrace_mt Hmt).
      rewrite extract_neg in *. lia.
    - reflexivity.
  Qed.

  (* The negation of a trail literal is false. *)
  Lemma trail_neg_false: forall (m: PA) (f: CNF) (x: Ctx) (q: nat),
    Core m f x -> q < tlen x -> l_eval m (¬tget (tr x) q) = Some false.
  Proof.
    intros m f x q Hcore Hq. rewrite l_eval_neg, fresh_in_true.
    - reflexivity.
    - apply Hcore.
    - apply (trail_of_in (tr x) (tlen x)).
      + apply Hcore.
      + assumption.
  Qed.
End Backjump.

(* The marks after the analysis gave ou with the marks mk and the lower literals lt:
   unmark lt, and the literal to assert. *)
Definition clear_marks (lv: Table nat) (mk: Table bool) (lt: list Lit) (ou: option Lit):
  Table bool * nat :=
match unmark_lower lv mk 0 lt with
| (mk1, mx) =>
  match ou with
  | Some u => (tset mk1 (lit_key u) false, mx)
  | None   => (mk1, mx)
  end
end.

(* Flip the last decision l of m = ⟨m'; l ++ n⟩, with the marks mk. *)
Definition flip (m' m: PA) (f: CNF) (x: Ctx) (l: Lit) (mk: Table bool):
  option (State * Ctx) :=
match saved x with
| c0 :: st =>
  Some (state ⟨m', (¬l)⟩ f,
        assign (jump x (unassign_level (vals x) m) (PA.length m') c0 st (dl x - 1) mk)
          (¬l) no_reason)
| []       => None
end.

(* Resolve a conflict on the false clause i: fail without decisions; otherwise analyse
   it, and if it gives a literal u to assert, jump back to before the decision of the
   level after the highest level mx of the other literals of the analysed clause, and
   assert u with that clause as its reason; otherwise flip the last decision. *)
Definition resolve (m: PA) (f: CNF) (x: Ctx) (i: nat): option (State * Ctx) :=
match split_last_decision m with
| None         => Some (fail, x)
| Some (m', l) =>
  match analyze x i (dl x) (PA.length m') with
  | (ou, mk, lt) =>
    match clear_marks (lvl x) mk lt ou with
    | (mk2, mx) =>
      match ou with
      | Some u =>
        if mx <? dl x then
          match split_levels (dl x - S mx) m with
          | Some (mt, d, n) =>
            match skipn (dl x - S mx) (saved x) with
            | c0 :: st =>
              match push_reason
                      (jump x (unassign_segment (vals x) d n) (PA.length mt) c0 st mx
                         mk2) u lt with
              | (x1, r) => Some (state ⟨mt, u⟩ f, assign x1 u r)
              end
            | []       => flip m' m f x l mk2
            end
          | None            => flip m' m f x l mk2
          end
        else flip m' m f x l mk2
      | None   => flip m' m f x l mk2
      end
    end
  end
end.

(* One step: check the short clauses and propagate; on a conflict resolve, and otherwise decide. *)
Definition step (p: State * Ctx): option (State * Ctx) :=
match p with
| (fail, _)      => None
| (state m f, x) =>
  match check_shorts (shorts x) m x with
  | (m1, x1, Some i) => resolve m1 f x1 i
  | (m1, x1, None)   =>
    match propagate (S (nvars x1)) m1 (clear_shorts x1) with
    | (m2, x2, Some i) => resolve m2 f x2 i
    | (m2, x2, None)   =>
      let c := skip_from (vals x2) (alls x2) (nlits x2) (nlits x2 - cur x2) (cur x2) in
      if c <? nlits x2 then
        let l := phase (phs x2) (tget (alls x2) c) in
        Some (state ⟨m2; l⟩ f, assign (open_level x2 c) l no_reason)
      else if Nat.eqb (tlen x2) (tlen x) then None else Some (state m2 f, with_cursor x2 c)
    end
  end
end.

(* After the analysis no literal is marked. *)
Lemma clear_marks_unmarked: forall (lv: Table nat) (mk mk2: Table bool) (lt: list Lit)
  (ou: option Lit) (mx: nat),
  (forall (y: Lit), tget mk (lit_key y) = true -> In y lt \/ ou = Some y) ->
  clear_marks lv mk lt ou = (mk2, mx) ->
  Unmarked mk2 /\ forall (y: Lit), In y lt -> tget lv (extract y) <= mx.
Proof.
  intros lv mk mk2 lt ou mx Hmarked Hclear. unfold clear_marks in Hclear.
  destruct (unmark_lower lv mk 0 lt) as [mk1 mx1] eqn:Hun.
  destruct (unmark_lower_spec lv lt mk mk1 0 mx1 Hun)
    as (Hcleared & Hother & Hle & _ & _).
  assert (Hmk1: forall (y: Lit), tget mk1 (lit_key y) = true -> ou = Some y).
  { intros y Hy. destruct (in_dec Lit.eq_dec y lt) as [Hin | Hnot_in].
    - rewrite Hcleared in Hy by assumption. discriminate.
    - rewrite Hother in Hy.
      + destruct (Hmarked y Hy) as [Hin | Hou].
        * contradiction.
        * assumption.
      + intros z Hz Heq. apply lit_key_inj in Heq. congruence. }
  destruct ou as [u|]; injection Hclear as <- <-; split.
  - intros y. rewrite tget_tset.
    destruct (Nat.eq_dec (lit_key u) (lit_key y)) as [Heq | Hne].
    + reflexivity.
    + destruct (tget mk1 (lit_key y)) eqn:Hy.
      * apply Hmk1 in Hy. injection Hy as ->. contradiction.
      * reflexivity.
  - assumption.
  - intros y. destruct (tget mk1 (lit_key y)) eqn:Hy.
    + apply Hmk1 in Hy. discriminate.
    + reflexivity.
  - assumption.
Qed.

(* Flipping the last decision is a Backjump step, to a consistent context. *)
Lemma flip_spec: forall (m' n: PA) (f: CNF) (x: Ctx) (l: Lit) (c: Clause)
  (mk: Table bool) (s': State) (x': Ctx),
  StepCore ⟨m'; l ++ n⟩ f x -> NoDecisions n -> WellFormed (state ⟨m'; l ++ n⟩ f) ->
  Entails f ⟨m'; l ++ n⟩ -> c ∈ f -> c_eval ⟨m'; l ++ n⟩ c = Some false -> Unmarked mk ->
  flip m' ⟨m'; l ++ n⟩ f x l mk = Some (s', x') ->
  state ⟨m'; l ++ n⟩ f ==>[DPLL_BJ] s' /\
  exists (m2: PA), s' = state m2 f /\ StepCore m2 f x'.
Proof.
  intros m' n f x l c mk s' x' Hcore Hno_dec Hwf Hentails Hc_in_f Hc_false Hmk Hflip.
  pose proof Hcore as [[[Hvals Hfresh Htrail _ _ Hdl _] _ _ _ _ _] _ _ Hsaved _ _ _ _ _].
  unfold flip in Hflip. destruct (saved x) as [|c0 st] eqn:Hsaved_x.
  - discriminate.
  - injection Hflip as <- <-.
    destruct (saved_c_split f (alls x) (nlits x) m' n l (c0 :: st) Hsaved)
      as (c1 & st1 & Hskip & Hc1 & Hst1).
    rewrite no_decisions_zero in Hskip by assumption.
    injection Hskip as <- <-. destruct (fresh_split m' n l Hfresh) as [_ Hl]. split.
    + apply (t_step Backjump).
      * right. right. right. now left.
      * apply backtrack_backjump.
        -- assumption.
        -- assumption.
        -- now apply (r_backtrack m' n f c l).
    + exists ⟨m', (¬l)⟩. split.
      * reflexivity.
      * assert (Hdl': dl x - 1 = decisions m').
        { rewrite Hdl, decisions_app, (no_decisions_zero n Hno_dec). simpl. lia. }
        rewrite Hdl'.
        apply (jump_core m' n f x l (¬l) (unassign_level (vals x) ⟨m'; l ++ n⟩) c0 st
                 mk).
        -- assumption.
        -- apply (unassign_level_spec (vals x) ⟨m'; l ++ n⟩ m' l).
           ++ assumption.
           ++ assumption.
           ++ apply PA.split_last_decision_some_iff. now exists n.
        -- rewrite (unassign_level_spec (vals x) ⟨m'; l ++ n⟩ m' l Hvals Hfresh).
           ++ now apply l_eval_neg_none_iff in Hl.
           ++ apply PA.split_last_decision_some_iff. now exists n.
        -- assumption.
        -- assumption.
        -- assumption.
        -- now left.
Qed.

(* Resolving a conflict on a false clause is a Fail or Backjump step, to a consistent context. *)
Lemma resolve_spec: forall (m: PA) (f: CNF) (x: Ctx) (i: nat) (ls: list Lit) (s': State) (x': Ctx),
  StepCore m f x ->
  WellFormed (state m f) ->
  Entails f m ->
  tget (cmap x) i = Some ls ->
  (forall (y: Lit), In y ls -> lookup (vals x) y = Some false) ->
  resolve m f x i = Some (s', x') ->
  state m f ==>[DPLL_BJ] s' /\ (s' = fail \/ exists (m': PA), s' = state m' f /\ StepCore m' f x').
Proof.
  intros m f x i ls s' x' Hcore Hwf Hentails Hi Hfalse Hres.
  pose proof Hcore as [Hprop _ _ Hsaved _ _ Hmarks _ [Hslots _ _]].
  pose proof (sc_prop _ _ _ Hcore) as [Hcore0 _ _ _ _ _].
  pose proof Hcore0 as [Hvals Hfresh Htrail Hsound _ Hdl Htrace].
  unfold resolve in Hres. pose proof Hi as Hi'. apply Hsound in Hi' as [c [Hc_in_f Hiff]].
  assert (Hc_false: c_eval m c = Some false).
  { apply c_eval_false_iff. intros l Hl. rewrite <- Hvals. apply Hfalse.
    now apply Hiff. }
  destruct (split_last_decision m) as [[m' l]|] eqn:Hsplit.
  2: { (* Fail *)
    injection Hres as <- <-. split.
    - apply (t_step Fail).
      + now left.
      + apply (r_fail m f c).
        * assumption.
        * assumption.
        * now apply PA.split_last_decision_none_iff.
    - now left. }
  apply PA.split_last_decision_some_iff in Hsplit as [n [-> Hno_dec]].
  assert (Hd: dl x = S (decisions m')).
  { rewrite Hdl, decisions_app, (no_decisions_zero n Hno_dec). simpl. lia. }
  rewrite Hd in Hres.
  destruct (analyze x i (S (decisions m')) (PA.length m')) as [[ou mk] lt] eqn:Han.
  destruct (analyze_spec f x m' n l Hcore0 Hno_dec Hslots i ls ou mk lt Hi Hfalse Hmarks
              Han)
    as (Hmarked & Hlower & Hassert).
  destruct (clear_marks (lvl x) mk lt ou) as [mk2 mx] eqn:Hclear.
  destruct (clear_marks_unmarked (lvl x) mk mk2 lt ou mx Hmarked Hclear) as [Hmk2 Hle].
  assert (Hfallback: flip m' ⟨m'; l ++ n⟩ f x l mk2 = Some (s', x') ->
            state ⟨m'; l ++ n⟩ f ==>[DPLL_BJ] s' /\
            (s' = fail \/ exists (m2: PA), s' = state m2 f /\ StepCore m2 f x')).
  { intros Hflip.
    destruct (flip_spec m' n f x l c mk2 s' x' Hcore Hno_dec Hwf Hentails Hc_in_f
                Hc_false Hmk2 Hflip) as [Hstep Hafter].
    split.
    - assumption.
    - now right. }
  destruct ou as [u|].
  2: now apply Hfallback.
  destruct (mx <? S (decisions m')) eqn:Hmx.
  2: now apply Hfallback.
  apply Nat.ltb_lt in Hmx.
  destruct (split_levels (S (decisions m') - S mx) ⟨m'; l ++ n⟩)
    as [[[mt d] n']|] eqn:Hsplit.
  2: now apply Hfallback.
  destruct (skipn (S (decisions m') - S mx) (saved x)) as [|c0 st] eqn:Hskip.
  1: now apply Hfallback.
  destruct (push_reason (jump x (unassign_segment (vals x) d n') (PA.length mt) c0 st mx
                          mk2) u lt)
    as [x1 r] eqn:Hpush.
  injection Hres as <- <-.
  (* The backjump: the analysed clause asserts u at level mx *)
  pose proof (split_levels_decisions _ _ _ _ _ Hsplit) as Hdec_n.
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
  assert (Hu_lv: tget (lvl x) (extract u) = S (decisions m')).
  { rewrite Hu_eq, extract_neg. apply (seg_level f x m' n l Hcore0 Hno_dec). lia. }
  rewrite Hsplit in Hvals, Hfresh, Htrace, Hlower, Hu_false, Hc_false, Hwf, Hcore,
    Hsaved.
  assert (Hlt_false: forall (y: Lit), In y lt -> l_eval mt y = Some false).
  { intros y Hy.
    apply (false_before (cmap x) (rsn x) (lvl x) (rcl x) (rps x) (nr x) mt n' d).
    - assumption.
    - assumption.
    - now apply Hlower.
    - rewrite Hdec_mt. now apply Hle. }
  assert (Hu_undef: l_eval mt u = None).
  { apply (undef_before (cmap x) (rsn x) (lvl x) (rcl x) (rps x) (nr x) mt n' d).
    - assumption.
    - assumption.
    - assumption.
    - lia. }
  rewrite Hsplit. split.
  - apply (t_step Backjump).
    + right. right. right. now left.
    + apply (r_backjump mt n' f c (clause_of (lt ++ [u])) d u).
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
  - right. exists ⟨mt, u⟩. split.
    + reflexivity.
    + destruct (saved_c_split f (alls x) (nlits x) mt n' d (saved x) Hsaved)
        as (c1 & st1 & Hskip1 & Hc1 & Hst1).
      rewrite Hdec_n, Hskip in Hskip1. injection Hskip1 as <- <-.
      apply (jump_core mt n' f x d u (unassign_segment (vals x) d n') c0 st mk2 x1 r).
      * assumption.
      * now apply unassign_segment_spec.
      * now rewrite (unassign_segment_spec (vals x) mt n' d Hvals Hfresh u).
      * assumption.
      * assumption.
      * assumption.
      * right. exists lt. split.
        -- now rewrite Hdec_mt.
        -- split.
           ++ apply (entailed_incl f (lt ++ [u])).
              ** assumption.
              ** intros y Hy. apply in_app_iff in Hy as [Hy | [<- | []]].
                 --- now right.
                 --- now left.
           ++ assumption.
Qed.

(* Flipping the last decision always gives a state. *)
Lemma flip_some: forall (m' n: PA) (f: CNF) (x: Ctx) (l: Lit) (mk: Table bool),
  StepCore ⟨m'; l ++ n⟩ f x -> NoDecisions n -> flip m' ⟨m'; l ++ n⟩ f x l mk <> None.
Proof.
  intros m' n f x l mk Hcore Hno_dec. pose proof Hcore as [_ _ _ Hsaved _ _ _ _ _].
  unfold flip.
  destruct (saved x) as [|c0 st] eqn:Hsaved_x.
  - destruct (saved_c_split f (alls x) (nlits x) m' n l [] Hsaved)
      as (c1 & st1 & Hskip & _).
    rewrite no_decisions_zero in Hskip by assumption. discriminate.
  - discriminate.
Qed.

(* Resolving a conflict always gives a state. *)
Lemma resolve_some: forall (m: PA) (f: CNF) (x: Ctx) (i: nat),
  StepCore m f x -> resolve m f x i <> None.
Proof.
  intros m f x i Hcore. unfold resolve.
  destruct (split_last_decision m) as [[m' l]|] eqn:Hsplit.
  - apply PA.split_last_decision_some_iff in Hsplit as [n [-> Hno_dec]].
    destruct (analyze x i (dl x) (PA.length m')) as [[ou mk] lt].
    destruct (clear_marks (lvl x) mk lt ou) as [mk2 mx].
    destruct ou as [u|].
    + destruct (mx <? dl x).
      * destruct (split_levels (dl x - S mx) ⟨m'; l ++ n⟩) as [[[mt d] n']|].
        -- destruct (skipn (dl x - S mx) (saved x)) as [|c0 st].
           ++ now apply flip_some.
           ++ destruct (push_reason _ u lt). discriminate.
        -- now apply flip_some.
      * now apply flip_some.
    + now apply flip_some.
  - discriminate.
Qed.

(* Resolving a conflict reached by a derivation. *)
Lemma after_resolve: forall (m m1: PA) (f: CNF) (x1: Ctx) (i: nat) (s': State) (x': Ctx),
  WellFormed (state m f) ->
  Entails f m ->
  state m f ==>*[DPLL_BJ] state m1 f ->
  StepCore m1 f x1 ->
  (exists (ls: list Lit), tget (cmap x1) i = Some ls /\ forall (y: Lit), In y ls -> lookup (vals x1) y = Some false) ->
  resolve m1 f x1 i = Some (s', x') ->
  state m f ==>+[DPLL_BJ] s' /\ StepInv s' x'.
Proof.
  intros m m1 f x1 i s' x' Hwf Hentails Hder Hcore [ls [Hi Hfalse]] Hres.
  assert (Hwf1: WellFormed (state m1 f)).
  - now apply (derivation_well_formed DPLL_BJ m m1 f f).
  - assert (Hentails1: Entails f m1).
    + now apply (derivation_entails DPLL_BJ m m1 f f).
    + destruct (resolve_spec m1 f x1 i ls s' x' Hcore Hwf1 Hentails1 Hi Hfalse Hres) as [Hstep [->|[m' [-> Hcore']]]].
      * split.
        -- apply clos_rt_t with (state m1 f).
           ++ assumption.
           ++ now apply Relation_Operators.t_step.
        -- easy.
      * assert (Hplus: state m f ==>+[DPLL_BJ] state m' f).
        -- apply clos_rt_t with (state m1 f).
           ++ assumption.
           ++ now apply Relation_Operators.t_step.
        -- split.
           ++ assumption.
           ++ now apply (step_inv_after m m' f x').
Qed.

(* A step is a strict derivation to a consistent context. *)
Lemma step_spec: forall (m: PA) (f: CNF) (x: Ctx) (s': State) (x': Ctx),
  StepInv (state m f) x -> step (state m f, x) = Some (s', x') -> state m f ==>+[DPLL_BJ] s' /\ StepInv s' x'.
Proof.
  intros m f x s' x' [Hcore [Hwf Hentails]] Hstep. cbn [step] in Hstep.
  destruct (check_shorts (shorts x) m x) as [[m1 x1] r1] eqn:Hcheck.
  destruct (front_shorts m m1 f x x1 r1 Hcore Hcheck) as (Hder1 & Hext1 & Hcore1 & Hnone1 & Hsome1).
  destruct r1 as [i|].
  - apply (after_resolve m m1 f x1 i).
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + now apply Hsome1.
    + assumption.
  - assert (Hwf1: WellFormed (state m1 f)).
    + now apply (derivation_well_formed DPLL_BJ m m1 f f).
    + destruct (propagate (S (nvars x1)) m1 (clear_shorts x1)) as [[m2 x2] r2] eqn:Hprop.
      destruct (front_prop m1 m2 f x1 x2 r2 Hcore1 Hwf1 (Hnone1 eq_refl) Hprop)
        as (Hder2 & Hext2 & Hcore2 & Hshorts2 & Hnonempty2 & Hnone2 & Hsome2).
      assert (Hder: state m f ==>*[DPLL_BJ] state m2 f).
      * now apply rt_trans with (state m1 f).
      * destruct r2 as [i|].
        -- apply (after_resolve m m2 f x2 i).
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ now apply Hsome2.
           ++ assumption.
        -- destruct (skip_from_spec (vals x2) f (alls x2) (nlits x2) (nlits x2 - cur x2) (cur x2)) as [Hc Hundef].
           ++ lia.
           ++ apply Hcore2.
           ++ set (c := skip_from (vals x2) (alls x2) (nlits x2) (nlits x2 - cur x2) (cur x2)) in Hstep, Hc, Hundef.
              destruct (c <? nlits x2) eqn:Hlt.
              (* Decide *)
              ** apply Nat.ltb_lt in Hlt. injection Hstep as <- <-.
                 destruct (decide_spec m2 f x2 c Hcore2 (Hnone2 eq_refl) Hshorts2 Hnonempty2 Hc Hlt (Hundef Hlt))
                   as [Hdecide Hcore3].
                 assert (Hplus: state m f ==>+[DPLL_BJ] state ⟨m2; (phase (phs x2) (tget (alls x2) c))⟩ f).
                 --- apply clos_rt_t with (state m2 f).
                     +++ assumption.
                     +++ now apply Relation_Operators.t_step.
                 --- split.
                     +++ assumption.
                     +++ now apply (step_inv_after m _ f).
              (* Only propagations *)
              ** destruct (Nat.eqb (tlen x2) (tlen x)) eqn:Hsame.
                 --- discriminate.
                 --- injection Hstep as <- <-.
                     assert (Hplus: state m f ==>+[DPLL_BJ] state m2 f).
                     +++ apply derivation_strict.
                         *** assumption.
                         *** intros Heq. injection Heq as Heq.
                             apply Nat.eqb_neq in Hsame. apply Hsame.
                             destruct Hcore
                               as [[[_ _ [Hlen _] _ _ _ _] _ _ _ _ _] _ _ _ _ _ _ _ _].
                             destruct Hcore2
                               as [[[_ _ [Hlen2 _] _ _ _ _] _ _ _ _ _] _ _ _ _ _ _ _ _].
                             now rewrite Hlen, Hlen2, Heq.
                     +++ split.
                         *** assumption.
                         *** apply (step_inv_after m m2 f).
                             ---- assumption.
                             ---- assumption.
                             ---- assumption.
                             ---- destruct Hcore2 as [Hprop2 Hcomplete2 _ Hsaved2 Hempty2
                                    Hshort2 Hmarks2 Hbound2 Hslots2].
                                  split.
                                  ++++ now apply (prop_inv_ext m2 f x2).
                                  ++++ assumption.
                                  ++++ assumption.
                                  ++++ assumption.
                                  ++++ assumption.
                                  ++++ assumption.
                                  ++++ assumption.
                                  ++++ assumption.
                                  ++++ apply (slots_grow f x2).
                                       **** assumption.
                                       **** reflexivity.
                                       **** reflexivity.
                                       **** reflexivity.
                                       **** simpl. lia.
Qed.

(* A step only stops at a final state. *)
Lemma step_none: forall (m: PA) (f: CNF) (x: Ctx),
  StepInv (state m f) x -> step (state m f, x) = None -> Final Basic (state m f).
Proof.
  intros m f x [Hcore [Hwf Hentails]] Hstep. cbn [step] in Hstep.
  destruct (check_shorts (shorts x) m x) as [[m1 x1] r1] eqn:Hcheck.
  destruct (front_shorts m m1 f x x1 r1 Hcore Hcheck) as (Hder1 & Hext1 & Hcore1 & Hnone1 & Hsome1).
  destruct r1 as [i|].
  - exfalso. now apply (resolve_some m1 f x1 i).
  - assert (Hwf1: WellFormed (state m1 f)).
    + now apply (derivation_well_formed DPLL_BJ m m1 f f).
    + destruct (propagate (S (nvars x1)) m1 (clear_shorts x1)) as [[m2 x2] r2] eqn:Hprop.
      destruct (front_prop m1 m2 f x1 x2 r2 Hcore1 Hwf1 (Hnone1 eq_refl) Hprop)
        as (Hder2 & Hext2 & Hcore2 & Hshorts2 & Hnonempty2 & Hnone2 & Hsome2).
      destruct r2 as [i|].
      * exfalso. now apply (resolve_some m2 f x2 i).
      * destruct (skip_from_spec (vals x2) f (alls x2) (nlits x2) (nlits x2 - cur x2) (cur x2)) as [Hc _].
        -- lia.
        -- apply Hcore2.
        -- set (c := skip_from (vals x2) (alls x2) (nlits x2) (nlits x2 - cur x2) (cur x2)) in Hstep, Hc.
           destruct (c <? nlits x2) eqn:Hlt.
           ++ discriminate.
           ++ destruct (Nat.eqb (tlen x2) (tlen x)) eqn:Hsame.
              ** apply Nat.eqb_eq in Hsame. apply Nat.ltb_ge in Hlt.
                 assert (Heq: m2 = m).
                 --- apply extends_same_length.
                     +++ now apply extends_trans with m1.
                     +++ destruct Hcore
                           as [[[_ _ [Hlen _] _ _ _ _] _ _ _ _ _] _ _ _ _ _ _ _ _].
                         destruct Hcore2
                           as [[[_ _ [Hlen2 _] _ _ _ _] _ _ _ _ _] _ _ _ _ _ _ _ _].
                         rewrite <- !trail_lits_length. congruence.
                 --- subst m2. destruct (final_state m f x2 c Hcore2 (Hnone2 eq_refl) Hnonempty2 Hc) as [H1 H2].
                     +++ lia.
                     +++ now apply final_basic_of.
              ** discriminate.
Qed.

(* The solver step is a strategy for DPLL_BJ. *)
Theorem step_strategy: Strategy DPLL_BJ StepInv step.
Proof.
  split.
  - reflexivity.
  - split.
    + intros [|m f] x Hinv Hstep.
      * intros [s' Htrans]. inversion Htrans.
      * now apply (step_none m f x).
    + intros [|m f] s' x x' Hinv Hstep.
      * discriminate.
      * now apply (step_spec m f x).
Qed.

(* The step on the context alone, as C computes it, with lims the positions of the decisions. *)
Section Table.
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

  (* Flip the last decision, at trail position j0, as flip. *)
  Definition flip_t (x: Ctx) (j0: nat) (lims0: list nat) (mk: Table bool): CResult :=
  match saved x with
  | c0 :: st =>
    CNext (assign (jump x (unset_range (vals x) (tr x) j0 (tlen x - j0)) j0 c0 st
                     (dl x - 1) mk)
             (¬tget (tr x) j0) no_reason) lims0
  | []       => CStop
  end.

  (* Resolve a conflict on clause i on the context, as resolve. *)
  Definition resolve_t (x: Ctx) (lims: list nat) (i: nat): CResult :=
  match lims with
  | []          => CFail
  | j0 :: lims0 =>
    match analyze x i (dl x) j0 with
    | (ou, mk, lt) =>
      match clear_marks (lvl x) mk lt ou with
      | (mk2, mx) =>
        match ou with
        | Some u =>
          if mx <? dl x then
            match nth_error lims (dl x - S mx) with
            | Some j =>
              match skipn (dl x - S mx) (saved x) with
              | c0 :: st =>
                match push_reason
                        (jump x (unset_range (vals x) (tr x) j (tlen x - j)) j c0 st mx
                           mk2) u lt with
                | (x1, r) => CNext (assign x1 u r) (skipn (S (dl x - S mx)) lims)
                end
              | []       => flip_t x j0 lims0 mk2
              end
            | None   => flip_t x j0 lims0 mk2
            end
          else flip_t x j0 lims0 mk2
        | None   => flip_t x j0 lims0 mk2
        end
      end
    end
  end.

  (* One step on the context, as step. *)
  Definition cstep (x: Ctx) (lims: list nat): CResult :=
  match check_shorts_t (shorts x) x with
  | (x1, Some i) => resolve_t x1 lims i
  | (x1, None)   =>
    match propagate_t (S (nvars x1)) (clear_shorts x1) with
    | (x2, Some i) => resolve_t x2 lims i
    | (x2, None)   =>
      let c := skip_from (vals x2) (alls x2) (nlits x2) (nlits x2 - cur x2) (cur x2) in
      if c <? nlits x2 then
        CNext (assign (open_level x2 c) (phase (phs x2) (tget (alls x2) c)) no_reason)
          (tlen x2 :: lims)
      else if Nat.eqb (tlen x2) (tlen x) then CStop else CNext (with_cursor x2 c) lims
    end
  end.

  (* Flipping on the context agrees with flip. *)
  Lemma flip_t_spec: forall (m' n: PA) (f: CNF) (x: Ctx) (l: Lit) (lims0: list nat)
    (mk: Table bool),
    TrailOf (tr x) (tlen x) ⟨m'; l ++ n⟩ -> NoDecisions n -> LimsOf lims0 m' ->
    Agrees f (flip m' ⟨m'; l ++ n⟩ f x l mk) (flip_t x (PA.length m') lims0 mk).
  Proof.
    intros m' n f x l lims0 mk Htrail Hn Hlims0. unfold flip, flip_t.
    assert (Hlen: tlen x = S (PA.length m' + PA.length n)).
    { destruct Htrail as [Hlen _].
      rewrite Hlen, trail_lits_length, (pa_length_app ⟨m'; l⟩ n). simpl. lia. }
    destruct (saved x) as [|c0 st].
    - reflexivity.
    - exists ⟨m', (¬l)⟩. split.
      + destruct (trail_of_snoc (tr x) _ m' ⟨m'; l⟩ l eq_refl
          (trail_of_prefix (tr x) (tlen x) ⟨m'; l⟩ n Htrail)) as (_ & Hl & _).
        rewrite Hl. replace (tlen x - PA.length m') with (S (PA.length n)) by lia.
        rewrite (unset_range_spec _ _ m' n l _ Htrail).
        rewrite <- (unassign_level_segment _ m' n l Hn).
        reflexivity.
      + assumption.
  Qed.

  (* Resolving a conflict on the context agrees with resolve. *)
  Lemma resolve_t_spec: forall (m: PA) (f: CNF) (x: Ctx) (lims: list nat) (i: nat),
    TrailOf (tr x) (tlen x) m -> LimsOf lims m ->
    Agrees f (resolve m f x i) (resolve_t x lims i).
  Proof.
    intros m f x lims i Htrail Hlims. unfold resolve, resolve_t.
    destruct (split_last_decision m) as [[m' l]|] eqn:Hsplit.
    - apply PA.split_last_decision_some_iff in Hsplit as [n [-> Hn]].
      destruct (lims_split lims m' n l Hlims) as (lims' & Hskip & Hlims' & _).
      rewrite no_decisions_zero in Hskip by assumption. simpl in Hskip. subst lims.
      destruct (analyze x i (dl x) (PA.length m')) as [[ou mk] lt].
      destruct (clear_marks (lvl x) mk lt ou) as [mk2 mx].
      destruct ou as [u|].
      2: now apply flip_t_spec.
      destruct (mx <? dl x).
      2: now apply flip_t_spec.
      destruct (split_levels (dl x - S mx) ⟨m'; l ++ n⟩) as [[[mt d] n']|] eqn:Hsplit.
      + destruct (split_levels_lims _ _ _ _ _ _ Hlims Hsplit) as [Hnth Hlims_mt].
        rewrite Hnth.
        destruct (skipn (dl x - S mx) (saved x)) as [|c0 st].
        * now apply flip_t_spec.
        * apply split_levels_spec in Hsplit. rewrite Hsplit in Htrail.
          assert (Hlen: tlen x - PA.length mt = S (PA.length n')).
          { destruct Htrail as [Hlen _].
            rewrite Hlen, trail_lits_length, (pa_length_app ⟨mt; d⟩ n').
            cbn [PA.length]. lia. }
          rewrite Hlen, (unset_range_spec _ _ mt n' d _ Htrail).
          destruct (push_reason _ u lt) as [x1 r]. exists ⟨mt, u⟩. split.
          -- reflexivity.
          -- assumption.
      + rewrite (split_levels_lims_none _ _ _ Hlims Hsplit). now apply flip_t_spec.
    - apply PA.split_last_decision_none_iff in Hsplit. destruct lims as [|j lims].
      + now exists x.
      + exfalso. clear - Hlims Hsplit. induction m as [|m IH y|m IH y]; simpl in Hlims, Hsplit.
        * discriminate.
        * now apply IH.
        * destruct Hsplit.
  Qed.

  (* The step on the context agrees with step. *)
  Lemma cstep_spec: forall (m: PA) (f: CNF) (x: Ctx) (lims: list nat),
    StepInv (state m f) x -> LimsOf lims m -> Agrees f (step (state m f, x)) (cstep x lims).
  Proof.
    intros m f x lims [Hcore [Hwf Hentails]] Hlims. cbn [step]. unfold cstep.
    destruct (check_shorts (shorts x) m x) as [[m1 x1] r1] eqn:Hcheck.
    destruct (front_shorts m m1 f x x1 r1 Hcore Hcheck) as (Hder1 & Hext1 & Hcore1 & Hnone1 & _).
    rewrite (check_shorts_free _ _ _ _ _ _ Hcheck).
    assert (Hlims1: LimsOf lims m1) by now apply (lims_extends lims m).
    destruct r1 as [i|].
    - apply resolve_t_spec.
      + apply Hcore1.
      + assumption.
    - assert (Hwf1: WellFormed (state m1 f)) by now apply (derivation_well_formed DPLL_BJ m m1 f f).
      destruct (propagate (S (nvars x1)) m1 (clear_shorts x1)) as [[m2 x2] r2] eqn:Hprop.
      destruct (front_prop m1 m2 f x1 x2 r2 Hcore1 Hwf1 (Hnone1 eq_refl) Hprop) as (_ & Hext2 & Hcore2 & _).
      rewrite (propagate_free _ _ _ _ _ _ Hprop).
      assert (Hlims2: LimsOf lims m2) by now apply (lims_extends lims m1).
      destruct r2 as [i|].
      + apply resolve_t_spec.
        * apply Hcore2.
        * assumption.
      + destruct (_ <? nlits x2).
        * exists ⟨m2; (phase (phs x2) (tget (alls x2) (skip_from (vals x2) (alls x2) (nlits x2) (nlits x2 - cur x2)
            (cur x2))))⟩. split.
          -- reflexivity.
          -- simpl. split.
             ++ destruct Hcore2 as [[[_ _ [Hlen _] _ _ _ _] _ _ _ _ _] _ _ _ _ _ _ _ _].
                now rewrite Hlen, trail_lits_length.
             ++ assumption.
        * destruct (Nat.eqb (tlen x2) (tlen x)).
          -- reflexivity.
          -- now exists m2.
  Qed.
End Table.
