From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Relations.
Import ListNotations.

From RocqSAT Require Import Lit.
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
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement Require Import Step.
From RocqSAT.refinement Require Import CStep.

(* The solver, whose step the C solver computes: check the short clauses, propagate with two watched literals
   (Propagate.v) and decide at the cursor (Step.v); on a conflict, fail without decisions and flip the last decision
   otherwise. step_strategy; cstep computes the same step from the context alone (CStep.v), cstep_spec. *)

(* Resolve a conflict: fail without decisions, and flip the last decision otherwise. *)
Definition resolve (m: PA) (f: CNF) (x: Ctx): option (State * Ctx) :=
match split_last_decision m with
| None         => Some (fail, x)
| Some (m', l) =>
  match saved x with
  | c0 :: st =>
    Some (state ⟨m', (¬l)⟩ f, assign (jump x (unassign_level (vals x) m) (tlen x - S (level_length m)) c0 st
      (dl x - 1) (mrk x)) (¬l) 0)
  | []       => None
  end
end.

(* One step: check the short clauses and propagate; on a conflict resolve, and otherwise decide. *)
Definition step (p: State * Ctx): option (State * Ctx) :=
match p with
| (fail, _)      => None
| (state m f, x) =>
  match check_shorts (shorts x) m x with
  | (m1, x1, Some _) => resolve m1 f x1
  | (m1, x1, None)   =>
    match propagate (S (nvars x1)) m1 (clear_shorts x1) with
    | (m2, x2, Some _) => resolve m2 f x2
    | (m2, x2, None)   =>
      let c := skip_from (vals x2) (alls x2) (nlits x2) (nlits x2 - cur x2) (cur x2) in
      if c <? nlits x2 then
        let l := phase (phs x2) (tget (alls x2) c) in
        Some (state ⟨m2; l⟩ f, assign (open_level x2 c) l 0)
      else if Nat.eqb (tlen x2) (tlen x) then None else Some (state m2 f, with_cursor x2 c)
    end
  end
end.

(* Resolving a conflict on a false clause is a Fail or Backjump step, to a consistent context. *)
Lemma resolve_spec: forall (m: PA) (f: CNF) (x: Ctx) (i: nat) (ls: list Lit) (s': State) (x': Ctx),
  StepCore m f x ->
  WellFormed (state m f) ->
  Entails f m ->
  tget (cmap x) i = Some ls ->
  (forall (y: Lit), In y ls -> lookup (vals x) y = Some false) ->
  resolve m f x = Some (s', x') ->
  state m f ==>[DPLL_BJ] s' /\ (s' = fail \/ exists (m': PA), s' = state m' f /\ StepCore m' f x').
Proof.
  intros m f x i ls s' x' Hcore Hwf Hentails Hi Hfalse Hres.
  pose proof Hcore as [[[Hvals Hfresh Htrail Hsound _] _ _ _ _] _ _ Hsaved _ _ Hmarks _].
  unfold resolve in Hres. pose proof Hi as Hi'. apply Hsound in Hi' as [c [Hc_in_f Hiff]].
  assert (Hc_false: c_eval m c = Some false).
  - apply c_eval_false_iff. intros l Hl. rewrite <- Hvals. apply Hfalse. now apply Hiff.
  - destruct (split_last_decision m) as [[m' l]|] eqn:Hsplit.
    + destruct (saved x) as [|c0 st] eqn:Hsaved_x.
      * discriminate.
      * injection Hres as <- <-. apply PA.split_last_decision_some_iff in Hsplit as [n [-> Hno_dec]].
        destruct (saved_c_split f (alls x) (nlits x) m' n l (c0 :: st) Hsaved) as (c1 & st1 & Hskip & Hc1 & Hst1).
        rewrite no_decisions_zero in Hskip.
        2: assumption.
        injection Hskip as <- <-. destruct (fresh_split m' n l Hfresh) as [_ Hl]. split.
        -- apply (t_step Backjump).
           ++ right. right. right. now left.
           ++ apply backtrack_backjump.
              ** assumption.
              ** assumption.
              ** now apply (r_backtrack m' n f c l).
        -- right. exists ⟨m', (¬l)⟩. split.
           ++ reflexivity.
           ++ rewrite (level_length_split _ m' l n eq_refl Hno_dec), (length_split (tr x) (tlen x) m' n l Htrail).
              apply (jump_core m' n f x l).
              ** assumption.
              ** apply (unassign_level_spec (vals x) ⟨m'; l ++ n⟩ m' l).
                 --- assumption.
                 --- assumption.
                 --- apply PA.split_last_decision_some_iff. now exists n.
              ** rewrite (unassign_level_spec (vals x) ⟨m'; l ++ n⟩ m' l Hvals Hfresh).
                 --- now apply l_eval_neg_none_iff in Hl.
                 --- apply PA.split_last_decision_some_iff. now exists n.
              ** assumption.
              ** assumption.
              ** assumption.
    + injection Hres as <- <-. split.
      * apply (t_step Fail).
        -- now left.
        -- apply (r_fail m f c).
           ++ assumption.
           ++ assumption.
           ++ now apply PA.split_last_decision_none_iff.
      * now left.
Qed.

(* Resolving a conflict always gives a state. *)
Lemma resolve_some: forall (m: PA) (f: CNF) (x: Ctx), StepCore m f x -> resolve m f x <> None.
Proof.
  intros m f x Hcore Hres. pose proof Hcore as [_ _ _ Hsaved _ _ _ _]. unfold resolve in Hres.
  destruct (split_last_decision m) as [[m' l]|] eqn:Hsplit.
  - destruct (saved x) as [|c0 st] eqn:Hsaved_x.
    + apply PA.split_last_decision_some_iff in Hsplit as [n [-> Hno_dec]].
      destruct (saved_c_split f (alls x) (nlits x) m' n l [] Hsaved) as (c1 & st1 & Hskip & _).
      rewrite no_decisions_zero in Hskip.
      * discriminate.
      * assumption.
    + discriminate.
  - discriminate.
Qed.

(* Resolving a conflict reached by a derivation. *)
Lemma after_resolve: forall (m m1: PA) (f: CNF) (x1: Ctx) (i: nat) (s': State) (x': Ctx),
  WellFormed (state m f) ->
  Entails f m ->
  state m f ==>*[DPLL_BJ] state m1 f ->
  StepCore m1 f x1 ->
  (exists (ls: list Lit), tget (cmap x1) i = Some ls /\ forall (y: Lit), In y ls -> lookup (vals x1) y = Some false) ->
  resolve m1 f x1 = Some (s', x') ->
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
                         *** intros Heq. injection Heq as Heq. apply Nat.eqb_neq in Hsame. apply Hsame.
                             destruct Hcore as [[[_ _ [Hlen _] _ _] _ _ _ _] _ _ _ _ _ _ _].
                             destruct Hcore2 as [[[_ _ [Hlen2 _] _ _] _ _ _ _] _ _ _ _ _ _ _].
                             now rewrite Hlen, Hlen2, Heq.
                     +++ split.
                         *** assumption.
                         *** apply (step_inv_after m m2 f).
                             ---- assumption.
                             ---- assumption.
                             ---- assumption.
                             ---- destruct Hcore2 as [Hprop2 Hcomplete2 _ Hsaved2 Hempty2 Hshort2 Hmarks2 Hbound2].
                                  split.
                                  ++++ now apply (prop_inv_ext m2 f x2).
                                  ++++ assumption.
                                  ++++ assumption.
                                  ++++ assumption.
                                  ++++ assumption.
                                  ++++ assumption.
                                  ++++ assumption.
                                  ++++ assumption.
Qed.

(* A step only stops at a final state. *)
Lemma step_none: forall (m: PA) (f: CNF) (x: Ctx),
  StepInv (state m f) x -> step (state m f, x) = None -> Final Basic (state m f).
Proof.
  intros m f x [Hcore [Hwf Hentails]] Hstep. cbn [step] in Hstep.
  destruct (check_shorts (shorts x) m x) as [[m1 x1] r1] eqn:Hcheck.
  destruct (front_shorts m m1 f x x1 r1 Hcore Hcheck) as (Hder1 & Hext1 & Hcore1 & Hnone1 & Hsome1).
  destruct r1 as [i|].
  - exfalso. now apply (resolve_some m1 f x1).
  - assert (Hwf1: WellFormed (state m1 f)).
    + now apply (derivation_well_formed DPLL_BJ m m1 f f).
    + destruct (propagate (S (nvars x1)) m1 (clear_shorts x1)) as [[m2 x2] r2] eqn:Hprop.
      destruct (front_prop m1 m2 f x1 x2 r2 Hcore1 Hwf1 (Hnone1 eq_refl) Hprop)
        as (Hder2 & Hext2 & Hcore2 & Hshorts2 & Hnonempty2 & Hnone2 & Hsome2).
      destruct r2 as [i|].
      * exfalso. now apply (resolve_some m2 f x2).
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
                     +++ destruct Hcore as [[[_ _ [Hlen _] _ _] _ _ _ _] _ _ _ _ _ _ _].
                         destruct Hcore2 as [[[_ _ [Hlen2 _] _ _] _ _ _ _] _ _ _ _ _ _ _].
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
  (* Resolve a conflict on the context, as resolve. *)
  Definition resolve_t (x: Ctx) (lims: list nat): CResult :=
  match lims with
  | []          => CFail
  | j0 :: lims0 =>
    match saved x with
    | c0 :: st =>
      CNext (assign (jump x (unset_range (vals x) (tr x) j0 (tlen x - j0)) j0 c0 st (dl x - 1) (mrk x))
        (¬(tget (tr x) j0)) 0) lims0
    | []       => CStop
    end
  end.

  (* One step on the context, as step. *)
  Definition cstep (x: Ctx) (lims: list nat): CResult :=
  match check_shorts_t (shorts x) x with
  | (x1, Some _) => resolve_t x1 lims
  | (x1, None)   =>
    match propagate_t (S (nvars x1)) (clear_shorts x1) with
    | (x2, Some _) => resolve_t x2 lims
    | (x2, None)   =>
      let c := skip_from (vals x2) (alls x2) (nlits x2) (nlits x2 - cur x2) (cur x2) in
      if c <? nlits x2 then CNext (assign (open_level x2 c) (phase (phs x2) (tget (alls x2) c)) 0) (tlen x2 :: lims)
      else if Nat.eqb (tlen x2) (tlen x) then CStop else CNext (with_cursor x2 c) lims
    end
  end.

  Lemma resolve_t_spec: forall (m: PA) (f: CNF) (x: Ctx) (lims: list nat),
    TrailOf (tr x) (tlen x) m -> LimsOf lims m -> Agrees f (resolve m f x) (resolve_t x lims).
  Proof.
    intros m f x lims Htrail Hlims. unfold resolve, resolve_t.
    destruct (split_last_decision m) as [[m' l]|] eqn:Hsplit.
    - apply PA.split_last_decision_some_iff in Hsplit as [n [-> Hn]].
      destruct (lims_split lims m' n l Hlims) as (lims' & Hskip & Hlims' & _).
      rewrite no_decisions_zero in Hskip by assumption. simpl in Hskip. subst lims.
      assert (Hlen: tlen x = S (PA.length m' + PA.length n)).
      + destruct Htrail as [Hlen _]. rewrite Hlen, trail_lits_length, (pa_length_app ⟨m'; l⟩ n). simpl. lia.
      + destruct (saved x) as [|c0 st].
        * reflexivity.
        * exists ⟨m', (¬l)⟩. split.
          -- destruct (trail_of_snoc (tr x) _ m' ⟨m'; l⟩ l eq_refl
               (trail_of_prefix (tr x) (tlen x) ⟨m'; l⟩ n Htrail)) as (_ & Hl & _).
             rewrite Hl. replace (tlen x - PA.length m') with (S (PA.length n)) by lia.
             rewrite (unset_range_spec _ _ m' n l _ Htrail), <- (unassign_level_segment _ m' n l Hn).
             rewrite (level_length_split _ m' l n eq_refl Hn), (length_split (tr x) (tlen x) m' n l Htrail).
             reflexivity.
          -- assumption.
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
             ++ destruct Hcore2 as [[[_ _ [Hlen _] _ _] _ _ _ _] _ _ _ _ _ _ _]. now rewrite Hlen, trail_lits_length.
             ++ assumption.
        * destruct (Nat.eqb (tlen x2) (tlen x)).
          -- reflexivity.
          -- now exists m2.
  Qed.
End Table.
