From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Relations.
From Stdlib Require SetoidList.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import State.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import Entails.
From RocqSAT Require Import Measure.
From RocqSAT Require Import Trans.
From RocqSAT Require Import Strategy.
From RocqSAT.rules Require Import Fail.
From RocqSAT.rules Require Import Backtrack.
From RocqSAT.rules Require Import Backjump.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Search.
From RocqSAT.refinement Require Import Analysis.
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement Require Import Step.

(* The solver step with conflict analysis: as in Step.v, but on a conflict analyse it (Analysis.v) and backjump to
   the level it gives; analysis_step_strategy. The C solver does not use it: it runs the step of SolverStep.v. *)

(* Resolve the conflict on the false clause i of m: fail without decisions; otherwise analyse it and backjump as
   planned, or else flip the last decision. *)
Definition analysis_resolve (m: PA) (f: CNF) (x: Ctx) (i: nat): option (State * Ctx) :=
match tget (cmap x) i with
| None    => None
| Some ls =>
  match split_last_decision m with
  | None         => Some (fail, x)
  | Some (m', l) =>
    match analyze (cmap x) (rsn x) (lvl x) (dl x) m (set_marks (mrk x) ls true) ls (count_level (lvl x) (dl x) ls) with
    | (c, mk) =>
      match plan (vals x) (lvl x) (dl x) m (set_marks mk c true) c with
      | Some (u, (mt, d, n)) =>
        match skipn (decisions n) (saved x) with
        | c0 :: st =>
          Some (state ⟨mt, u⟩ f, assign (jump x (unassign_segment (vals x) d n) (tlen x - S (PA.length n)) c0 st
            (dl x - S (decisions n)) (set_marks (set_marks mk c true) c false)) u 0)
        | []       => None
        end
      | None =>
        match saved x with
        | c0 :: st =>
          Some (state ⟨m', (¬l)⟩ f, assign (jump x (unassign_level (vals x) m) (tlen x - S (level_length m)) c0 st
            (dl x - 1)
            (set_marks (set_marks mk c true) c false)) (¬l) 0)
        | []       => None
        end
      end
    end
  end
end.

(* One solver step: check the short clauses and propagate; on a conflict resolve it, and otherwise decide the
   first unassigned literal with its phase. If there is nothing to decide, stop, unless propagation made progress. *)
Definition analysis_step (p: State * Ctx): option (State * Ctx) :=
match p with
| (fail, _)      => None
| (state m f, x) =>
  match check_shorts (shorts x) m x with
  | (m1, x1, Some i) => analysis_resolve m1 f x1 i
  | (m1, x1, None)   =>
    match propagate (S (nvars x1)) m1 (clear_shorts x1) with
    | (m2, x2, Some i) => analysis_resolve m2 f x2 i
    | (m2, x2, None)   =>
      let c := skip_from (vals x2) (alls x2) (nlits x2) (nlits x2 - cur x2) (cur x2) in
      if c <? nlits x2 then
        let l := phase (phs x2) (tget (alls x2) c) in
        Some (state ⟨m2; l⟩ f, assign (open_level x2 c) l 0)
      else if Nat.eqb (tlen x2) (tlen x) then None else Some (state m2 f, with_cursor x2 c)
    end
  end
end.

(* Resolving a conflict on the false clause i is a Fail or Backjump step, to a consistent context. *)
Lemma analysis_resolve_spec: forall (m: PA) (f: CNF) (x: Ctx) (i: nat) (ls: list Lit) (s': State) (x': Ctx),
  StepCore m f x ->
  WellFormed (state m f) ->
  Entails f m ->
  tget (cmap x) i = Some ls ->
  (forall (y: Lit), In y ls -> lookup (vals x) y = Some false) ->
  analysis_resolve m f x i = Some (s', x') ->
  state m f ==>[DPLL_BJ] s' /\ (s' = fail \/ exists (m': PA), s' = state m' f /\ StepCore m' f x').
Proof.
  intros m f x i ls s' x' Hcore Hwf Hentails Hi Hfalse Hres.
  pose proof Hcore as [[[Hvals Hfresh Htrail Hsound _] _ _ _ _] _ _ Hsaved _ _ Hmarks _].
  unfold analysis_resolve in Hres. rewrite Hi in Hres.
  assert (Hall: forall (j: nat) (r: list Lit), tget (cmap x) j = Some r -> Entailed f r).
  - intros j r Hj. apply entailed_clause_of. now apply Hsound with j.
  - assert (Hls: Entailed f ls).
    + now apply (Hall i).
    + pose proof Hi as Hi'. apply Hsound in Hi' as [c [Hc_in_f Hiff]].
      assert (Hc_false: c_eval m c = Some false).
      * apply c_eval_false_iff. intros l Hl. rewrite <- Hvals. apply Hfalse. now apply Hiff.
      * destruct (split_last_decision m) as [[m' l]|] eqn:Hsplit.
        -- destruct (analyze (cmap x) (rsn x) (lvl x) (dl x) m (set_marks (mrk x) ls true)
             ls (count_level (lvl x) (dl x) ls)) as [c' mk] eqn:Hanalyze.
           destruct (analyze_spec f (cmap x) (rsn x) (lvl x) (dl x) m _ mk ls c' _ Hall Hls
             (set_marks_marked_in (mrk x) ls Hmarks) Hanalyze) as [Hc' Hmk].
           destruct (plan (vals x) (lvl x) (dl x) m (set_marks mk c' true) c') as [[u [[mt d] n]]|] eqn:Hplan.
           (* Backjump *)
           ++ destruct (plan_spec (vals x) (lvl x) (dl x) m mt n _ _ u d Hvals Hfresh (set_marks_in _ _ true) Hplan)
                as (Hm & Hu_in & Hu_false & Hu & Hrest).
              subst m. destruct (saved_c_split f (alls x) (nlits x) mt n d (saved x) Hsaved) as (c0 & st & Hskip & Hc0 & Hst).
              rewrite Hskip in Hres. injection Hres as <- <-. split.
              ** apply (t_step Backjump).
                 --- right. right. right. now left.
                 --- apply (r_backjump mt n f c (clause_of c') d u).
                     +++ assumption.
                     +++ assumption.
                     +++ now apply entailed_consequence.
                     +++ now apply clause_of_spec.
                     +++ apply c_eval_false_iff. intros y Hy. apply Clause.remove_spec in Hy as [Hy Hneq].
                         apply clause_of_spec in Hy. now apply Hrest.
                     +++ assumption.
                     +++ destruct Hwf as [_ Hbounded]. apply l_eval_false_in, Hbounded in Hu_false.
                         rewrite Neg.involutive in Hu_false. now apply or_comm.
              ** right. exists ⟨mt, u⟩. split.
                 --- reflexivity.
                 --- rewrite (length_split (tr x) (tlen x) mt n d Htrail). apply (jump_core mt n f x d).
                     +++ assumption.
                     +++ apply unassign_segment_spec.
                         *** assumption.
                         *** assumption.
                     +++ rewrite (unassign_segment_spec (vals x) mt n d Hvals Hfresh u). assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ now apply set_marks_unmarked, set_marks_true_marked_in.
           (* Otherwise a backtrack, which is a backjump *)
           ++ destruct (saved x) as [|c0 st] eqn:Hsaved_x.
              ** discriminate.
              ** injection Hres as <- <-. apply PA.split_last_decision_some_iff in Hsplit as [n [-> Hno_dec]].
                 destruct (saved_c_split f (alls x) (nlits x) m' n l (c0 :: st) Hsaved) as (c1 & st1 & Hskip & Hc1 & Hst1).
                 rewrite no_decisions_zero in Hskip.
                 2: assumption.
                 injection Hskip as <- <-. destruct (fresh_split m' n l Hfresh) as [_ Hl]. split.
                 --- apply (t_step Backjump).
                     +++ right. right. right. now left.
                     +++ apply backtrack_backjump.
                         *** assumption.
                         *** assumption.
                         *** now apply (r_backtrack m' n f c l).
                 --- right. exists ⟨m', (¬l)⟩. split.
                     +++ reflexivity.
                     +++ rewrite (level_length_split _ m' l n eq_refl Hno_dec), (length_split (tr x) (tlen x) m' n l Htrail).
                         apply (jump_core m' n f x l).
                         *** assumption.
                         *** apply (unassign_level_spec (vals x) ⟨m'; l ++ n⟩ m' l).
                             ---- assumption.
                             ---- assumption.
                             ---- apply PA.split_last_decision_some_iff. now exists n.
                         *** rewrite (unassign_level_spec (vals x) ⟨m'; l ++ n⟩ m' l Hvals Hfresh).
                             ---- now apply l_eval_neg_none_iff in Hl.
                             ---- apply PA.split_last_decision_some_iff. now exists n.
                         *** assumption.
                         *** assumption.
                         *** now apply set_marks_unmarked, set_marks_true_marked_in.
        (* Fail *)
        -- injection Hres as <- <-. split.
           ++ apply (t_step Fail).
              ** now left.
              ** apply (r_fail m f c).
                 --- assumption.
                 --- assumption.
                 --- now apply PA.split_last_decision_none_iff.
           ++ now left.
Qed.

(* Resolving a conflict always gives a state. *)
Lemma analysis_resolve_some: forall (m: PA) (f: CNF) (x: Ctx) (i: nat) (ls: list Lit),
  StepCore m f x -> tget (cmap x) i = Some ls -> analysis_resolve m f x i <> None.
Proof.
  intros m f x i ls Hcore Hi Hres. pose proof Hcore as [[[Hvals Hfresh _ _ _] _ _ _ _] _ _ Hsaved _ _ _ _].
  unfold analysis_resolve in Hres. rewrite Hi in Hres.
  destruct (split_last_decision m) as [[m' l]|] eqn:Hsplit.
  - destruct (analyze (cmap x) (rsn x) (lvl x) (dl x) m (set_marks (mrk x) ls true) ls (count_level (lvl x) (dl x) ls))
      as [c mk].
    destruct (plan (vals x) (lvl x) (dl x) m (set_marks mk c true) c) as [[u [[mt d] n]]|] eqn:Hplan.
    + destruct (plan_spec (vals x) (lvl x) (dl x) m mt n _ _ u d Hvals Hfresh (set_marks_in _ _ true) Hplan) as (-> & _).
      destruct (saved_c_split f (alls x) (nlits x) mt n d (saved x) Hsaved) as (c0 & st & Hskip & _).
      rewrite Hskip in Hres. discriminate.
    + destruct (saved x) as [|c0 st] eqn:Hsaved_x.
      * apply PA.split_last_decision_some_iff in Hsplit as [n [-> Hno_dec]].
        destruct (saved_c_split f (alls x) (nlits x) m' n l [] Hsaved) as (c1 & st1 & Hskip & _).
        rewrite no_decisions_zero in Hskip.
        -- discriminate.
        -- assumption.
      * discriminate.
  - discriminate.
Qed.

Section Derivations.
  (* Resolving a conflict reached by a derivation. *)
  Lemma analysis_after_resolve: forall (m m1: PA) (f: CNF) (x1: Ctx) (i: nat) (s': State) (x': Ctx),
    WellFormed (state m f) ->
    Entails f m ->
    state m f ==>*[DPLL_BJ] state m1 f ->
    StepCore m1 f x1 ->
    (exists (ls: list Lit), tget (cmap x1) i = Some ls /\ forall (y: Lit), In y ls -> lookup (vals x1) y = Some false) ->
    analysis_resolve m1 f x1 i = Some (s', x') ->
    state m f ==>+[DPLL_BJ] s' /\ StepInv s' x'.
  Proof.
    intros m m1 f x1 i s' x' Hwf Hentails Hder Hcore [ls [Hi Hfalse]] Hres.
    assert (Hwf1: WellFormed (state m1 f)).
    - now apply (derivation_well_formed DPLL_BJ m m1 f f).
    - assert (Hentails1: Entails f m1).
      + now apply (derivation_entails DPLL_BJ m m1 f f).
      + destruct (analysis_resolve_spec m1 f x1 i ls s' x' Hcore Hwf1 Hentails1 Hi Hfalse Hres) as [Hstep [->|[m' [-> Hcore']]]].
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
End Derivations.

(* A step is a strict derivation to a consistent context. *)
Lemma analysis_step_spec: forall (m: PA) (f: CNF) (x: Ctx) (s': State) (x': Ctx),
  StepInv (state m f) x -> analysis_step (state m f, x) = Some (s', x') -> state m f ==>+[DPLL_BJ] s' /\ StepInv s' x'.
Proof.
  intros m f x s' x' [Hcore [Hwf Hentails]] Hstep. cbn [analysis_step] in Hstep.
  destruct (check_shorts (shorts x) m x) as [[m1 x1] r1] eqn:Hcheck.
  destruct (front_shorts m m1 f x x1 r1 Hcore Hcheck) as (Hder1 & Hext1 & Hcore1 & Hnone1 & Hsome1).
  destruct r1 as [i|].
  - apply (analysis_after_resolve m m1 f x1 i).
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
        -- apply (analysis_after_resolve m m2 f x2 i).
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
Lemma analysis_step_none: forall (m: PA) (f: CNF) (x: Ctx),
  StepInv (state m f) x -> analysis_step (state m f, x) = None -> Final Basic (state m f).
Proof.
  intros m f x [Hcore [Hwf Hentails]] Hstep. cbn [analysis_step] in Hstep.
  destruct (check_shorts (shorts x) m x) as [[m1 x1] r1] eqn:Hcheck.
  destruct (front_shorts m m1 f x x1 r1 Hcore Hcheck) as (Hder1 & Hext1 & Hcore1 & Hnone1 & Hsome1).
  destruct r1 as [i|].
  - destruct (Hsome1 i eq_refl) as [ls [Hi _]]. exfalso. now apply (analysis_resolve_some m1 f x1 i ls).
  - assert (Hwf1: WellFormed (state m1 f)).
    + now apply (derivation_well_formed DPLL_BJ m m1 f f).
    + destruct (propagate (S (nvars x1)) m1 (clear_shorts x1)) as [[m2 x2] r2] eqn:Hprop.
      destruct (front_prop m1 m2 f x1 x2 r2 Hcore1 Hwf1 (Hnone1 eq_refl) Hprop)
        as (Hder2 & Hext2 & Hcore2 & Hshorts2 & Hnonempty2 & Hnone2 & Hsome2).
      destruct r2 as [i|].
      * destruct (Hsome2 i eq_refl) as [ls [Hi _]]. exfalso. now apply (analysis_resolve_some m2 f x2 i ls).
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

Lemma analysis_step_strategy: Strategy DPLL_BJ StepInv analysis_step.
Proof.
  split.
  - reflexivity.
  - split.
    + intros [|m f] x Hinv Hstep.
      * intros [s' Htrans]. inversion Htrans.
      * now apply (analysis_step_none m f x).
    + intros [|m f] s' x x' Hinv Hstep.
      * discriminate.
      * now apply (analysis_step_spec m f x).
Qed.

Section Initial.
  (* The literals of a clause have no duplicates. *)
  Lemma nodupa_nodup: forall (ls: list Lit), SetoidList.NoDupA eq ls -> NoDup ls.
  Proof.
    intros ls H. induction H as [|y ls Hnotin _ IH].
    - constructor.
    - constructor.
      + intros Hin. apply Hnotin. apply SetoidList.In_InA.
        * split.
          -- intros a. reflexivity.
          -- intros a b Hab. now symmetry.
          -- intros a b c Hab Hbc. now rewrite Hab.
        * assumption.
      + assumption.
  Qed.

  (* The initial context of f, for the clauses and literals of f. *)
  Definition initial_ctx (f: CNF): Ctx :=
  initial_of (clause_lists f) (Clause.elements (formula_lits f)) (S (max_atom_f f)).

  Lemma initial_ctx_inv: forall (f: CNF), StepInv (state ⟨⟩ f) (initial_ctx f).
  Proof.
    intros f. apply initial_of_inv.
    - intros cs Hin. split.
      + apply in_clause_lists in Hin as [c [-> _]]. apply nodupa_nodup, Clause.elements_spec2w.
      + now apply clause_lists_clause_of.
    - intros c Hc_in_f. apply clause_lists_in in Hc_in_f as [c' [Heq Hin]]. exists (Clause.elements c'). split.
      + assumption.
      + intros l. rewrite clause_elements_iff. split.
        * intros Hl. now apply Heq.
        * intros Hl. now apply Heq.
    - intros l. rewrite clause_elements_iff. apply formula_lits_spec.
    - reflexivity.
  Qed.
End Initial.
