(* solve runs the solver to the end: it terminates, and answers whether the formula is
   satisfiable, unless it gives up. *)
From Stdlib Require Import List Relations.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit Clause CNF Assignment Evaluation State Satisfiability
  Trans Termination WellFormed.
From RocqSAT Require Import Strategy.
From RocqSAT.systems Require Basic DPLL_BJ.
From RocqSAT Require Import Model.
From RocqSAT.refinement Require Import Table Lookup Watches Search Propagate Step CStep
  SolverStep.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep Resolve Step.
Import ListNotations.

(* Resolving a conflict keeps the formula. *)
Lemma resolve_formula: forall (pm pm': PA) (f f': CNF) (x x': Ctx),
  resolve pm f x = Some (state pm' f', x') -> f' = f.
Proof.
  intros pm pm' f f' x x'. unfold resolve.
  destruct (split_last_decision pm) as [[m l]|].
  - destruct (saved x); intros H.
    + discriminate.
    + injection H. congruence.
  - intros H. discriminate.
Qed.

(* A step keeps the formula. *)
Lemma step_formula: forall (pm pm': PA) (f f': CNF) (x x': Ctx),
  step (state pm f, x) = Some (state pm' f', x') -> f' = f.
Proof.
  intros pm pm' f f' x x'. cbn [step].
  destruct (check_shorts (shorts x) pm x) as [[m1 x1] [i|]].
  - apply resolve_formula.
  - destruct (propagate (Datatypes.S (nvars x1)) m1 (clear_shorts x1)) as [[m2 x2] [i|]].
    + apply resolve_formula.
    + destruct (_ <? _)%nat.
      * intros H. injection H. congruence.
      * destruct (Nat.eqb (tlen x2) (tlen x)); intros H.
        -- discriminate.
        -- injection H. congruence.
Qed.

(* The invariant of the loop of solve at the state s of the derivation it follows, for
   the formula f: the temporary s holds the solver, s is reached from the initial state
   of f, and the memory represents a context xc consistent with s = state pm f, with the
   decision positions lims. *)
Record SolveInv (S: Shape) (N: nat) (lss: list (list Lit)) (f: CNF) (s: State)
  (le: temp_env) (m1: mem): Prop := {
  vi_s: le ! _s = Some (sptr S);
  vi_reached: state ⟨⟩ f ==>*[DPLL_BJ] s;
  vi_ctx: exists (pm: PA) (xc: Ctx) (lims: list nat),
    s = state pm f /\ StepInv (state pm f) xc /\ LimsOf lims pm /\
    Rep m1 S N lss xc lims;
}.

(* solve runs step until it stops, fails or gives up, following a derivation of DPLL_BJ
   by step_strategy:

     {{ Rep m S N lss x [] /\ StepInv (state ⟨⟩ f) x }}
       while (1) {
     {{ SolveInv (state pm f) }}
         int r = step(s);
     {{ r = -1 (out of room), or r is the outcome of cstep: 0 to stop, 1 for fail, 2
        for the next context }}
         if (r == 0) return 1;
     {{ result = 1: the trail is a model of f, as step stops only at final states }}
         if (r == 1) return 0;
     {{ result = 0: fail is reachable, so f is unsatisfiable }}
         if (r < 0) return 2;
     {{ result = 2: out of room }}
     {{ SolveInv (state pm' f), after a strict derivation }}
       }

   The loop ends: every pass takes a strict derivation step, which is well-founded
   (strict_derivation_well_founded). *)
Theorem solve_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (f: CNF),
  {{ m | Rep m S N lss x [] /\ StepInv (state ⟨⟩ f) x }}
    f_solve(sptr S)
  {{ m', v | (v = vint 1 /\ exists (pm: PA), Model pm f /\ TrailIn m' S N pm) \/
             (v = vint 0 /\ Unsat f) \/
             v = vint 2 }}.
Proof.
  intros S N lss x f m [HRep Hinv].
  pose proof step_strategy as Hstrat.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_solve. cbn [fn_body fn_return].
    apply exec_loop with (R := Basics.flip (clos_trans _ (WellFormedTrans DPLL_BJ)))
      (I := SolveInv S N lss f) (a := state ⟨⟩ f).
    + apply strict_derivation_well_founded.
    + intros s le1 m1 HI.
      destruct HI as [Hs Hder (pm & xc & lims & -> & Hinv1 & Hlims & HRep1)].
      (* int r = step(s); *)
      run. call step_fun. eapply call_weaken.
      { apply (step_correct S N lss xc lims pm f). split.
        - assumption.
        - split.
          + assumption.
          + assumption. }
      intros m2 v Hout. normal. run.
      pose proof (cstep_spec pm f xc lims Hinv1 Hlims) as Hagree.
      destruct Hout as [-> | Hout].
      * (* r = -1: out of room *)
        eapply (exec_if_cmp _ _ _ Ceq _ _ (-1) 0).
        -- ev.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- unfold Small. lia.
        -- unfold Small. lia.
        -- change (zcmp Ceq (-1) 0) with false. cbv beta iota. run.
           eapply (exec_if_cmp _ _ _ Ceq _ _ (-1) 1).
           ++ ev.
           ++ ev.
           ++ reflexivity.
           ++ reflexivity.
           ++ unfold Small. lia.
           ++ unfold Small. lia.
           ++ change (zcmp Ceq (-1) 1) with false. cbv beta iota. run.
              eapply (exec_if_cmp _ _ _ Clt _ _ (-1) 0).
              ** ev.
              ** ev.
              ** reflexivity.
              ** reflexivity.
              ** unfold Small. lia.
              ** unfold Small. lia.
              ** (* return 2; *)
                 change (zcmp Clt (-1) 0) with true. cbv beta iota. eapply exec_return.
                 --- ev.
                 --- ret. exists (vint 2). split.
                     +++ apply result_int.
                     +++ right. now right.
      * destruct (cstep xc lims) as [| |x' lims'] eqn:Hcs;
          cbn [COutcome Agrees] in Hout, Hagree.
        -- (* r = 0: step stops, so the trail is a model; return 1; *)
           destruct Hout as [-> Htrail].
           eapply (exec_if_cmp _ _ _ Ceq _ _ 0 0).
           ++ ev.
           ++ ev.
           ++ reflexivity.
           ++ reflexivity.
           ++ unfold Small. lia.
           ++ unfold Small. lia.
           ++ change (zcmp Ceq 0 0) with true. cbv beta iota. eapply exec_return.
              ** ev.
              ** ret. exists (vint 1). split.
                 --- apply result_int.
                 --- left. split.
                     +++ reflexivity.
                     +++ exists pm. split.
                         *** apply Basic.final_model. destruct Hstrat as (_ & Hnone & _).
                             now apply (Hnone _ xc).
                         *** assumption.
        -- (* r = 1: step reaches fail, so f is unsatisfiable; return 0; *)
           subst v. destruct Hagree as [x' Hb].
           eapply (exec_if_cmp _ _ _ Ceq _ _ 1 0).
           ++ ev.
           ++ ev.
           ++ reflexivity.
           ++ reflexivity.
           ++ unfold Small. lia.
           ++ unfold Small. lia.
           ++ change (zcmp Ceq 1 0) with false. cbv beta iota. run.
              eapply (exec_if_cmp _ _ _ Ceq _ _ 1 1).
              ** ev.
              ** ev.
              ** reflexivity.
              ** reflexivity.
              ** unfold Small. lia.
              ** unfold Small. lia.
              ** change (zcmp Ceq 1 1) with true. cbv beta iota. eapply exec_return.
                 --- ev.
                 --- ret. exists (vint 0). split.
                     +++ apply result_int.
                     +++ right. left. split.
                         *** reflexivity.
                         *** apply DPLL_BJ.final_unsat_refl. split.
                             ---- apply (strategy_trans DPLL_BJ _ _ f (state pm f) fail
                                           xc x' Hstrat Hinv1 Hb Hder).
                             ---- intros [s' Htrans]. inversion Htrans.
        -- (* r = 2: the next context, after a strict derivation; the loop goes on *)
           destruct Hout as [-> HRep2]. destruct Hagree as (pm' & Hb & Hlims').
           eapply (exec_if_cmp _ _ _ Ceq _ _ 2 0).
           ++ ev.
           ++ ev.
           ++ reflexivity.
           ++ reflexivity.
           ++ unfold Small. lia.
           ++ unfold Small. lia.
           ++ change (zcmp Ceq 2 0) with false. cbv beta iota. run.
              eapply (exec_if_cmp _ _ _ Ceq _ _ 2 1).
              ** ev.
              ** ev.
              ** reflexivity.
              ** reflexivity.
              ** unfold Small. lia.
              ** unfold Small. lia.
              ** change (zcmp Ceq 2 1) with false. cbv beta iota. run.
                 eapply (exec_if_cmp _ _ _ Clt _ _ 2 0).
                 --- ev.
                 --- ev.
                 --- reflexivity.
                 --- reflexivity.
                 --- unfold Small. lia.
                 --- unfold Small. lia.
                 --- change (zcmp Clt 2 0) with false. cbv beta iota. apply exec_skip.
                     destruct (strategy_trans DPLL_BJ _ _ f (state pm f) (state pm' f)
                                 xc x' Hstrat Hinv1 Hb Hder) as [Hder' Hinv'].
                     apply loopk_next with (state pm' f).
                     +++ apply strict_derivation_well_formed_trans.
                         *** destruct Hstrat as (_ & _ & Hstep).
                             now apply (Hstep _ _ xc x').
                         *** apply (derivation_well_formed DPLL_BJ ⟨⟩ pm f f Hder).
                             apply initial_well_formed.
                     +++ constructor.
                         *** tmp.
                         *** assumption.
                         *** exists pm', x', lims'. split.
                             ---- reflexivity.
                             ---- split.
                                  ++++ assumption.
                                  ++++ split; assumption.
    + (* The invariant holds at the initial state. *)
      constructor.
      * tmp.
      * apply rt_refl.
      * exists ⟨⟩, x, []. split.
        -- reflexivity.
        -- split.
           ++ assumption.
           ++ split.
              ** reflexivity.
              ** assumption.
Qed.
