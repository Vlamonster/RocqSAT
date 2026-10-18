(* solve runs the solver to the end: it terminates, and answers whether the formula is
   satisfiable, unless it gives up. *)
From Stdlib Require Import List.
From Stdlib Require Import Relations.
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
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import Model.
From RocqSAT Require Import State.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import Trans.
From RocqSAT Require Import Termination.
From RocqSAT Require Import Satisfiability.
From RocqSAT Require Import Strategy.
From RocqSAT.systems Require Basic.
From RocqSAT.systems Require DPLL_BJ.
From RocqSAT.refinement Require Import Table.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Search.
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
From RocqSAT.refinement.c Require Import Resolve.
From RocqSAT.refinement.c Require Import Step.

(* The invariant of the loop of solve at the state s of the derivation it follows, for
   the formula f: the temporary s holds the solver, s is reached from the initial state
   of f, and the memory represents a context xc with s = state (trail xc) f. *)
Record SolveInv {sh: Shape} {N: nat} {lss: list (list Lit)} {f: CNF} {s: State}
  {le: temp_env} {m1: mem}: Prop := {
  sv_s: le ! _s = Some (sptr sh);
  sv_reached: state ⟨⟩ f ==>*[DPLL_BJ] s;
  sv_ctx: exists (xc: Ctx),
    s = state (trail xc) f /\ StepInv s xc /\ Rep m1 sh N lss xc;
}.
Arguments SolveInv : clear implicits.

(* solve runs step until it stops, fails or gives up, following a derivation of DPLL_BJ
   by cstep_spec:

     {{ Rep m sh N lss x /\ StepInv (state ⟨⟩ f) x }}
       while (1) {
     {{ SolveInv (state (trail xc) f) }}
         int r = step(s);
     {{ r = -1 (out of room), or r is the outcome of cstep: 0 to stop, 1 for fail, 2
        for the next context }}
         if (r == 0) return 1;
     {{ result = 1: the trail is a model of f, as step stops only at final states }}
         if (r == 1) return 0;
     {{ result = 0: fail is reachable, so f is unsatisfiable }}
         if (r < 0) return 2;
     {{ result = 2: out of room }}
     {{ SolveInv (state (trail xc') f), after a strict derivation }}
       }

   The loop ends: every pass takes a strict derivation step, which is well-founded
   (strict_derivation_well_founded). *)
Theorem solve_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (f: CNF),
  {{ m | Rep m sh N lss x /\ StepInv (state ⟨⟩ f) x }}
    f_solve(sptr sh)
  {{ m', v | (v = vint 1 /\ exists (pm: PA), Model pm f /\ TrailIn m' sh N pm) \/
             (v = vint 0 /\ Unsat f) \/
             v = vint 2 }}.
Proof.
  intros sh N lss x f m [HRep Hinv].
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_solve. cbn [fn_body fn_return].
    apply exec_loop with (R := Basics.flip (clos_trans _ (WellFormedTrans DPLL_BJ)))
      (I := SolveInv sh N lss f) (a := state ⟨⟩ f).
    + apply strict_derivation_well_founded.
    + intros s le1 m1 HI.
      destruct HI as [Hs Hder (xc & -> & Hinv1 & HRep1)].
      (* int r = step(s); *)
      run. call step_fun (step_correct sh N lss xc f) by (split; assumption).
      intros m2 v Hout. normal. run.
      pose proof (cstep_spec (trail xc) f xc Hinv1) as Hok.
      destruct Hout as [-> | Hout].
      * (* r = -1: out of room *)
        branch (-1) 0.
        -- intros Heq. lia.
        -- intros _. run. take_else (-1) 1 by lia.
           intros _. run. take_then (-1) 0 by lia.
           (* return 2; *)
           intros _. return_int.
           right. now right.
      * destruct (cstep xc) as [| |x'] eqn:Hcs;
          cbn [COutcome StepOk] in Hout, Hok.
        -- (* r = 0: step stops, so the trail is a model; return 1; *)
           destruct Hout as [-> Htrail].
           take_then 0 0 by lia.
           intros _. return_int.
           left. split.
           ++ reflexivity.
           ++ exists (trail xc). split.
              ** now apply Basic.final_model.
              ** assumption.
        -- (* r = 1: step reaches fail, so f is unsatisfiable; return 0; *)
           subst v.
           take_else 1 0 by lia.
           intros _. run. take_then 1 1 by lia.
           intros _. return_int.
           right. left. split.
           ++ reflexivity.
           ++ apply DPLL_BJ.final_unsat_refl. split.
              ** apply rt_trans with (state (trail xc) f).
                 --- assumption.
                 --- now apply clos_t_clos_rt.
              ** intros [s' Htrans]. inversion Htrans.
        -- (* r = 2: the next context, after a strict derivation; the loop goes on *)
           destruct Hout as [-> HRep2]. destruct Hok as [Hplus Hinv'].
           take_else 2 0 by lia.
           intros _. run. take_else 2 1 by lia.
           intros _. run. take_else 2 0 by lia.
           intros _. apply exec_skip.
           apply loopk_next with (state (trail x') f).
           ++ apply strict_derivation_well_formed_trans.
              ** assumption.
              ** apply (derivation_well_formed DPLL_BJ ⟨⟩ _ f f Hder).
                 apply initial_well_formed.
           ++ constructor.
              ** tmp.
              ** apply rt_trans with (state (trail xc) f).
                 --- assumption.
                 --- now apply clos_t_clos_rt.
              ** exists x'. split.
                 --- reflexivity.
                 --- split; assumption.
    + (* The invariant holds at the initial state. *)
      constructor.
      * tmp.
      * apply rt_refl.
      * exists x. split.
        -- (* the initial trail is the trail of x *)
           rewrite <- (@step_core_trail ⟨⟩ f x).
           ++ reflexivity.
           ++ apply Hinv.
        -- split; assumption.
Qed.
