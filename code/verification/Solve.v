From Stdlib Require Import Basics.
From Stdlib Require Import List.
From Stdlib Require Import Relations.
Import ListNotations.

From Equations Require Import Equations.

From RocqSAT Require Import CNF.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import State.
From RocqSAT Require Import Trans.
From RocqSAT Require Import Termination.
From RocqSAT.utils Require Import Inspect.
From RocqSAT Require Import Strategy.

(* Do not assume functional extensionality with Equations. *)
Unset Equations With Funext.

Section Solve.
  Context (f: CNF) (next: State -> option State) (Hstrat: Strategy next).

  Instance strict_derivation_well_founded: WellFounded (flip (clos_trans _ (WellFormedTrans DPLL))) := strict_derivation_well_founded DPLL dpll_keeps_formula.

  (* Apply the strategy until it stops. This terminates because every step is a strict derivation from a well-formed state (strict_derivation_well_founded). *)
  Equations solve_aux (s: State) (H: state [] f ==>* s): State by wf s (flip (clos_trans _ (WellFormedTrans DPLL))) :=
  solve_aux s H with inspect (next s) :=
    | Some s' eqn:ns := solve_aux s' (strategy_trans f s s' next Hstrat ns H)
    | None    eqn:ns := s.
  Next Obligation.
    clear solve_aux. apply strict_derivation_well_formed_trans.
    - now apply Hstrat in ns.
    - destruct s as [|m f'].
      + easy.
      + apply (derivation_well_formed DPLL [] m f f' H). apply initial_well_formed.
  Qed.

  (* Run the strategy from the initial state of f. *)
  Definition solve: State := solve_aux (state [] f) (initial_refl f).

  Theorem solve_final_derivation: forall (s s': State) (H: state [] f ==>* s),
    solve_aux s H = s' -> state [] f ==>* s' /\ Final DPLL s'.
  Proof. 
    intros. funelim (solve_aux s H).
    - now apply H0.
    - split.
      + assumption.
      + apply final_dpll_basic. now apply Hstrat.
  Qed.
End Solve.
