From Stdlib Require Import Basics.
From Stdlib Require Import List.
Import ListNotations.

From Equations Require Import Equations.

From RocqSAT Require Import CNF.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import Trans.
From RocqSAT Require Import Termination.
From RocqSAT.utils Require Import Inspect.
From RocqSAT Require Import Strategy.

(* Do not assume functional extensionality with Equations. *)
Unset Equations With Funext.

Section Solve.
  Context (f: CNF) (next: State -> option State) (Hstrat: Strategy next).

  Instance strict_derivation_well_founded: WellFounded (flip (DerivationStrict DPLL)) := strict_derivation_well_founded.

  (* Apply the strategy until it stops. This terminates because every step is a strict derivation (strict_derivation_well_founded). *)
  Equations solve_aux (s: State) (H: state [] f (initial_well_formed f) ==>* s): State by wf s (flip (DerivationStrict DPLL)) :=
  solve_aux s H with inspect (next s) :=
    | Some s' eqn:ns := solve_aux s' (strategy_trans f s s' next Hstrat ns H)
    | None    eqn:ns := s.
  Next Obligation. clear solve_aux. now apply Hstrat in ns. Qed.

  (* Run the strategy from the initial state of f. *)
  Definition solve: State := solve_aux (state [] f (initial_well_formed f)) (initial_refl f).

  Theorem solve_final_derivation: forall (s s': State) (H: state [] f (initial_well_formed f) ==>* s),
    solve_aux s H = s' -> state [] f (initial_well_formed f) ==>* s' /\ Final DPLL s'.
  Proof. 
    intros. funelim (solve_aux s H).
    - now apply H0.
    - split.
      + assumption.
      + apply final_dpll_basic. now apply Hstrat.
  Qed.
End Solve.
