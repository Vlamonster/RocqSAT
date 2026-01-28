From Equations Require Import Equations.
From Stdlib Require Import List Relations.
Import ListNotations.
From RocqSAT Require Import CNF Evaluation WellFormed Trans Termination Inspect Strategy.

(* Do not assume functional extensionality with Equations. *)
Unset Equations With Funext.

Section Solve.
  Context (f: CNF) (next: State -> option State) (Hstrat: Strategy next).

  Instance wf_state_lt_f: WellFounded (StateLtTransClos f) := wf_state_lt_trans_clos f.

  Equations solve_aux (s: State) (H: state [] f (initial_wf f) ==>* s): State by wf s (StateLtTransClos f) :=
  solve_aux s H with inspect (next s) :=
    | Some s' eqn:ns := solve_aux s' (strategy_trans f s s' next Hstrat ns H)
    | None    eqn:ns := s.
  Next Obligation. 
    clear solve_aux. destruct s.
    - assert (next fail = None) by apply Hstrat. congruence.
    - apply derivation_same_formula in H as Heq. subst f0.
      apply derivation_strict__state_lt_trans_clos.
      now apply Hstrat in ns.
  Qed.

  Definition solve: State := solve_aux (state [] f (initial_wf f)) (initial_refl f).

  Theorem solve_final_derivation: forall (s s': State) (H: state [] f (initial_wf f) ==>* s),
    solve_aux s H = s' -> state [] f (initial_wf f) ==>* s' /\ Final s'.
  Proof. 
    intros. funelim (solve_aux s H).
    - now apply H0.
    - split.
      + assumption.
      + apply final__final_b. now apply Hstrat.
  Qed.
End Solve.
