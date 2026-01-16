From Equations Require Import Equations.
From Stdlib Require Import List Relations.
Import ListNotations.
From RocqSAT Require Import CNF Trans Termination Inspect Strategy.

(* Do not assume functional extensionality with Equations. *)
Unset Equations With Funext.

Section Solve.
  Context (f: CNF). 

  Instance wf_state_lt_f: WellFounded (StateLt f) := wf_state_lt f.

  Equations solve_aux (s: State) (H: state [] f (initial_wf f) ==>* s): State by wf s (StateLt f) :=
  solve_aux s H with inspect (next_state s) :=
    | Some s' eqn:ns := solve_aux s' (next_state_trans f s s' ns H)
    | None    eqn:ns := s.
  Next Obligation. 
    clear solve_aux. destruct s.
    - inversion ns.
    - destruct (next_state_options m f0 Hwf) as [G|[G|G]].
      + congruence.
      + rewrite ns in G. injection G as ->. now constructor.
      + rewrite ns in G. destruct G. destruct H0. injection H0 as ->.
        apply next_state_sound in ns. assert (state [] f (initial_wf f) ==>* state x f0 x0).
        * eapply rt_trans.
          -- apply H.
          -- now apply rt_step.
        * apply trans_clos_same_formula in H0. subst f0. now apply trans__state_lt.
  Qed.

  Definition solve: State := solve_aux (state [] f (initial_wf f)) (initial_refl f).
End Solve.

Lemma solve_aux_trans: forall (f: CNF) (s s': State) (H: state [] f (initial_wf f) ==>* s),
  solve_aux f s H = s' -> state [] f (initial_wf f) ==>* s'.
Proof.
  intros. funelim (solve_aux f s H).
  - now apply H0.
  - assumption.
Qed.

Lemma solve_aux_final: forall (f: CNF) (s s': State) (H: state [] f (initial_wf f) ==>* s),
  solve_aux f s H = s' -> Final s'.
Proof.
  intros. apply next_state_final_refl. funelim (solve_aux f s H).
  - now apply H0.
  - assumption.
Qed.
