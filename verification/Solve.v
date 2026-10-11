From Stdlib Require Import Basics.
From Stdlib Require Import List.
From Stdlib Require Import Relations.
Import ListNotations.

From Equations Require Import Equations.

From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import State.
From RocqSAT Require Import Trans.
From RocqSAT Require Import Termination.
From RocqSAT.utils Require Import Inspect.
From RocqSAT Require Import Strategy.

(* Do not assume functional extensionality with Equations. *)
Unset Equations With Funext.

Section Solve.
  Context (f: CNF) {Ctx: Type} {Inv: State -> Ctx -> Prop} {next: State * Ctx -> option (State * Ctx)}
    (Hstrat: Strategy Inv next) {x0: Ctx} (Hx0: Inv (state ⟨⟩ f) x0).

  Instance strict_derivation_well_founded: WellFounded (flip (clos_trans _ (WellFormedTrans DPLL))) := strict_derivation_well_founded DPLL.

  (* Apply the strategy until it stops. This terminates because every step is a strict derivation from a well-formed state (strict_derivation_well_founded). *)
  Equations solve_aux (s: State) (x: Ctx) (H: state ⟨⟩ f ==>* s) (Hinv: Inv s x): State
    by wf s (flip (clos_trans _ (WellFormedTrans DPLL))) :=
  solve_aux s x H Hinv with inspect (next (s, x)) :=
    | Some (s', x') eqn:ns :=
      solve_aux s' x' (proj1 (strategy_trans Inv next f s s' x x' Hstrat Hinv ns H))
        (proj2 (strategy_trans Inv next f s s' x x' Hstrat Hinv ns H))
    | None eqn:ns := s.
  Next Obligation.
    clear solve_aux. apply strict_derivation_well_formed_trans.
    - destruct Hstrat as (_ & _ & Hstep). apply Hstep in ns as [Hplus _].
      + assumption.
      + assumption.
    - destruct s as [|m f'].
      + easy.
      + apply (derivation_well_formed DPLL ⟨⟩ m f f' H). apply initial_well_formed.
  Qed.

  (* Run the strategy from the initial state of f. *)
  Definition solve: State := solve_aux (state ⟨⟩ f) x0 (initial_refl f) Hx0.

  Theorem solve_final_derivation: forall (s s': State) (x: Ctx) (H: state ⟨⟩ f ==>* s) (Hinv: Inv s x),
    solve_aux s x H Hinv = s' -> state ⟨⟩ f ==>* s' /\ Final DPLL s'.
  Proof.
    intros. funelim (solve_aux s x H Hinv).
    - now apply H0.
    - split.
      + assumption.
      + apply final_dpll_basic. destruct Hstrat as (_ & Hnone & _). now apply Hnone with x.
  Qed.
End Solve.
