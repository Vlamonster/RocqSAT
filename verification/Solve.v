From Stdlib Require Import Basics.
From Stdlib Require Import List.
From Stdlib Require Import Relations.
From Stdlib Require Import Arith.
Import ListNotations.

From Equations Require Import Equations.

From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import State.
From RocqSAT Require Import Rule.
From RocqSAT Require Import Trans.
From RocqSAT Require Import Termination.
From RocqSAT.utils Require Import Inspect.
From RocqSAT Require Import Strategy.
From RocqSAT Require Import Schedule.
From RocqSAT.rules Require Import Restart.

(* Do not assume functional extensionality with Equations. *)
Unset Equations With Funext.

Section Solve.
  Context (f: CNF) {rs: list Rule} {Ctx: Type} {Inv: State -> Ctx -> Prop} {next: State * Ctx -> option (State * Ctx)}
    (Hstrat: Strategy rs Inv next) {x0: Ctx} (Hx0: Inv (state ⟨⟩ f) x0).

  Instance strict_derivation_well_founded: WellFounded (flip (clos_trans _ (WellFormedTrans rs))) := strict_derivation_well_founded rs.

  (* Apply the strategy until it stops. This terminates because every step is a strict derivation from a well-formed state (strict_derivation_well_founded). *)
  Equations solve_aux (s: State) (x: Ctx) (H: state ⟨⟩ f ==>*[rs] s) (Hinv: Inv s x): State
    by wf s (flip (clos_trans _ (WellFormedTrans rs))) :=
  solve_aux s x H Hinv with inspect (next (s, x)) :=
    | Some (s', x') eqn:ns :=
      solve_aux s' x' (proj1 (strategy_trans rs Inv next f s s' x x' Hstrat Hinv ns H))
        (proj2 (strategy_trans rs Inv next f s s' x x' Hstrat Hinv ns H))
    | None eqn:ns := s.
  Next Obligation.
    clear solve_aux. apply strict_derivation_well_formed_trans.
    - destruct Hstrat as (_ & _ & Hstep). apply Hstep in ns as [Hplus _].
      + assumption.
      + assumption.
    - destruct s as [|m f'].
      + easy.
      + apply (derivation_well_formed rs ⟨⟩ m f f' H). apply initial_well_formed.
  Qed.

  (* Run the strategy from the initial state of f. *)
  Definition solve: State := solve_aux (state ⟨⟩ f) x0 (initial_refl rs f) Hx0.

  Theorem solve_final_derivation: forall (s s': State) (x: Ctx) (H: state ⟨⟩ f ==>*[rs] s) (Hinv: Inv s x),
    solve_aux s x H Hinv = s' -> state ⟨⟩ f ==>*[rs] s' /\ Final Basic s'.
  Proof.
    intros. funelim (solve_aux s x H Hinv).
    - now apply H0.
    - split.
      + assumption.
      + destruct Hstrat as (_ & Hnone & _). now apply Hnone with x.
  Qed.
End Solve.

(* The same with restarts on the schedule g: before each step, restart if the steps since the last restart reach
   g k for the restarts k so far. *)
Section SolveRestart.
  Context (f: CNF) {rs: list Rule} (g: nat -> nat) (Hunbounded: forall (n: nat), exists (k: nat), n < g k)
    (Hkeep: KeepsFormula rs) {Ctx: Type} {Inv: State -> Ctx -> Prop} {next: State * Ctx -> option (State * Ctx)}
    (Hstrat: Strategy rs Inv next) (restart: PA -> CNF -> Ctx -> Ctx)
    (Hrestart: forall (m: PA) (f': CNF) (x: Ctx), Inv (state m f') x -> Inv (state ⟨⟩ f') (restart m f' x))
    {x0: Ctx} (Hx0: Inv (state ⟨⟩ f) x0).

  (* The steps solve_restart_aux takes. *)
  Lemma restart_scheduled: forall (s: State) (m: PA) (f': CNF) (k c: nat),
    s = state m f' -> g k <= c -> Scheduled rs g (s, k, c) (state ⟨⟩ f', S k, 0).
  Proof.
    intros s m f' k c -> Hle. apply s_restart.
    - assumption.
    - apply r_restart.
  Qed.

  Lemma restart_inv: forall (s: State) (m: PA) (f': CNF) (x: Ctx),
    s = state m f' -> Inv s x -> Inv (state ⟨⟩ f') (restart m f' x).
  Proof. intros s m f' x -> Hinv. now apply Hrestart. Qed.

  Lemma limit_le: forall (lim k c: nat), lim = g k -> lim <= c -> g k <= c.
  Proof. intros lim k c -> Hle. assumption. Qed.

  Lemma next_scheduled: forall (s s': State) (x x': Ctx) (k c: nat),
    Inv s x -> next (s, x) = Some (s', x') -> Scheduled rs g (s, k, c) (s', k, S c).
  Proof.
    intros s s' x x' k c Hinv Hnext. apply s_step. destruct Hstrat as (_ & _ & Hstep).
    now apply (Hstep s s' x x').
  Qed.

  Lemma next_inv: forall (s s': State) (x x': Ctx), Inv s x -> next (s, x) = Some (s', x') -> Inv s' x'.
  Proof.
    intros s s' x x' Hinv Hnext. destruct Hstrat as (_ & _ & Hstep). now apply (Hstep s s' x x').
  Qed.

  (* Apply the strategy until it stops, restarting on the schedule; this terminates by scheduled_terminates. The
     limit lim = g k is computed once per restart. *)
  Fixpoint solve_restart_aux (s: State) (x: Ctx) (k c lim: nat) (Hlim: lim = g k) (Hinv: Inv s x)
    (Hacc: Acc (flip (Scheduled rs g)) (s, k, c)) {struct Hacc}: State :=
  match inspect s with
  | exist _ fail _          => fail
  | exist _ (state m f') Hs =>
    match le_dec lim c with
    | left Hle =>
      solve_restart_aux (state ⟨⟩ f') (restart m f' x) (S k) 0 (g (S k)) eq_refl (restart_inv s m f' x Hs Hinv)
        (Acc_inv Hacc (restart_scheduled s m f' k c Hs (limit_le lim k c Hlim Hle)))
    | right _  =>
      match inspect (next (s, x)) with
      | exist _ (Some (s', x')) Hnext =>
        solve_restart_aux s' x' k (S c) lim Hlim (next_inv s s' x x' Hinv Hnext)
          (Acc_inv Hacc (next_scheduled s s' x x' k c Hinv Hnext))
      | exist _ None _                => s
      end
    end
  end.

  (* Run the strategy with restarts from the initial state of f. *)
  Definition solve_restart: State :=
    solve_restart_aux (state ⟨⟩ f) x0 0 0 (g 0) eq_refl Hx0 (scheduled_terminates rs g (state ⟨⟩ f) 0 Hkeep Hunbounded
      (initial_well_formed f)).

  (* The formula of a state reachable from the initial state is f. *)
  Lemma reachable_formula: forall (m: PA) (f': CNF), state ⟨⟩ f ==>*[rs] state m f' -> f' = f.
  Proof.
    intros m f' Hreach. apply (derivation_invariant rs (fun (_: PA) (g: CNF) => g = f)) with ⟨⟩ m f.
    - intros m1 m2 f1 f2 Htrans <-. symmetry. now apply (trans_same_formula rs m1 m2 f1 f2).
    - assumption.
    - reflexivity.
  Qed.

  (* The result is reachable without restarts (the restarts lead back to the initial state) and final. *)
  Lemma solve_restart_aux_final: forall (p: State * nat * nat), Acc (flip (Scheduled rs g)) p ->
    forall (s: State) (x: Ctx) (k c lim: nat) (Hlim: lim = g k) (Hinv: Inv s x)
      (Hacc: Acc (flip (Scheduled rs g)) (s, k, c)),
    p = (s, k, c) ->
    state ⟨⟩ f ==>*[rs] s ->
    state ⟨⟩ f ==>*[rs] solve_restart_aux s x k c lim Hlim Hinv Hacc /\
    Final Basic (solve_restart_aux s x k c lim Hlim Hinv Hacc).
  Proof.
    intros p Hp. induction Hp as [p _ IH]. intros s x k c lim Hlim Hinv Hacc -> Hreach. destruct Hacc as [Hacc].
    cbn [solve_restart_aux]. destruct (inspect s) as [[|m f'] Hs]; subst s.
    - split.
      + assumption.
      + intros [s' Htrans]. inversion Htrans.
    - destruct (le_dec lim c) as [Hle|Hle].
      (* Restart *)
      + apply (IH (state ⟨⟩ f', S k, 0)).
        * apply (restart_scheduled (state m f') m f').
          -- reflexivity.
          -- now subst lim.
        * reflexivity.
        * apply reachable_formula in Hreach as ->. apply rt_refl.
      + destruct (inspect (next (state m f', x))) as [[[s' x']|] Hnext].
        (* Step *)
        * apply (IH (s', k, S c)).
          -- now apply (next_scheduled (state m f') s' x x').
          -- reflexivity.
          -- destruct Hstrat as (_ & _ & Hstep). apply rt_trans with (state m f').
             ++ assumption.
             ++ apply clos_t_clos_rt. now apply (Hstep (state m f') s' x x').
        (* Final *)
        * split.
          -- assumption.
          -- destruct Hstrat as (_ & Hnone & _). now apply (Hnone (state m f') x).
  Qed.

  Theorem solve_restart_final: state ⟨⟩ f ==>*[rs] solve_restart /\ Final Basic solve_restart.
  Proof.
    unfold solve_restart. apply (solve_restart_aux_final (state ⟨⟩ f, 0, 0)).
    - apply scheduled_terminates.
      + assumption.
      + assumption.
      + apply initial_well_formed.
    - reflexivity.
    - apply rt_refl.
  Qed.
End SolveRestart.
