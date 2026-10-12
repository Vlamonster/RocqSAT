From Stdlib Require Import List.

From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Model.
From RocqSAT Require Import State.
From RocqSAT Require Import Rule.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import Entails.
From RocqSAT Require Import Trans.
From RocqSAT Require Import Strategy.
From RocqSAT Require Import Satisfiability.
From RocqSAT.rules Require Import Fail.
From RocqSAT.rules Require Import Unit.
From RocqSAT.rules Require Import Decide.
From RocqSAT.rules Require Import Backtrack.
From RocqSAT.rules Require Import Backjump.
From RocqSAT.rules Require Import Pure.
From RocqSAT.systems Require DPLL.

(* The main theorems for DPLL_BJ: DPLL with Backjump in place of Backtrack. *)

Lemma dpll_bj_fail_only: forall (r: Rule) (s: State), In r DPLL_BJ -> step r s fail -> FailStep s fail.
Proof.
  intros r s Hr Hstep. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - assumption.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep.
Qed.

(* Whenever DPLL_BJ can step, DPLL can: Backtrack applies whenever Backjump does. *)
Lemma trans_dpll_bj_dpll: forall (s s': State), s ==>[DPLL_BJ] s' -> exists (s'': State), s ==> s''.
Proof.
  intros s s' Htrans. inversion Htrans as [r m f s'' Hr Hstep]; subst.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - exists s'. apply (t_step Fail).
    + now left.
    + assumption.
  - exists s'. apply (t_step Unit).
    + right. now left.
    + assumption.
  - exists s'. apply (t_step Decide).
    + right. right. now left.
    + assumption.
  - apply backjump_backtrack in Hstep as [s'' Hstep]. exists s''. apply (t_step Backtrack).
    + right. right. right. now left.
    + assumption.
  - exists s'. apply (t_step Pure).
    + right. right. right. right. now left.
    + assumption.
Qed.

(* From a well-formed entailed state, every DPLL step is a DPLL_BJ step (backtrack_backjump). *)
Lemma trans_dpll_dpll_bj: forall (m: PA) (f: CNF) (s': State),
  WellFormed (state m f) -> Entails f m -> state m f ==> s' -> state m f ==>[DPLL_BJ] s'.
Proof.
  intros m f s' Hwf Hentails Htrans. inversion Htrans as [r ? ? ? Hr Hstep]; subst.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - apply (t_step Fail).
    + now left.
    + assumption.
  - apply (t_step Unit).
    + right. now left.
    + assumption.
  - apply (t_step Decide).
    + right. right. now left.
    + assumption.
  - apply (t_step Backjump).
    + right. right. right. now left.
    + now apply backtrack_backjump.
  - apply (t_step Pure).
    + right. right. right. right. now left.
    + assumption.
Qed.

(* A state that is final for Basic is final for DPLL_BJ. *)
Lemma final_basic_dpll_bj: forall (s: State), Final Basic s -> Final DPLL_BJ s.
Proof.
  intros s Hfinal [s' Htrans]. apply trans_dpll_bj_dpll in Htrans as [s'' Htrans].
  apply Hfinal. now apply trans_dpll_basic in Htrans.
Qed.

(* From every initial state, a final state is reachable: next_state either stops at a final state or takes a DPLL step, which DPLL_BJ can take as well. *)
Theorem final_exists: forall (f: CNF),
  exists (s: State), state ⟨⟩ f ==>*[DPLL_BJ] s /\ Final DPLL_BJ s.
Proof.
  intros f. apply final_exists_progress. intros s Hderivation.
  destruct (next_state s) as [s'|] eqn:Hnext.
  - left. exists s'. destruct s as [|m f'].
    + discriminate.
    + apply trans_dpll_dpll_bj.
      * apply (derivation_well_formed DPLL_BJ ⟨⟩ m f f' Hderivation). apply initial_well_formed.
      * apply (derivation_entails DPLL_BJ ⟨⟩ m f f' Hderivation). constructor.
      * now apply next_state_sound.
  - right. apply final_basic_dpll_bj. destruct next_state_strategy as [_ [Hnone _]]. now apply Hnone.
Qed.

(* A final well-formed entailed state is final for DPLL as well, so it is a model. *)
Theorem final_model: forall (m: PA) (f: CNF),
  WellFormed (state m f) -> Entails f m -> Final DPLL_BJ (state m f) -> Model m f.
Proof.
  intros m f Hwf Hentails Hfinal. apply DPLL.final_model. intros [s' Htrans].
  apply Hfinal. exists s'. now apply trans_dpll_dpll_bj.
Qed.

(* A formula is satisfiable exactly when a final state other than fail is reachable. *)
Theorem final_sat_refl: forall (f: CNF),
  (exists (m: PA), state ⟨⟩ f ==>*[DPLL_BJ] state m f /\ Final DPLL_BJ (state m f)) <-> Sat f.
Proof.
  intros f. apply (sat_iff_final DPLL_BJ).
  - right. right. now left.
  - apply final_model.
Qed.

(* A formula is unsatisfiable exactly when fail is reachable. *)
Theorem final_unsat_refl: forall (f: CNF),
  state ⟨⟩ f ==>*[DPLL_BJ] fail /\ Final DPLL_BJ fail <-> Unsat f.
Proof.
  intros f. apply (unsat_iff_fail DPLL_BJ).
  - apply dpll_bj_fail_only.
  - apply final_exists.
  - apply final_model.
Qed.

Theorem sat_decidable: forall (f: CNF), Sat f \/ Unsat f.
Proof.
  intros f. apply (sat_or_unsat DPLL_BJ).
  - apply dpll_bj_fail_only.
  - apply final_exists.
  - apply final_model.
Qed.
