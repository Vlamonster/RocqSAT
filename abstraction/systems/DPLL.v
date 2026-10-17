From Stdlib Require Import List.

From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Model.
From RocqSAT Require Import State.
From RocqSAT Require Import Rule.
From RocqSAT Require Import Trans.
From RocqSAT Require Import Satisfiability.
From RocqSAT.rules Require Import Fail.
From RocqSAT.systems Require Basic.

(* The main theorems for DPLL: Fail, Unit, Decide, Backtrack and Pure. *)

Lemma dpll_fail_only: forall (r: Rule) (s: State), In r DPLL -> step r s fail -> FailStep s fail.
Proof.
  intros r s Hr Hstep. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - assumption.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep.
Qed.

(* From every initial state, a final state is reachable: every state is final for Basic, hence for DPLL, or has a Basic step, which is a DPLL step. *)
Theorem final_exists: forall (f: CNF),
  exists (s: State), state ⟨⟩ f ==>* s /\ Final DPLL s.
Proof.
  intros f. apply final_exists_progress. intros [|m f'] _.
  - right. intros [s' Htrans]. inversion Htrans.
  - destruct (final_or_step m f') as [Hfinal|[s' Htrans]].
    + right. now apply final_dpll_basic.
    + left. exists s'. now apply trans_basic_dpll.
Qed.

(* A final state is final for Basic as well, so it is a model. *)
Theorem final_model: forall (m: PA) (f: CNF),
  Final DPLL (state m f) -> Model m f.
Proof. intros m f Hfinal. apply Basic.final_model. now apply final_dpll_basic. Qed.

(* A formula is satisfiable exactly when a final state other than fail is reachable. *)
Theorem final_sat_refl: forall (f: CNF),
  (exists (m: PA), state ⟨⟩ f ==>* state m f /\ Final DPLL (state m f)) <-> Sat f.
Proof.
  intros f. apply (sat_iff_final DPLL).
  - right. right. now left.
  - intros m f' _ _. apply final_model.
Qed.

(* A formula is unsatisfiable exactly when fail is reachable. *)
Theorem final_unsat_refl: forall (f: CNF),
  state ⟨⟩ f ==>* fail /\ Final DPLL fail <-> Unsat f.
Proof.
  intros f. apply (unsat_iff_fail DPLL).
  - apply dpll_fail_only.
  - apply final_exists.
  - intros m f' _ _. apply final_model.
Qed.

Theorem sat_decidable: forall (f: CNF), Sat f \/ Unsat f.
Proof.
  intros f. apply (sat_or_unsat DPLL).
  - apply dpll_fail_only.
  - apply final_exists.
  - intros m f' _ _. apply final_model.
Qed.
