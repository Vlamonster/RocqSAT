From Stdlib Require Import List.

From RocqSAT Require Import Lit.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import Model.
From RocqSAT Require Import State.
From RocqSAT Require Import Rule.
From RocqSAT Require Import Trans.
From RocqSAT Require Import Strategy.
From RocqSAT Require Import Satisfiability.
From RocqSAT.rules Require Import Fail.
From RocqSAT.rules Require Import Decide.
From RocqSAT.rules Require Import Backtrack.

(* The main theorems for Basic: Fail, Decide and Backtrack. *)

Lemma basic_fail_only: forall (r: Rule) (s: State), In r Basic -> step r s fail -> FailStep s fail.
Proof.
  intros r s Hr Hstep. destruct Hr as [<-|[<-|[<-|[]]]].
  - assumption.
  - inversion Hstep.
  - inversion Hstep.
Qed.

(* From every initial state, a final state is reachable: next_state either stops at a final state or finds a step, which Basic can take as well. *)
Theorem final_exists: forall (f: CNF),
  exists (s: State), state ⟨⟩ f ==>*[Basic] s /\ Final Basic s.
Proof.
  intros f. apply final_exists_progress. intros s _.
  destruct (next_state s) as [s'|] eqn:Hnext.
  - left. apply next_state_sound in Hnext. now apply trans_dpll_basic in Hnext.
  - right. destruct next_state_strategy as [_ [Hnone _]]. now apply Hnone.
Qed.

(* A final state is a model: otherwise there is a conflict, so Fail or Backtrack applies, or an undefined literal, so Decide applies. *)
Theorem final_model: forall (m: PA) (f: CNF),
  Final Basic (state m f) -> Model m f.
Proof.
  unfold Model. unfold Final. unfold not. intros. destruct (f_eval m f) eqn:Heq.
  - destruct b.
    + reflexivity.
    + exfalso. apply H. apply f_eval_false_iff in Heq as [c [Hc_in_f Hconflict]].
      destruct (proj2 (find_conflict_exists_iff m f)) as [c_conflict Hfind_conflict]. now exists c.
      destruct (split_last_decision m) as [[m_split l_split]|] eqn:Hsplit.
      (* Backtrack *)
      * exists (state ⟨m_split, (¬l_split)⟩ f).
        pose proof Hsplit as Hdecomp.
        apply PA.split_last_decision_some_iff in Hdecomp as [n_split [-> Hno_dec]].
        apply (t_step Backtrack).
        -- right. right. now left.
        -- apply (r_backtrack m_split n_split f c_conflict l_split).
          ++ now apply find_conflict_c_in_f in Hfind_conflict.
          ++ now apply find_conflict_conflicting in Hfind_conflict.
          ++ assumption.
      (* Fail *)
      * exists fail. apply (t_step Fail).
        -- now left.
        -- apply (r_fail m f c_conflict).
          ++ now apply find_conflict_c_in_f in Hfind_conflict.
          ++ now apply find_conflict_conflicting in Hfind_conflict.
          ++ now apply PA.split_last_decision_none_iff.
  (* Decide *)
  - exfalso. apply H. apply undef_decision_exists in Heq as [l_decide Hfind_dec].
    exists (state ⟨m; l_decide⟩ f).
    pose proof (find_decision_decomp m f l_decide Hfind_dec) as [c_decide [Hfind_undef_l Hc_in_f]].
    apply (t_step Decide).
    + right. now left.
    + apply r_decide.
      * left. exists c_decide. split.
        -- now apply find_undef_l_in_c in Hfind_undef_l.
        -- assumption.
      * now apply find_undef_l_undef in Hfind_undef_l.
Qed.

(* A formula is satisfiable exactly when a final state other than fail is reachable. *)
Theorem final_sat_refl: forall (f: CNF),
  (exists (m: PA), state ⟨⟩ f ==>*[Basic] state m f /\ Final Basic (state m f)) <-> Sat f.
Proof.
  intros f. apply (sat_iff_final Basic).
  - right. now left.
  - intros m f' _ _. apply final_model.
Qed.

(* A formula is unsatisfiable exactly when fail is reachable. *)
Theorem final_unsat_refl: forall (f: CNF),
  state ⟨⟩ f ==>*[Basic] fail /\ Final Basic fail <-> Unsat f.
Proof.
  intros f. apply (unsat_iff_fail Basic).
  - apply basic_fail_only.
  - apply final_exists.
  - intros m f' _ _. apply final_model.
Qed.

Theorem sat_decidable: forall (f: CNF), Sat f \/ Unsat f.
Proof.
  intros f. apply (sat_or_unsat Basic).
  - apply basic_fail_only.
  - apply final_exists.
  - intros m f' _ _. apply final_model.
Qed.
