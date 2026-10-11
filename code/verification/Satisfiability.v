From Stdlib Require Import List.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import Model.
From RocqSAT Require Import State.
From RocqSAT Require Import Entails.
From RocqSAT Require Import Rule.
From RocqSAT Require Import Trans.
From RocqSAT Require Import Strategy.
From RocqSAT Require Import Normalization.
From RocqSAT Require Import Solve.
From RocqSAT.rules Require Import Fail.
From RocqSAT.rules Require Import Decide.
From RocqSAT.rules Require Import Backtrack.

(* m assigns a value to every literal occurring in f. *)
Definition Total (m: PA) (f: CNF): Prop := forall (l: Lit) (c: Clause), Clause.In l c -> CNF.In c f -> Def m l.

Definition Sat (f: CNF): Prop := exists (m: PA), Model m f.
Definition Unsat (f: CNF): Prop := ~ Sat f.

Theorem final_exists: forall (f: CNF),
  exists (s: State), state ⟨⟩ f ==>* s /\ Final DPLL s.
Proof.
  intros. destruct (solve f next_state next_state_strategy) as [|m' f'] eqn:H.
  - exists fail. now apply solve_final_derivation in H.
  - exists (state m' f'). now apply solve_final_derivation in H.
Qed.

Theorem final_model: forall (m: PA) (f: CNF),
  Final DPLL (state m f) -> Model m f.
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
        apply split_last_decision_some_iff in Hdecomp as [n_split [-> Hno_dec]].
        apply (t_step Backtrack).
        -- right. right. right. now left.
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
          ++ now apply split_last_decision_none_iff.
  (* Decide *)
  - exfalso. apply H. apply undef_decision_exists in Heq as [l_decide Hfind_dec].
    exists (state ⟨m; l_decide⟩ f).
    pose proof (find_decision_decomp m f l_decide Hfind_dec) as [c_decide [Hfind_undef_l Hc_in_f]].
    apply (t_step Decide).
    + right. right. now left.
    + apply (r_decide m f c_decide l_decide).
      * left. now apply find_undef_l_in_c in Hfind_undef_l.
      * assumption.
      * now apply find_undef_l_undef in Hfind_undef_l.
Qed.

(* A formula is satisfiable exactly when a final state other than fail is reachable. *)
Theorem final_sat_refl: forall (f: CNF),
  (exists (m: PA), state ⟨⟩ f ==>* state m f /\ Final DPLL (state m f)) <-> Sat f.
Proof.
  intros. split.
  - intros [m [Htrans Hfinal]]. exists m. now apply final_model in Hfinal.
  - intros Hsat. unfold Sat in Hsat. unfold Model in Hsat. destruct Hsat as [m Heq].
    remember (normalize m f) as m' eqn:H.
    pose proof (normalize_only_dec m f) as Honly_dec.
    pose proof (normalize_all_def m f) as Hall_def.
    pose proof (normalize_derivation m f) as Hderivation.
    apply normalize_f in Heq.
    rewrite <- H in *. clear H. clear m.
    exists m'. split.
    + assumption.
    + unfold Final. unfold not. intros [s Htrans].
      apply trans_rule in Htrans as [r [_ Hstep]].
      apply (rule_model_final r m' f Heq Hall_def). now exists s.
Qed.

(* A formula is unsatisfiable exactly when fail is reachable. *)
Theorem final_unsat_refl: forall (f: CNF),
  state ⟨⟩ f ==>* fail /\ Final DPLL fail <-> Unsat f.
Proof.
  intros. split.
  - intros [Hderivation _]. apply fail_predecessor in Hderivation as [m [f' [Hderivation Htrans]]].
    apply trans_rule in Htrans as [r [Hr Hstep]].
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; inversion Hstep as [? ? c Hc_in_f Hconflict Hno_dec]; subst.
    pose proof Hderivation as Hequivalent. apply derivation_equivalent in Hequivalent as [Hff' _].
    apply derivation_entails in Hderivation.
    + unfold Unsat. unfold Sat. unfold not. intros [m' Hsat]. apply Hff' in Hsat.
      destruct (entails_extend f' ⟨⟩ m m') as [m'' Hm''].
      * now rewrite extend_empty_l.
      * assumption.
      * apply model_union_iff. split.
        -- assumption.
        -- apply model_units_iff. intros l a [].
      * apply model_union_iff in Hm'' as [Hf Htrail]. rewrite extend_empty_l in Htrail.
        unfold Model in Hf. rewrite f_eval_true_iff in Hf. apply Hf in Hc_in_f.
        apply (units_transfer_c m'' _ _ Htrail) in Hconflict. congruence.
    + constructor.
  - intros Hunsat. destruct (final_exists f) as [[|m f'] [Hderivation Hfinal]].
    + now split.
    + exfalso. apply Hunsat. exists m. apply final_model in Hfinal.
      apply derivation_equivalent in Hderivation as [_ Hf'f].
      now apply Hf'f.
Qed.

Theorem sat_decidable: forall (f: CNF), Sat f \/ Unsat f.
Proof.
  intros. destruct (final_exists f) as [[|m f'] [Hderivation Hfinal]].
  - right. now apply final_unsat_refl.
  - left. exists m. apply final_model in Hfinal.
    apply derivation_equivalent in Hderivation as [_ Hf'f].
    now apply Hf'f.
Qed.
