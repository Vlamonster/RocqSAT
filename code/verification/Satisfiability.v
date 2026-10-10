From Stdlib Require Import List.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import Model.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import Trans.
From RocqSAT Require Import Solve.
From RocqSAT Require Import Strategy.
From RocqSAT Require Import Normalization.
From RocqSAT.entailment Require Import Entails.
From RocqSAT.entailment Require Import Properties.
From RocqSAT.entailment Require Import Preservation.
From RocqSAT.rules Require Import Fail.
From RocqSAT.rules Require Import Unit.
From RocqSAT.rules Require Import Decide.
From RocqSAT.rules Require Import Backtrack.
From RocqSAT.rules Require Import Pure.

(* m assigns a value to every literal occurring in f. *)
Definition Total (m: PA) (f: CNF): Prop := forall (l: Lit) (c: Clause), Clause.In l c -> CNF.In c f -> Def m l.

Definition Sat (f: CNF): Prop := exists (m: PA), Model m f.
Definition Unsat (f: CNF): Prop := ~ Sat f.

Theorem final_exists: forall (f: CNF),
  exists (s: State), state [] f (initial_well_formed f) ==>* s /\ Final DPLL s.
Proof.
  intros. destruct (solve f next_state next_state_strategy) as [|m' f' Hwf'] eqn:H.
  - exists fail. now apply solve_final_derivation in H.
  - exists (state m' f' Hwf'). now apply solve_final_derivation in H.
Qed.

Theorem final_model: forall (m: PA) (f: CNF) (Hwf: WellFormed m f),
  Final DPLL (state m f Hwf) -> Model m f.
Proof.
  unfold Model. unfold Final. unfold not. intros. destruct (f_eval m f) eqn:Heq.
  - destruct b.
    + reflexivity.
    + exfalso. apply H. apply f_eval_false_iff in Heq as [c [Hc_in_f Hconflict]].
      destruct (proj2 (find_conflict_exists_iff m f)) as [c_conflict Hfind_conflict]. now exists c.
      destruct (split_last_decision m) as [[m_split l_split]|] eqn:Hsplit.
      (* t_backtrack *)
      * exists (state (m_split ++p (¬l_split)) f (backtrack_well_formed m m_split f l_split Hsplit Hwf)).
        pose proof (split_decomp m m_split l_split Hsplit) as [n_split [-> Hno_dec]].
        apply (t_backtrack m_split n_split f c_conflict l_split Hwf).
        -- right. right. right. now left.
        -- now apply find_conflict_c_in_f in Hfind_conflict.
        -- now apply find_conflict_conflicting in Hfind_conflict.
        -- assumption.
      (* t_fail *)
      * exists fail. apply (t_fail m f c_conflict).
        -- now left.
        -- now apply find_conflict_c_in_f in Hfind_conflict.
        -- now apply find_conflict_conflicting in Hfind_conflict.
        -- now apply split_none_iff.
  (* t_decide *)
  - exfalso. apply H. apply undef_decision_exists in Heq as [l_decide Hfind_dec].
    exists (state (m ++d l_decide) f (decide_well_formed _ _ _ Hfind_dec Hwf)).
    pose proof (find_decision_decomp m f l_decide Hfind_dec) as [c_decide [Hfind_undef_l Hc_in_f]].
    eapply (t_decide m f c_decide l_decide).
    + right. right. now left.
    + left. now apply find_undef_l_in_c in Hfind_undef_l.
    + assumption.
    + now apply find_undef_l_undef in Hfind_undef_l.
Qed.

(* A formula is satisfiable exactly when a final state other than fail is reachable. *)
Theorem final_sat_refl: forall (f: CNF),
  (exists (m: PA) (Hwf: WellFormed m f),
    state [] f (initial_well_formed f) ==>* state m f Hwf /\ Final DPLL (state m f Hwf)) <-> Sat f.
Proof.
  intros. split.
  - intros [m [Hwf [Htrans Hfinal]]]. exists m. now apply final_model in Hfinal.
  - intros Hsat. unfold Sat in Hsat. unfold Model in Hsat. destruct Hsat as [m Heq].
    remember (normalize m f) as m' eqn:H.
    pose proof (normalize_only_dec m f) as Honly_dec.
    pose proof (normalize_all_def m f) as Hall_def.
    pose proof (normalize_derivation m f) as Htrans.
    apply normalize_f in Heq.
    rewrite <- H in *. clear H. clear m.
    destruct Htrans as [Hwf Htrans'].
    exists m', Hwf. split.
    + assumption.
    + unfold Final. unfold not. intros [s Htrans]. apply trans_union in Htrans as [r [Hr Htrans]].
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]].
      * apply (fail_model_final m' f Hwf Heq Hall_def). now exists s.
      * apply (unit_model_final m' f Hwf Heq Hall_def). now exists s.
      * apply (decide_model_final m' f Hwf Heq Hall_def). now exists s.
      * apply (backtrack_model_final m' f Hwf Heq Hall_def). now exists s.
      * apply (pure_model_final m' f Hwf Heq Hall_def). now exists s.
Qed.

(* A formula is unsatisfiable exactly when fail is reachable. *)
Theorem final_unsat_refl: forall (f: CNF),
  state [] f (initial_well_formed f) ==>* fail /\ Final DPLL fail <-> Unsat f.
Proof.
  intros. split.
  - intros [Hderivation _]. apply fail_predecessor in Hderivation as [m [Hwf [Hderivation Htrans]]].
    inversion Htrans as [? ? c ? _ Hc_in_f Hconflict Hno_dec | | | |]; subst.
    apply derivation_entails in Hderivation.
    + unfold Unsat. unfold Sat. unfold Model. unfold not. intros [m' Hsat].
      destruct (entails_extend f [] m m') as [m'' Hm''].
      * now rewrite app_nil_r.
      * assumption.
      * apply model_union_iff. split.
        -- assumption.
        -- apply model_units_iff. intros l a [].
      * apply model_union_iff in Hm'' as [Hf Htrail]. rewrite app_nil_r in Htrail.
        unfold Model in Hf. rewrite f_eval_true_iff in Hf. apply Hf in Hc_in_f.
        apply (units_transfer_c m'' _ _ Htrail) in Hconflict. congruence.
    + constructor.
  - intros.
    pose proof (final_sat_refl f) as Hsat_refl. 
    apply not_iff_compat in Hsat_refl as [_ Hsat_refl_complete].
    apply Hsat_refl_complete in H. clear Hsat_refl_complete.
    pose proof (final_exists f) as [s [Hderivation Hfinal]].
    destruct s.
    + intuition.
    + exfalso. apply H. apply derivation_same_formula in Hderivation as Heq.
      subst f0. now exists m, Hwf.
Qed.

Theorem sat_decidable: forall (f: CNF), Sat f \/ Unsat f.
Proof.
  intros. destruct (final_exists f) as [[|m f' Hwf] ].
  - right. now apply final_unsat_refl.
  - left. destruct H. assert (f = f').
    + now apply (derivation_same_formula [] m f f' (initial_well_formed f) Hwf).
    + subst f'. apply final_sat_refl. now exists m, Hwf.
Qed.
