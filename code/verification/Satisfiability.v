From Stdlib Require Import List.
From Stdlib Require Import Relations.

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
From RocqSAT.refinement Require Import Search.
From RocqSAT Require Import Normalization.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import Termination.
From RocqSAT.rules Require Import Fail.
From RocqSAT.rules Require Import Decide.
From RocqSAT.rules Require Import Backtrack.

(* m assigns a value to every literal occurring in f. *)
Definition Total (m: PA) (f: CNF): Prop := forall (l: Lit), l ∈ f -> Def m l.

Definition Sat (f: CNF): Prop := exists (m: PA), Model m f.
Definition Unsat (f: CNF): Prop := ~ Sat f.

(* Every state is final for Basic, or a Basic step is possible from it. *)
Lemma final_or_step: forall (m: PA) (f: CNF), Final Basic (state m f) \/ exists (s': State), state m f ==>[Basic] s'.
Proof.
  intros m f.
  assert (Hcompat_false: forall (c1 c2: Clause), Clause.Equal c1 c2 -> c_false m c1 = c_false m c2).
  - intros c1 c2 Heq. unfold c_false, c_eval.
    rewrite (Clause.c_equal_exists _ c1 c2 Heq). now rewrite (Clause.c_equal_forall _ c1 c2 Heq).
  - destruct (CNF.exists_ (c_false m) f) eqn:Hconflict.
    (* A false clause: Fail or Backtrack *)
    + right. apply CNF.exists_spec in Hconflict as [c [Hc_in_f Hc]].
      * assert (Hc_false: c_eval m c = Some false).
        -- unfold c_false in Hc. destruct (c_eval m c) as [[|]|]; easy.
        -- destruct (split_last_decision m) as [[m' l]|] eqn:Hsplit.
          ++ apply PA.split_last_decision_some_iff in Hsplit as [n [-> Hno_dec]].
             exists (state ⟨m', (¬l)⟩ f). apply (t_step Backtrack).
            ** right. right. now left.
            ** now apply (r_backtrack m' n f c l).
          ++ exists fail. apply (t_step Fail).
            ** now left.
            ** apply (r_fail m f c).
              --- assumption.
              --- assumption.
              --- now apply PA.split_last_decision_none_iff.
      * intros c1 c2 Heq. now apply Hcompat_false.
    + destruct (CNF.exists_ (fun (c: Clause) => Clause.exists_ (l_undef m) c) f) eqn:Hundef.
      (* An unassigned literal: Decide *)
      * right. apply CNF.exists_spec in Hundef as [c [Hc_in_f Hc]].
        -- apply Clause.exists_spec in Hc as [l [Hl_in_c Hl]].
          ++ exists (state ⟨m; l⟩ f). apply (t_step Decide).
            ** right. now left.
            ** apply r_decide.
              --- left. now exists c.
              --- unfold l_undef in Hl. unfold Undef. destruct (l_eval m l); easy.
          ++ now intros ? ? ->.
        -- intros c1 c2 Heq. now apply Clause.c_equal_exists.
      (* Neither: no rule of Basic applies *)
      * left. intros [s' Htrans]. inversion Htrans as [r ? ? s'' Hr Hstep]; subst.
        assert (Hno_conflict: forall (c: Clause), c ∈ f -> c_eval m c <> Some false).
        -- intros c Hc_in_f Hc. enough (Htrue: CNF.exists_ (c_false m) f = true).
          ++ congruence.
          ++ apply CNF.exists_spec.
            ** intros c1 c2 Heq. now apply Hcompat_false.
            ** exists c. split.
              --- assumption.
              --- unfold c_false. now rewrite Hc.
        -- assert (Hall_def: forall (l: Lit), l ∈ f -> ~ Undef m l).
          ++ intros l [c [Hl_in_c Hc_in_f]] Hl.
             enough (Htrue: CNF.exists_ (fun (c: Clause) => Clause.exists_ (l_undef m) c) f = true).
            ** congruence.
            ** apply CNF.exists_spec.
              --- intros c1 c2 Heq. now apply Clause.c_equal_exists.
              --- exists c. split.
                +++ assumption.
                +++ apply Clause.exists_spec.
                  *** now intros ? ? ->.
                  *** exists l. split.
                    ---- assumption.
                    ---- unfold l_undef. unfold Undef in Hl. now rewrite Hl.
          ++ destruct Hr as [<-|[<-|[<-|[]]]].
            (* Fail *)
            ** inversion Hstep as [? ? c Hc_in_f Hc Hno_dec]; subst. now apply (Hno_conflict c).
            (* Decide *)
            ** inversion Hstep as [? ? l [Hl_in_f|Hnegl_in_f] Hl]; subst.
              --- now apply (Hall_def l).
              --- apply (Hall_def (¬l)).
                +++ assumption.
                +++ now apply l_eval_neg_none_iff in Hl.
            (* Backtrack *)
            ** inversion Hstep as [m' n ? c l Hc_in_f Hc Hno_dec]; subst. now apply (Hno_conflict c).
Qed.

(* Since there are no infinite derivations, every derivation from the initial state can be extended to a final state. *)
Theorem final_exists: forall (f: CNF),
  exists (s: State), state ⟨⟩ f ==>* s /\ Final DPLL s.
Proof.
  intros f. assert (Hfinal: forall (s: State), state ⟨⟩ f ==>* s -> exists (s': State), state ⟨⟩ f ==>* s' /\ Final DPLL s').
  - intros s. induction (strict_derivation_well_founded DPLL s) as [s _ IH]. intros Hderivation.
    destruct s as [|m f'].
    + exists fail. split.
      * assumption.
      * intros [s' Htrans]. inversion Htrans.
    + destruct (final_or_step m f') as [Hfinal|[s' Htrans]].
      * exists (state m f'). split.
        -- assumption.
        -- now apply final_dpll_basic.
      * apply (trans_incl Basic DPLL) in Htrans.
        -- apply IH with s'.
          ++ apply Relation_Operators.t_step. split.
            ** apply (derivation_well_formed DPLL ⟨⟩ m f f' Hderivation). apply initial_well_formed.
            ** assumption.
          ++ apply rt_trans with (state m f').
            ** assumption.
            ** now apply rt_step.
        -- intros r Hr. destruct Hr as [<-|[<-|[<-|[]]]].
          ++ now left.
          ++ right. right. now left.
          ++ right. right. right. now left.
  - apply Hfinal with (state ⟨⟩ f). apply rt_refl.
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
        apply PA.split_last_decision_some_iff in Hdecomp as [n_split [-> Hno_dec]].
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
          ++ now apply PA.split_last_decision_none_iff.
  (* Decide *)
  - exfalso. apply H. apply undef_decision_exists in Heq as [l_decide Hfind_dec].
    exists (state ⟨m; l_decide⟩ f).
    pose proof (find_decision_decomp m f l_decide Hfind_dec) as [c_decide [Hfind_undef_l Hc_in_f]].
    apply (t_step Decide).
    + right. right. now left.
    + apply r_decide.
      * left. exists c_decide. split.
        -- now apply find_undef_l_in_c in Hfind_undef_l.
        -- assumption.
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
      * now rewrite PA.app_empty_l.
      * assumption.
      * apply model_union_iff. split.
        -- assumption.
        -- apply model_units_iff. intros l [].
      * apply model_union_iff in Hm'' as [Hf Htrail]. rewrite PA.app_empty_l in Htrail.
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
