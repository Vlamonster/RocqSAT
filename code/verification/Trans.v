From Stdlib Require Import List.
From Stdlib Require Import Relations.
Import ListNotations.

From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Model.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import State.
From RocqSAT Require Import Rule.
From RocqSAT.rules Require Import Fail.
From RocqSAT.rules Require Import Unit.
From RocqSAT.rules Require Import Decide.
From RocqSAT.rules Require Import Backtrack.
From RocqSAT.rules Require Import Pure.

(* A step of one of the rules in rs. Steps only start from a state other than fail, so fail is final. *)
Inductive Trans (rs: list Rule): relation State :=
| t_step (r: Rule) (m: PA) (f: CNF) (Hwf: WellFormed m f) (s': State):
  In r rs ->
  r (state m f Hwf) s' ->
  Trans rs (state m f Hwf) s'.

Arguments t_step {rs}.

(* All rules, and the basic rules that suffice to decide satisfiability. *)
Definition DPLL: list Rule := [Fail; Unit; Decide; Backtrack; Pure].
(* The rules a strategy has to implement: a state is final for DPLL exactly when it is final for these (final_dpll_basic). *)
Definition Basic: list Rule := [Fail; Decide; Backtrack].

(* Sequences of zero or more (Derivation) or one or more (DerivationStrict) transitions. *)
Definition Derivation (rs: list Rule): relation State := clos_refl_trans State (Trans rs).
Definition DerivationStrict (rs: list Rule): relation State := clos_trans State (Trans rs).

Declare Scope trans_scope.
Notation "s ==>[ rs ] s'" := (Trans rs s s') (at level 70, format "s  ==>[ rs ]  s'"): trans_scope.
Notation "s ==>*[ rs ] s'" := (Derivation rs s s') (at level 70, format "s  ==>*[ rs ]  s'"): trans_scope.
Notation "s ==>+[ rs ] s'" := (DerivationStrict rs s s') (at level 70, format "s  ==>+[ rs ]  s'"): trans_scope.
Notation "s ==> s'" := (Trans DPLL s s') (at level 70): trans_scope.
Notation "s ==>* s'" := (Derivation DPLL s s') (at level 70): trans_scope.
Notation "s ==>+ s'" := (DerivationStrict DPLL s s') (at level 70): trans_scope.
Open Scope trans_scope.

(* A transition from a state is a step of one of the rules from that same state. *)
Lemma trans_rule: forall (rs: list Rule) (m: PA) (f: CNF) (Hwf: WellFormed m f) (s': State),
  state m f Hwf ==>[rs] s' -> exists (r: Rule), In r rs /\ r (state m f Hwf) s'.
Proof.
  intros rs m f Hwf s' Htrans. remember (state m f Hwf) as s eqn:Hs.
  destruct Htrans as [r m' f' Hwf' s' Hr Hstep]. now exists r.
Qed.

(* A transition is in the union of the rules exactly when one of its rules allows it. *)
Lemma trans_union: forall (rs: list Rule) (s s': State),
  s ==>[rs] s' <-> exists (r: Rule), In r rs /\ s ==>[[r]] s'.
Proof.
  intros rs s s'. split.
  - intros Htrans. inversion Htrans as [r m f Hwf s'' Hr Hstep]; subst. exists r. split.
    + assumption.
    + apply (t_step r).
      * now left.
      * assumption.
  - intros [r [Hr Htrans]]. inversion Htrans as [r' m f Hwf s'' Hr' Hstep]; subst.
    destruct Hr' as [<-|[]]. now apply (t_step r).
Qed.

(* Adding rules keeps every transition. *)
Lemma trans_incl: forall (rs rs': list Rule) (s s': State),
  incl rs rs' -> s ==>[rs] s' -> s ==>[rs'] s'.
Proof.
  intros rs rs' s s' Hincl Htrans. inversion Htrans as [r m f Hwf s'' Hr Hstep]; subst. apply (t_step r).
  - now apply Hincl.
  - assumption.
Qed.

(* A state is final if there are no states that follow from it by `==>[rs]`. *)
Definition Final (rs: list Rule) (s: State): Prop := ~ exists (s': State), s ==>[rs] s'.

(* Unit and Pure are not needed to recognise final states: whenever they apply, Decide applies as well. *)
Lemma final_dpll_basic: forall (s: State), Final DPLL s <-> Final Basic s.
Proof.
  intros s. unfold Final. split.
  - intros Hfinal [s' Htrans]. apply Hfinal. exists s'. apply (trans_incl Basic).
    + intros r Hr. destruct Hr as [<-|[<-|[<-|[]]]].
      * now left.
      * right. right. now left.
      * right. right. right. now left.
    + assumption.
  - intros Hfinal [s' Htrans]. apply Hfinal.
    inversion Htrans as [r m f Hwf s'' Hr Hstep]; subst.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]].
    + exists s'. apply (t_step Fail).
      * now left.
      * assumption.
    + inversion Hstep as [? ? c_unit l_unit ? ? Hl_in_c Hc_in_f Hconflict Hundef]; subst.
      assert (Hwf'': WellFormed (m ++d l_unit) f).
      * unfold WellFormed. split.
        -- apply nodup_cons.
          ++ apply Hwf.
          ++ assumption.
        -- apply bounded_cons.
          ++ apply Hwf.
          ++ apply CNF.l_in_f_true_iff. exists c_unit. intuition.
      * exists (state (m ++d l_unit) f Hwf''). apply (t_step Decide).
        -- right. now left.
        -- apply (r_decide m f c_unit l_unit).
          ++ now left.
          ++ assumption.
          ++ assumption.
    + exists s'. apply (t_step Decide).
      * right. now left.
      * assumption.
    + exists s'. apply (t_step Backtrack).
      * right. right. now left.
      * assumption.
    + inversion Hstep as [? ? c_pure l_pure ? ? Hl_in_c Hc_in_f Hpure Hundef]; subst.
      assert (Hwf'': WellFormed (m ++d l_pure) f).
      * unfold WellFormed. split.
        -- apply nodup_cons.
          ++ apply Hwf.
          ++ assumption.
        -- apply bounded_cons.
          ++ apply Hwf.
          ++ apply CNF.l_in_f_true_iff. exists c_pure. intuition.
      * exists (state (m ++d l_pure) f Hwf''). apply (t_step Decide).
        -- right. now left.
        -- apply (r_decide m f c_pure l_pure).
          ++ now left.
          ++ assumption.
          ++ assumption.
Qed.

Lemma initial_refl: forall (f: CNF), state [] f (initial_well_formed f) ==>* state [] f (initial_well_formed f).
Proof. intros. apply rt_refl. Qed.

(* Transitions never change the formula, as long as no rule does. *)
Lemma trans_same_formula: forall (rs: list Rule) (m m': PA) (f f': CNF) (Hwf: WellFormed m f) (Hwf': WellFormed m' f'),
  Forall KeepsFormula rs ->
  state m f Hwf ==>[rs] state m' f' Hwf' -> f = f'.
Proof.
  intros rs m m' f f' Hwf Hwf' Hrs Htrans.
  apply trans_rule in Htrans as [r [Hr Hstep]].
  rewrite Forall_forall in Hrs. now apply (Hrs r Hr m m' f f' Hwf Hwf').
Qed.

Lemma dpll_keeps_formula: Forall KeepsFormula DPLL.
Proof.
  repeat apply Forall_cons.
  - exact fail_keeps_formula.
  - exact unit_keeps_formula.
  - exact decide_keeps_formula.
  - exact backtrack_keeps_formula.
  - exact pure_keeps_formula.
  - apply Forall_nil.
Qed.


(* Likewise for derivations. *)
Lemma derivation_same_formula: forall (m m': PA) (f f': CNF) (Hwf: WellFormed m f) (Hwf': WellFormed m' f'), 
  state m f Hwf ==>* state m' f' Hwf' -> f = f'.
Proof. 
  intros m m' f f' Hwf Hwf' H. apply clos_rt_rtn1_iff in H. 
  remember (state m f Hwf) as s eqn:Heqs.
  remember (state m' f' Hwf') as s' eqn:Heqs'.
  generalize dependent m. generalize dependent m'.
  induction H.
  - intros. congruence.
  - intros. destruct y, z; try congruence.
    + inversion H.
    + subst. injection Heqs' as <- <-. apply (trans_same_formula DPLL) in H as <-.
      * now apply IHclos_refl_trans_n1 with (Hwf':=Hwf0) (Hwf:=Hwf).
      * exact dpll_keeps_formula.
Qed.

(* Transitions, and hence derivations, only change the formula to an equivalent one, as long as no rule does otherwise. *)
Lemma trans_equivalent: forall (rs: list Rule) (m m': PA) (f f': CNF) (Hwf: WellFormed m f) (Hwf': WellFormed m' f'),
  Forall PreservesEquivalence rs ->
  state m f Hwf ==>[rs] state m' f' Hwf' -> Equivalent f f'.
Proof.
  intros rs m m' f f' Hwf Hwf' Hrs Htrans.
  apply trans_rule in Htrans as [r [Hr Hstep]].
  rewrite Forall_forall in Hrs. now apply (Hrs r Hr m m' f f' Hwf Hwf').
Qed.

Lemma derivation_equivalent: forall (rs: list Rule) (m m': PA) (f f': CNF) (Hwf: WellFormed m f) (Hwf': WellFormed m' f'),
  Forall PreservesEquivalence rs ->
  state m f Hwf ==>*[rs] state m' f' Hwf' -> Equivalent f f'.
Proof.
  intros rs m m' f f' Hwf Hwf' Hrs H. apply clos_rt_rtn1_iff in H.
  remember (state m f Hwf) as s eqn:Heqs.
  remember (state m' f' Hwf') as s' eqn:Heqs'.
  generalize dependent m'. generalize dependent f'.
  induction H.
  - intros. subst. injection Heqs' as <- <-. apply equivalent_refl.
  - intros. destruct y.
    + subst. inversion H.
    + subst. apply (equivalent_trans f f0 f').
      * now apply (IHclos_refl_trans_n1 f0 m0 Hwf0).
      * now apply (trans_equivalent rs m0 m' f0 f' Hwf0 Hwf').
Qed.

Lemma dpll_equivalence: Forall PreservesEquivalence DPLL.
Proof. apply (Forall_impl _ keeps_formula_equivalence dpll_keeps_formula). Qed.

(* A derivation that ends in fail passes through a state that steps to fail directly. *)
Lemma fail_predecessor: forall (m: PA) (f: CNF) (Hwf: WellFormed m f),
  state m f Hwf ==>* fail ->
  exists (m': PA) (f': CNF) (Hwf': WellFormed m' f'),
    state m f Hwf ==>* state m' f' Hwf' /\ state m' f' Hwf' ==> fail.
Proof.
  intros. apply clos_rt_rtn1_iff in H.
  remember (state m f Hwf) as s eqn:Heqs.
  remember (fail) as s' eqn:Heqs'.
  induction H.
  - congruence.
  - subst s; subst z. destruct y.
    + now apply IHclos_refl_trans_n1.
    + apply clos_rt_rtn1_iff in H0. now exists m0, f0, Hwf0.
Qed.
