From Stdlib Require Import List.
From Stdlib Require Import Relations.
Import ListNotations.

From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Model.
From RocqSAT Require Import State.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import Rule.
From RocqSAT.rules Require Import Fail.
From RocqSAT.rules Require Import Unit.
From RocqSAT.rules Require Import Decide.
From RocqSAT.rules Require Import Backtrack.
From RocqSAT.rules Require Import Pure.

(* A step of one of the rules in rs. Steps only start from a state other than fail, so fail is final. *)
Inductive Trans (rs: list Rule): relation State :=
| t_step (r: Rule) (m: PA) (f: CNF) (s': State):
  In r rs ->
  step r (state m f) s' ->
  Trans rs (state m f) s'.

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
Lemma trans_rule: forall (rs: list Rule) (m: PA) (f: CNF) (s': State),
  state m f ==>[rs] s' -> exists (r: Rule), In r rs /\ step r (state m f) s'.
Proof.
  intros rs m f s' Htrans. inversion Htrans as [r ? ? ? Hr Hstep]; subst. now exists r.
Qed.

(* A transition is in the union of the rules exactly when one of its rules allows it. *)
Lemma trans_union: forall (rs: list Rule) (s s': State),
  s ==>[rs] s' <-> exists (r: Rule), In r rs /\ s ==>[[r]] s'.
Proof.
  intros rs s s'. split.
  - intros Htrans. inversion Htrans as [r m f s'' Hr Hstep]; subst. exists r. split.
    + assumption.
    + apply (t_step r).
      * now left.
      * assumption.
  - intros [r [Hr Htrans]]. inversion Htrans as [r' m f s'' Hr' Hstep]; subst.
    destruct Hr' as [<-|[]]. now apply (t_step r).
Qed.

(* Adding rules keeps every transition. *)
Lemma trans_incl: forall (rs rs': list Rule) (s s': State),
  incl rs rs' -> s ==>[rs] s' -> s ==>[rs'] s'.
Proof.
  intros rs rs' s s' Hincl Htrans. inversion Htrans as [r m f s'' Hr Hstep]; subst. apply (t_step r).
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
    inversion Htrans as [r m f s'' Hr Hstep]; subst.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]].
    + exists s'. apply (t_step Fail).
      * now left.
      * assumption.
    + inversion Hstep as [? ? c_unit l_unit Hl_in_c Hc_in_f Hconflict Hundef]; subst.
      exists (state (m ++d l_unit) f). apply (t_step Decide).
      * right. now left.
      * apply (r_decide m f c_unit l_unit).
        -- now left.
        -- assumption.
        -- assumption.
    + exists s'. apply (t_step Decide).
      * right. now left.
      * assumption.
    + exists s'. apply (t_step Backtrack).
      * right. right. now left.
      * assumption.
    + inversion Hstep as [? ? c_pure l_pure Hl_in_c Hc_in_f Hpure Hundef]; subst.
      exists (state (m ++d l_pure) f). apply (t_step Decide).
      * right. now left.
      * apply (r_decide m f c_pure l_pure).
        -- now left.
        -- assumption.
        -- assumption.
Qed.

Lemma initial_refl: forall (f: CNF), state [] f ==>* state [] f.
Proof. intros. apply rt_refl. Qed.

(* Transitions, and hence derivations, keep states well-formed. *)
Lemma trans_well_formed: forall (rs: list Rule) (s s': State),
  s ==>[rs] s' -> WellFormed s -> WellFormed s'.
Proof.
  intros rs s s' Htrans Hwf. inversion Htrans as [r m f s'' Hr Hstep]; subst.
  destruct s' as [|m' f'].
  - easy.
  - now apply (rule_well_formed r m m' f f').
Qed.

Lemma derivation_well_formed: forall (rs: list Rule) (s s': State),
  s ==>*[rs] s' -> WellFormed s -> WellFormed s'.
Proof.
  intros rs s s' H. induction H as [x y Htrans | x | x y z _ IHxy _ IHyz].
  - now apply (trans_well_formed rs x).
  - easy.
  - intros Hwf. now apply IHyz, IHxy.
Qed.

(* Transitions never change the formula, as long as no rule does. *)
Lemma trans_same_formula: forall (rs: list Rule) (m m': PA) (f f': CNF),
  Forall (fun (r: Rule) => KeepsFormula (step r)) rs ->
  state m f ==>[rs] state m' f' -> f = f'.
Proof.
  intros rs m m' f f' Hrs Htrans.
  apply trans_rule in Htrans as [r [Hr Hstep]].
  rewrite Forall_forall in Hrs. now apply (Hrs r Hr m m' f f').
Qed.

Lemma dpll_keeps_formula: Forall (fun (r: Rule) => KeepsFormula (step r)) DPLL.
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
Lemma derivation_same_formula: forall (m m': PA) (f f': CNF),
  state m f ==>* state m' f' -> f = f'.
Proof.
  intros m m' f f' H. apply clos_rt_rtn1_iff in H.
  remember (state m f) as s eqn:Heqs.
  remember (state m' f') as s' eqn:Heqs'.
  generalize dependent m'. generalize dependent f'.
  induction H.
  - intros. subst. now injection Heqs' as <- <-.
  - intros. destruct y.
    + subst. inversion H.
    + subst. apply (trans_same_formula DPLL) in H as <-.
      * now apply (IHclos_refl_trans_n1 f0 m0).
      * exact dpll_keeps_formula.
Qed.

(* Transitions, and hence derivations, only change the formula to an equivalent one. *)
Lemma trans_equivalent: forall (rs: list Rule) (m m': PA) (f f': CNF),
  state m f ==>[rs] state m' f' -> Equivalent f f'.
Proof.
  intros rs m m' f f' Htrans.
  apply trans_rule in Htrans as [r [_ Hstep]]. now apply (rule_equivalence r m m' f f').
Qed.

Lemma derivation_equivalent: forall (rs: list Rule) (m m': PA) (f f': CNF),
  state m f ==>*[rs] state m' f' -> Equivalent f f'.
Proof.
  intros rs m m' f f' H. apply clos_rt_rtn1_iff in H.
  remember (state m f) as s eqn:Heqs.
  remember (state m' f') as s' eqn:Heqs'.
  generalize dependent m'. generalize dependent f'.
  induction H.
  - intros. subst. injection Heqs' as <- <-. apply equivalent_refl.
  - intros. destruct y.
    + subst. inversion H.
    + subst. apply (equivalent_trans f f0 f').
      * now apply (IHclos_refl_trans_n1 f0 m0).
      * now apply (trans_equivalent rs m0 m' f0 f').
Qed.

(* A derivation that ends in fail passes through a state that steps to fail directly. *)
Lemma fail_predecessor: forall (m: PA) (f: CNF),
  state m f ==>* fail ->
  exists (m': PA) (f': CNF), state m f ==>* state m' f' /\ state m' f' ==> fail.
Proof.
  intros. apply clos_rt_rtn1_iff in H.
  remember (state m f) as s eqn:Heqs.
  remember (fail) as s' eqn:Heqs'.
  induction H.
  - congruence.
  - subst s; subst z. destruct y.
    + now apply IHclos_refl_trans_n1.
    + apply clos_rt_rtn1_iff in H0. now exists m0, f0.
Qed.
