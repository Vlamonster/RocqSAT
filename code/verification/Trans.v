From Stdlib Require Import List.
From Stdlib Require Import Relations.
Import ListNotations.

From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Model.
From RocqSAT Require Import State.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import Entails.
From RocqSAT Require Import Rule.
From RocqSAT.rules Require Import Fail.
From RocqSAT.rules Require Import Unit.
From RocqSAT.rules Require Import Decide.
From RocqSAT.rules Require Import Backtrack.
From RocqSAT.rules Require Import Backjump.
From RocqSAT.rules Require Import Pure.
From RocqSAT.utils Require Import Invariant.

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
(* DPLL with Backjump in place of Backtrack. *)
Definition DPLL_BJ: list Rule := [Fail; Unit; Decide; Backjump; Pure].

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
Lemma trans_dpll_basic: forall (s s': State), s ==> s' -> exists (s'': State), s ==>[Basic] s''.
Proof.
  intros s s' Htrans. inversion Htrans as [r m f s'' Hr Hstep]; subst.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - exists s'. apply (t_step Fail).
    + now left.
    + assumption.
  - inversion Hstep as [? ? c_unit l_unit Hl_in_c Hc_in_f Hconflict Hundef]; subst.
    exists (state ⟨m; l_unit⟩ f). apply (t_step Decide).
    + right. now left.
    + apply r_decide.
      * left. now exists c_unit.
      * assumption.
  - exists s'. apply (t_step Decide).
    + right. now left.
    + assumption.
  - exists s'. apply (t_step Backtrack).
    + right. right. now left.
    + assumption.
  - inversion Hstep as [? ? l_pure Hl_in_f Hpure Hundef]; subst.
    exists (state ⟨m; l_pure⟩ f). apply (t_step Decide).
    + right. now left.
    + apply r_decide.
      * now left.
      * assumption.
Qed.

(* Hence a state is final for DPLL exactly when it is final for Basic. *)
Lemma final_dpll_basic: forall (s: State), Final DPLL s <-> Final Basic s.
Proof.
  intros s. unfold Final. split.
  - intros Hfinal [s' Htrans]. apply Hfinal. exists s'. apply (trans_incl Basic).
    + intros r Hr. destruct Hr as [<-|[<-|[<-|[]]]].
      * now left.
      * right. right. now left.
      * right. right. right. now left.
    + assumption.
  - intros Hfinal [s' Htrans]. apply Hfinal. now apply trans_dpll_basic in Htrans.
Qed.

Lemma initial_refl: forall (f: CNF), state ⟨⟩ f ==>* state ⟨⟩ f.
Proof. intros. apply rt_refl. Qed.

(* A property of assignments that every transition between states preserves is preserved by every derivation between states. *)
Lemma derivation_invariant: forall (rs: list Rule) (P: PA -> CNF -> Prop),
  (forall (m m': PA) (f f': CNF), state m f ==>[rs] state m' f' -> P m f -> P m' f') ->
  forall (m m': PA) (f f': CNF), state m f ==>*[rs] state m' f' -> P m f -> P m' f'.
Proof.
  intros rs P Hstep m m' f f'.
  apply (clos_refl_trans_invariant _ _ (fun (s: State) => match s with fail => True | state m f => P m f end)).
  intros [|m0 f0] [|m1 f1] Htrans.
  - easy.
  - inversion Htrans.
  - easy.
  - now apply Hstep.
Qed.

(* Transitions, and hence derivations, keep states well-formed. *)
Lemma trans_well_formed: forall (rs: list Rule) (s s': State),
  s ==>[rs] s' -> WellFormed s -> WellFormed s'.
Proof.
  intros rs s s' Htrans Hwf. inversion Htrans as [r m f s'' Hr Hstep]; subst.
  destruct s' as [|m' f'].
  - easy.
  - apply rule_well_formed in Hstep. now apply Hstep.
Qed.

Lemma derivation_well_formed: forall (rs: list Rule) (m m': PA) (f f': CNF),
  state m f ==>*[rs] state m' f' -> WellFormed (state m f) -> WellFormed (state m' f').
Proof.
  intros rs. apply derivation_invariant. intros m m' f f'. apply trans_well_formed.
Qed.

(* Transitions, and hence derivations, only change the formula to an equivalent one. *)
Lemma trans_equivalent: forall (rs: list Rule) (m m': PA) (f f': CNF),
  state m f ==>[rs] state m' f' -> Equivalent f f'.
Proof.
  intros rs m m' f f' Htrans.
  apply trans_rule in Htrans as [r [_ Hstep]]. now apply rule_equivalence in Hstep.
Qed.

Lemma derivation_equivalent: forall (rs: list Rule) (m m': PA) (f f': CNF),
  state m f ==>*[rs] state m' f' -> Equivalent f f'.
Proof.
  intros rs m m' f f' H.
  apply (derivation_invariant rs (fun (_: PA) (g: CNF) => Equivalent f g)) with (m := m) (m' := m') (f := f).
  - intros m0 m1 f0 f1 Htrans Hf0. apply trans_equivalent in Htrans. now apply equivalent_trans with f0.
  - assumption.
  - apply equivalent_refl.
Qed.

(* Every transition, and hence every derivation, preserves entailment. *)
Lemma trans_entails: forall (rs: list Rule) (m m': PA) (f f': CNF),
  state m f ==>[rs] state m' f' -> Entails f m -> Entails f' m'.
Proof.
  intros rs m m' f f' Htrans.
  apply trans_rule in Htrans as [r [_ Hstep]]. now apply rule_entails in Hstep.
Qed.

Lemma derivation_entails: forall (rs: list Rule) (m m': PA) (f f': CNF),
  state m f ==>*[rs] state m' f' -> Entails f m -> Entails f' m'.
Proof. intros rs. apply derivation_invariant. intros m m' f f'. apply trans_entails. Qed.

(* A derivation that ends in fail passes through a state that steps to fail directly. *)
Lemma fail_predecessor: forall (rs: list Rule) (m: PA) (f: CNF),
  state m f ==>*[rs] fail ->
  exists (m': PA) (f': CNF), state m f ==>*[rs] state m' f' /\ state m' f' ==>[rs] fail.
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
