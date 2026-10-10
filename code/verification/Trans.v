From Stdlib Require Import List.
From Stdlib Require Import Relations.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import WellFormed.

(* A state is either the failure state or a well-formed assignment for a formula. *)
Inductive State: Type :=
| fail
| state (m: PA) (f: CNF) (Hwf: WellFormed m f).

(* The rules of the abstract transition system. *)
Inductive Rule: Type := 
| Fail 
| Unit 
| Decide 
| Backtrack 
| Pure.

(* The union of the transitions of all rules in `rs` (only membership in `rs` matters). *)
Inductive Trans (rs: list Rule): relation State :=
(* Fail if all literals are assigned and there is a conflict. *)
| t_fail (m: PA) (f: CNF) (c: Clause) (Hwf: WellFormed m f):
  In Fail rs ->
  CNF.In c f ->
  c_eval m c = Some false ->
  NoDecisions m ->
  Trans rs (state m f Hwf) fail
(* If a clause is false except for one unassigned literal, assign it to satisfy the clause. *)
| t_unit (m: PA) (f: CNF) (c: Clause) (l: Lit) (Hwf: WellFormed m f) (Hwf': WellFormed (m ++p l) f):
  In Unit rs ->
  Clause.In l c ->
  CNF.In c f ->
  c_eval m (Clause.remove l c) = Some false ->
  Undef m l ->
  Trans rs (state m f Hwf) (state (m ++p l) f Hwf')
(* Arbitrarily set an unassigned literal in the formula to true. *)
| t_decide (m: PA) (f: CNF) (c: Clause) (l: Lit) (Hwf: WellFormed m f) (Hwf': WellFormed (m ++d l) f):
  In Decide rs ->
  Clause.In l c \/ Clause.In (¬l) c ->
  CNF.In c f ->
  Undef m l ->
  Trans rs (state m f Hwf) (state (m ++d l) f Hwf')
(* Backtrack by flipping the most recent decision literal. *)
| t_backtrack (m n: PA) (f: CNF) (c: Clause) (l: Lit) (Hwf: WellFormed (m ++d l ++a n) f) (Hwf': WellFormed (m ++p (¬l)) f):
  In Backtrack rs ->
  CNF.In c f ->
  c_eval (m ++d l ++a n) c = Some false ->
  NoDecisions n ->
  Trans rs (state (m ++d l ++a n) f Hwf) (state (m ++p (¬l)) f Hwf')
(* Adds a literal that only occurs positively. *)
| t_pure (m: PA) (f: CNF) (c: Clause) (l: Lit) (Hwf: WellFormed m f) (Hwf': WellFormed (m ++p l) f):
  In Pure rs ->
  Clause.In l c ->
  CNF.In c f ->
  (forall (c': Clause), CNF.In c' f -> ~ Clause.In (¬l) c') ->
  Undef m l ->
  Trans rs (state m f Hwf) (state (m ++p l) f Hwf').

Arguments t_fail {rs}.
Arguments t_unit {rs}.
Arguments t_decide {rs}.
Arguments t_backtrack {rs}.
Arguments t_pure {rs}.

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

(* A transition is in the union of the rules exactly when one of its rules allows it. *)
Lemma trans_union: forall (rs: list Rule) (s s': State),
  s ==>[rs] s' <-> exists (r: Rule), In r rs /\ s ==>[[r]] s'.
Proof.
  intros rs s s'. split.
  - intros Htrans. destruct Htrans as
    [
      m f c Hwf Hr |
      m f c l Hwf Hwf' Hr |
      m f c l Hwf Hwf' Hr |
      m n f c l Hwf Hwf' Hr |
      m f c l Hwf Hwf' Hr
    ].
    + exists Fail. split.
      * assumption.
      * apply (t_fail m f c); try assumption. now left.
    + exists Unit. split.
      * assumption.
      * apply (t_unit m f c l); try assumption. now left.
    + exists Decide. split.
      * assumption.
      * apply (t_decide m f c l); try assumption. now left.
    + exists Backtrack. split.
      * assumption.
      * apply (t_backtrack m n f c l); try assumption. now left.
    + exists Pure. split.
      * assumption.
      * apply (t_pure m f c l); try assumption. now left.
  - intros [r [Hr Htrans]]. destruct Htrans as
    [
      m f c Hwf Hin |
      m f c l Hwf Hwf' Hin |
      m f c l Hwf Hwf' Hin |
      m n f c l Hwf Hwf' Hin |
      m f c l Hwf Hwf' Hin
    ]; destruct Hin as [->|[]].
    + now apply (t_fail m f c).
    + now apply (t_unit m f c l).
    + now apply (t_decide m f c l).
    + now apply (t_backtrack m n f c l).
    + now apply (t_pure m f c l).
Qed.

(* A state is final if there are no states that follow from it by `==>[rs]`. *)
Definition Final (rs: list Rule) (s: State): Prop := ~ exists (s': State), s ==>[rs] s'.

(* Unit and Pure are not needed to recognise final states: whenever they apply, Decide applies as well. *)
Lemma final_dpll_basic: forall (s: State), Final DPLL s <-> Final Basic s.
Proof.
  split.
  - unfold Final. unfold not. intros H [s' Htrans]. apply H. inversion Htrans as
    [
      m f c_conflict Hwf' Hr Hc_in_f Hconflict Hno_dec |
      m f c_unit l_unit Hwf Hwf' Hr |
      m f c_decide l_decide Hwf Hwf' Hr Hx_in_c Hc_in_f Hundef |
      m_split n_split f c_conflict l_split Hwf Hwf' Hr Hc_in_f Hconflict Hno_dec |
      m f c_pure l_pure Hwf Hwf' Hr
    ]; subst s; subst s'.
    + exists fail. apply (t_fail _ _ c_conflict); try assumption. now left.
    + destruct Hr as [Hr|[Hr|[Hr|[]]]]; discriminate.
    + exists (state (m ++d l_decide) f Hwf'). apply (t_decide _ _ c_decide); try assumption.
      right. right. now left.
    + exists (state (m_split ++p (¬l_split)) f Hwf'). apply (t_backtrack _ _ _ c_conflict); try assumption.
      right. right. right. now left.
    + destruct Hr as [Hr|[Hr|[Hr|[]]]]; discriminate.
  - unfold Final. unfold not. intros H [s' Htrans]. apply H. inversion Htrans as
    [
      m f c_conflict Hwf' _ Hc_in_f Hconflict Hno_dec |
      m f c_unit l_unit Hwf Hwf' _ Hl_in_c Hc_in_f Hconflict Hundef |
      m f c_decide l_decide Hwf Hwf' _ Hx_in_c Hc_in_f Hundef |
      m_split n_split f c_conflict l_split Hwf Hwf' _ Hc_in_f Hconflict Hno_dec |
      m f c_pure l_pure Hwf Hwf' _ Hl_in_c Hc_in_f Hpure Hundef
    ]; subst s; subst s'.
    + exists fail. apply (t_fail _ _ c_conflict); try assumption. now left.
    + assert (Hwf'': WellFormed (m ++d l_unit) f).
      * unfold WellFormed. split.
        -- apply nodup_cons.
          ++ apply Hwf.
          ++ assumption.
        -- apply bounded_cons.
          ++ apply Hwf.
          ++ apply CNF.l_in_f_true_iff. exists c_unit. intuition.
      * exists (state (m ++d l_unit) f Hwf''). apply (t_decide _ _ c_unit).
        -- right. now left.
        -- intuition.
        -- assumption.
        -- assumption.
    + exists (state (m ++d l_decide) f Hwf'). apply (t_decide _ _ c_decide); try assumption.
      right. now left.
    + exists (state (m_split ++p (¬l_split)) f Hwf'). apply (t_backtrack _ _ _ c_conflict); try assumption.
      right. right. now left.
    + assert (Hwf'': WellFormed (m ++d l_pure) f).
      * unfold WellFormed. split.
        -- apply nodup_cons.
          ++ apply Hwf.
          ++ assumption.
        -- apply bounded_cons.
          ++ apply Hwf.
          ++ apply CNF.l_in_f_true_iff. exists c_pure. intuition.
      * exists (state (m ++d l_pure) f Hwf''). apply (t_decide _ _ c_pure).
        -- right. now left.
        -- intuition.
        -- assumption.
        -- assumption.
Qed.
Lemma initial_refl: forall (f: CNF), state [] f (initial_well_formed f) ==>* state [] f (initial_well_formed f).
Proof. intros. apply rt_refl. Qed.

(* Transitions never change the formula. *)
Lemma trans_same_formula: forall (rs: list Rule) (m m': PA) (f f': CNF) (Hwf: WellFormed m f) (Hwf': WellFormed m' f'),
  state m f Hwf ==>[rs] state m' f' Hwf' -> f = f'.
Proof. intros. inversion H; subst; reflexivity. Qed.
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
    + subst. injection Heqs' as <- <-. apply trans_same_formula in H as <-.
      now apply IHclos_refl_trans_n1 with (Hwf':=Hwf0) (Hwf:=Hwf).
Qed.

(* A derivation that ends in fail passes through a state that steps to fail directly. *)
Lemma fail_predecessor: forall (m: PA) (f: CNF) (Hwf: WellFormed m f),
  state m f Hwf ==>* fail -> 
  exists (m': PA) (Hwf': WellFormed m' f), 
    state m f Hwf ==>* state m' f Hwf' /\ state m' f Hwf' ==> fail.
Proof.
  intros. apply clos_rt_rtn1_iff in H.
  remember (state m f Hwf) as s eqn:Heqs.
  remember (fail) as s' eqn:Heqs'.
  induction H.
  - congruence.
  - subst s; subst z. destruct y.
    + now apply IHclos_refl_trans_n1.
    + apply clos_rt_rtn1_iff in H0. apply derivation_same_formula in H0 as Heq.
      subst f0. now exists m0, Hwf0.
Qed.
