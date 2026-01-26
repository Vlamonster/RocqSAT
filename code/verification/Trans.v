From Stdlib Require Import List Relations.
Import ListNotations.
From RocqSAT Require Import Lit Neg Clause CNF Evaluation WellFormed.

Inductive State: Type :=
| fail
| state (m: PA) (f: CNF) (Hwf: WellFormed m f).

Inductive Trans: relation State :=
(* Fail if all literals are assigned and there is a conflict. *)
| t_fail (m: PA) (f: CNF) (c: Clause) (Hwf: WellFormed m f):
  In c f ->
  Conflicting m c ->
  NoDecisions m ->
  Trans (state m f Hwf) fail
(* If a clause is false except for one unassigned literal, assign it to satisfy the clause. *)
| t_unit (m: PA) (f: CNF) (c: Clause) (l: Lit) (Hwf: WellFormed m f) (Hwf': WellFormed (m ++p l) f):
  In l c ->
  In c f ->
  Conflicting m (l_remove c l) ->
  Undef m l ->
  Trans (state m f Hwf) (state (m ++p l) f Hwf')
(* Arbitrarily set an unassigned literal in the formula to true. *)
| t_decide (m: PA) (f: CNF) (c: Clause) (l: Lit) (Hwf: WellFormed m f) (Hwf': WellFormed (m ++d l) f):
  In l c \/ In (¬l) c ->
  In c f ->
  Undef m l ->
  Trans (state m f Hwf) (state (m ++d l) f Hwf')
(* Backtrack by flipping the most recent decision literal. *)
| t_backtrack (m n: PA) (f: CNF) (c: Clause) (l: Lit) (Hwf: WellFormed (m ++d l ++a n) f) (Hwf': WellFormed (m ++p ¬l) f):
  In c f ->
  Conflicting (m ++d l ++a n) c ->
  NoDecisions n ->
  Trans (state (m ++d l ++a n) f Hwf) (state (m ++p ¬l) f Hwf').

Inductive TransB: relation State :=
(* Fail if all literals are assigned and there is a conflict. *)
| tb_fail (m: PA) (f: CNF) (c: Clause) (Hwf: WellFormed m f):
  In c f ->
  Conflicting m c ->
  NoDecisions m ->
  TransB (state m f Hwf) fail
(* Arbitrarily set an unassigned literal in the formula to true. *)
| tb_decide (m: PA) (f: CNF) (c: Clause) (l: Lit) (Hwf: WellFormed m f) (Hwf': WellFormed (m ++d l) f):
  In l c \/ In (¬l) c ->
  In c f ->
  Undef m l ->
  TransB (state m f Hwf) (state (m ++d l) f Hwf')
(* Backtrack by flipping the most recent decision literal. *)
| tb_backtrack (m n: PA) (f: CNF) (c: Clause) (l: Lit) (Hwf: WellFormed (m ++d l ++a n) f) (Hwf': WellFormed (m ++p ¬l) f):
  In c f ->
  Conflicting (m ++d l ++a n) c ->
  NoDecisions n ->
  TransB (state (m ++d l ++a n) f Hwf) (state (m ++p ¬l) f Hwf').

(* The following is the reflexive-transitive closure of `==>`. *)
Definition Derivation: relation State := clos_refl_trans State Trans.

Declare Scope trans_scope.
Infix "==>" := Trans (at level 70): trans_scope.
Infix "==>b" := TransB (at level 70): trans_scope.
Infix "==>*" := Derivation (at level 70): trans_scope.
Open Scope trans_scope.

(* A state is final if there are no states that follow from it by `==>`. *)
Definition Final (s: State): Prop := ~ exists (s': State), s ==> s'.
Definition FinalB (s: State): Prop := ~ exists (s': State), s ==>b s'.

Lemma final__final_b: forall (s: State), Final s <-> FinalB s.
Proof.
  split.
  - unfold FinalB. unfold not. intros H [s' Htrans]. apply H. inversion Htrans as
    [
      m f c_conflict Hwf' Hc_in_f Hconflict Hno_dec |
      m f c_decide l_decide Hwf Hwf' Hx_in_c Hc_in_f Hundef |
      m_split n_split f c_conflict l_split Hwf Hwf' Hc_in_f Hconflict Hno_dec
    ]; subst s; subst s'.
    + exists fail. now apply (t_fail _ _ c_conflict).
    + exists (state (m ++d l_decide) f Hwf'). now apply (t_decide _ _ c_decide).
    + exists (state (m_split ++p (¬l_split)) f Hwf'). now apply (t_backtrack _ _ _ c_conflict).
  - unfold Final. unfold not. intros H [s' Htrans]. apply H. inversion Htrans as
    [
      m f c_conflict Hwf' Hc_in_f Hconflict Hno_dec |
      m f c_unit l_unit Hwf Hwf' Hl_in_c Hc_in_f Hconflict Hundef |
      m f c_decide l_decide Hwf Hwf' Hx_in_c Hc_in_f Hundef |
      m_split n_split f c_conflict l_split Hwf Hwf' Hc_in_f Hconflict Hno_dec
    ]; subst s; subst s'.
    + exists fail. now apply (tb_fail _ _ c_conflict).
    + assert (Hwf'': WellFormed (m ++d l_unit) f).
      * unfold WellFormed. split.
        -- apply nodup_cons.
          ++ apply Hwf.
          ++ assumption.
        -- apply bounded_cons.
          ++ apply Hwf.
          ++ apply l_in_f_true_iff. exists c_unit. intuition.
      * exists (state (m ++d l_unit) f Hwf''). apply (tb_decide _ _ c_unit).
        -- intuition.
        -- assumption.
        -- assumption.
    + exists (state (m ++d l_decide) f Hwf'). now apply (tb_decide _ _ c_decide).
    + exists (state (m_split ++p (¬l_split)) f Hwf'). now apply (tb_backtrack _ _ _ c_conflict).
Qed.

Lemma fail_final: Final fail.
Proof. unfold Final. unfold not. intros. inversion H. inversion H0. Qed.

Lemma initial_wf: forall (f: CNF), WellFormed [] f.
Proof.
  unfold WellFormed, NoDuplicates, Bounded. split.
  - constructor.
  - now intros.
Qed.

Lemma initial_refl: forall (f: CNF), state [] f (initial_wf f) ==>* state [] f (initial_wf f).
Proof. intros. apply rt_refl. Qed.

Lemma trans_same_formula: forall (m m': PA) (f f': CNF) (Hwf: WellFormed m f) (Hwf': WellFormed m' f'), 
  state m f Hwf ==> state m' f' Hwf' -> f = f'.
Proof. intros. inversion H; subst; reflexivity. Qed.

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
