From Stdlib Require Import List.
From Stdlib Require Import Relations.

From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import State.
From RocqSAT Require Import Rule.
From RocqSAT Require Import Trans.
From RocqSAT.entailment Require Import Entails.
From RocqSAT.rules Require Import Fail.
From RocqSAT.rules Require Import Unit.
From RocqSAT.rules Require Import Decide.
From RocqSAT.rules Require Import Backtrack.
From RocqSAT.rules Require Import Pure.

(* Every transition, and hence every derivation, preserves entailment, as long as every rule does. *)
Lemma trans_entails: forall (rs: list Rule) (m m': PA) (f f': CNF) (Hwf: WellFormed m f) (Hwf': WellFormed m' f'),
  Forall PreservesEntails rs ->
  state m f Hwf ==>[rs] state m' f' Hwf' -> Entails f m -> Entails f' m'.
Proof.
  intros rs m m' f f' Hwf Hwf' Hrs Htrans.
  apply trans_rule in Htrans as [r [Hr Hstep]].
  rewrite Forall_forall in Hrs. now apply (Hrs r Hr m m' f f' Hwf Hwf').
Qed.

Lemma derivation_entails: forall (rs: list Rule) (m m': PA) (f f': CNF) (Hwf: WellFormed m f) (Hwf': WellFormed m' f'),
  Forall PreservesEntails rs ->
  state m f Hwf ==>*[rs] state m' f' Hwf' -> Entails f m -> Entails f' m'.
Proof.
  intros rs m m' f f' Hwf Hwf' Hrs H. apply clos_rt_rtn1_iff in H.
  remember (state m f Hwf) as s eqn:Heqs.
  remember (state m' f' Hwf') as s' eqn:Heqs'.
  generalize dependent m'. generalize dependent f'.
  induction H.
  - intros. subst. now injection Heqs' as <- <-.
  - intros f'' m'' Hwf'' Heqs' Hentails. destruct y.
    + subst. inversion H.
    + subst. apply (trans_entails rs m0 m'' f0 f'' Hwf0 Hwf'' Hrs H).
      now apply (IHclos_refl_trans_n1 f0 m0 Hwf0).
Qed.

Lemma dpll_entails: Forall PreservesEntails DPLL.
Proof.
  repeat apply Forall_cons.
  - exact fail_entails.
  - exact unit_entails.
  - exact decide_entails.
  - exact backtrack_entails.
  - exact pure_entails.
  - apply Forall_nil.
Qed.
