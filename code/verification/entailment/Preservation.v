From Stdlib Require Import Relations.

From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import Trans.
From RocqSAT.entailment Require Import Entails.
From RocqSAT.rules Require Import Fail.
From RocqSAT.rules Require Import Unit.
From RocqSAT.rules Require Import Decide.
From RocqSAT.rules Require Import Backtrack.
From RocqSAT.rules Require Import Pure.

(* Every transition, and hence every derivation, preserves entailment. *)

Lemma trans_entails: forall (rs: list Rule) (m m': PA) (f: CNF) (Hwf: WellFormed m f) (Hwf': WellFormed m' f),
  state m f Hwf ==>[rs] state m' f Hwf' -> Entails f m -> Entails f m'.
Proof.
  intros rs m m' f Hwf Hwf' Htrans. apply trans_union in Htrans as [r [_ Htrans]]. destruct r.
  - now apply (fail_entails m m' f Hwf Hwf').
  - now apply (unit_entails m m' f Hwf Hwf').
  - now apply (decide_entails m m' f Hwf Hwf').
  - now apply (backtrack_entails m m' f Hwf Hwf').
  - now apply (pure_entails m m' f Hwf Hwf').
Qed.

Lemma derivation_entails: forall (rs: list Rule) (m m': PA) (f: CNF) (Hwf: WellFormed m f) (Hwf': WellFormed m' f),
  state m f Hwf ==>*[rs] state m' f Hwf' -> Entails f m -> Entails f m'.
Proof.
  intros rs m m' f Hwf Hwf' H. apply clos_rt_rtn1_iff in H. 
  remember (state m f Hwf) as s eqn:Heqs.
  remember (state m' f Hwf') as s' eqn:Heqs'.
  generalize dependent m. generalize dependent m'.
  induction H.
  - intros. congruence.
  - intros. subst s; subst z. destruct y.
    + inversion H.
    + apply trans_same_formula in H as Heq. subst f0. apply trans_entails in H.
      * assumption.
      * now apply IHclos_refl_trans_n1 with (Hwf':= Hwf0) (Hwf:=Hwf).
Qed.
