From Stdlib Require Import Relations.

From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import State.
From RocqSAT Require Import Rule.
From RocqSAT Require Import Trans.
From RocqSAT.entailment Require Import Entails.

(* Every transition, and hence every derivation, preserves entailment. *)
Lemma trans_entails: forall (rs: list Rule) (m m': PA) (f f': CNF),
  state m f ==>[rs] state m' f' -> Entails f m -> Entails f' m'.
Proof.
  intros rs m m' f f' Htrans.
  apply trans_rule in Htrans as [r [_ Hstep]]. now apply (rule_entails r m m' f f').
Qed.

Lemma derivation_entails: forall (rs: list Rule) (m m': PA) (f f': CNF),
  state m f ==>*[rs] state m' f' -> Entails f m -> Entails f' m'.
Proof.
  intros rs m m' f f' H. apply clos_rt_rtn1_iff in H.
  remember (state m f) as s eqn:Heqs.
  remember (state m' f') as s' eqn:Heqs'.
  generalize dependent m'. generalize dependent f'.
  induction H.
  - intros. subst. now injection Heqs' as <- <-.
  - intros f'' m'' Heqs' Hentails. destruct y.
    + subst. inversion H.
    + subst. apply (trans_entails rs m0 m'' f0 f'' H).
      now apply (IHclos_refl_trans_n1 f0 m0).
Qed.
