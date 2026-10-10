From Stdlib Require Import Basics.
From Stdlib Require Import List.
From Stdlib Require Import Relations.
From Stdlib Require Import Wellfounded.

From Equations Require Import Equations.

From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import State.
From RocqSAT Require Import Rule.
From RocqSAT Require Import Trans.
From RocqSAT Require Import Measure.

(* Every transition decreases the measure. *)
Lemma trans__state_lt: forall (rs: list Rule) (m: PA) (f: CNF) (s': State),
  WellFormed (state m f) -> state m f ==>[rs] s' -> state m f >>[f] s'.
Proof.
  intros rs m f s' Hwf Htrans.
  apply trans_rule in Htrans as [r [_ Hstep]]. now apply rule_decreasing in Hstep.
Qed.

(* Thanks to Gaetan Gilbert *)
Lemma clos_trans_flip: forall {A: Type} (R: relation A) (a b: A),
  flip (clos_trans _ R) a b <-> clos_trans _ (flip R) a b.
Proof.
  split.
  - intros. induction H.
    + now apply Relation_Operators.t_step.
    + eapply t_trans.
      * apply IHclos_trans2.
      * apply IHclos_trans1.
  - intros. induction H.
    + now apply Relation_Operators.t_step.
    + eapply t_trans.
      * apply IHclos_trans2.
      * apply IHclos_trans1.
Qed.

Lemma clos_refl_trans_flip: forall {A: Type} (R: relation A) (a b: A),
  flip (clos_refl_trans _ R) a b <-> clos_refl_trans _ (flip R) a b.
Proof.
  split.
  - intros. induction H.
    + now apply rt_step.
    + apply rt_refl.
    + eapply rt_trans.
      * apply IHclos_refl_trans2.
      * apply IHclos_refl_trans1.
  - intros. induction H.
    + now apply rt_step.
    + apply rt_refl.
    + eapply rt_trans.
      * apply IHclos_refl_trans2.
      * apply IHclos_refl_trans1.
Qed.

Section WfInclusion.
  Variable A : Type.
  Variables R1 R2 : A -> A -> Prop.

  (* Variant of Acc_incl that only needs the inclusion on steps reachable from z. *)
  Lemma Acc_incl' : forall z : A, (forall x y, clos_refl_trans _ R1 y z -> R1 x y -> R2 x y) -> Acc R2 z -> Acc R1 z.
  Proof.
    intros z H.
    induction 1 as [z Hz IH].
    apply Acc_intro.
    intros y Hy.
    apply IH.
    - apply H. 2:assumption.
      constructor 2.
    - intros x z' Hz' HR.
      apply H; only 2: exact HR.
      apply rt_trans with y.
      + assumption.
      + apply rt_step;assumption.
  Qed.
End WfInclusion.

(* The formula of a state, if it has one. *)
Equations cnf (s: State): option CNF :=
cnf fail          := None;
cnf (state _ f)   := Some f.

(* Transitions from well-formed states: the measure only decreases along these. *)
Definition WellFormedTrans (rs: list Rule): relation State := fun (s s': State) => WellFormed s /\ s ==>[rs] s'.

(* A strict derivation from a well-formed state only passes through well-formed states. *)
Lemma strict_derivation_well_formed_trans: forall (rs: list Rule) (s s': State),
  s ==>+[rs] s' -> WellFormed s -> clos_trans _ (WellFormedTrans rs) s s'.
Proof.
  intros rs s s' H. apply clos_trans_t1n_iff in H.
  induction H as [x y Htrans | x y z Htrans _ IH].
  - intros Hwf. apply Relation_Operators.t_step. now split.
  - intros Hwf. apply (Relation_Operators.t_trans _ _ x y z).
    + apply Relation_Operators.t_step. now split.
    + apply IH. now apply (trans_well_formed rs x).
Qed.

(* From here on, rs is a set of rules that all keep the formula: the measure is relative to a fixed formula. *)
Section Termination.
  Context (rs: list Rule) (Hkeep: Forall (fun (r: Rule) => KeepsFormula (step r)) rs).

(* A transition from a state with a formula keeps the formula (or ends in fail) and decreases the measure. *)
Lemma to_statelt s s' :
  WellFormedTrans rs s s' ->
  match cnf s with
  | None => False
  | Some f =>
      (cnf s' = None \/ cnf s' = Some f) /\ StateLt f s' s
  end.
Proof.
  intros [Hwf H]. funelim (cnf s).
  - inversion H.
  - split.
    + destruct s'.
      * now left.
      * right. apply (trans_same_formula rs _ _ _ _ Hkeep) in H. now subst.
    + now apply (trans__state_lt rs).
Qed.

(* Variant of to_statelt for a target state with formula f. *)
Lemma to_statelt0 s s' f : cnf s' = Some f -> WellFormedTrans rs s s' -> cnf s = Some f /\ StateLt f s' s.
Proof.
  intros H H'.
  apply to_statelt in H'.
  rewrite H in H'.
  destruct (cnf s).
  - destruct H' as [[e|[=]] H']; try discriminate e.
    subst;auto.
  - contradiction H'.
Qed.

(* Variant of to_statelt for a source state with formula f. *)
Lemma to_statelt0' s s' f : cnf s = Some f -> WellFormedTrans rs s s' -> (cnf s' = None \/ cnf s' = Some f) /\ StateLt f s' s.
Proof.
  intros H H'.
  apply to_statelt in H'. rewrite H in H'. assumption.
Qed.

(* Derivations keep the formula: if a derivation ends in a state with formula f, it started there. *)
Lemma clos_nf s s' f : cnf s' = Some f -> clos_refl_trans _ (WellFormedTrans rs) s s' -> cnf s = Some f.
Proof.
  intros Hf H.
  induction H as [s s' H| s | y v x _ IHyv _ IHzy].
  - apply (to_statelt0 _ _ _ Hf) in H.
    destruct H as [H _]; exact H.
  - assumption.
  - auto.
Qed.

(* Nothing is reachable from fail except fail itself. *)
Lemma clos_nf0 s s' : cnf s = None -> clos_refl_trans _ (WellFormedTrans rs) s s' -> s = s'.
Proof.
  intros Hf H.
  induction H as [s s' H| s | y v x Hyv IHyv Hzy IHzy].
  - apply to_statelt in H. rewrite Hf in H. contradiction H.
  - reflexivity.
  - firstorder. subst. auto.
Qed.

(* Every transition reachable from a state with formula f decreases StateLt f. *)
Lemma statelt_incl x f :
  cnf x = Some f ->
  forall z y,
  clos_refl_trans _ (WellFormedTrans rs) x y ->
  WellFormedTrans rs y z ->
  StateLt f z y.
Proof.
  intros Hx z; induction 1 as [y x Hyx| x | y v x Hyv Hzv Hvx Hzx].
  - intros Hxz.
    apply (to_statelt0' _ _ _ Hx) in Hyx.
    destruct Hyx as [[e|e] Hxy].
    + apply to_statelt in Hxz. rewrite e in Hxz. contradiction Hxz.
    + apply (to_statelt0' _ _ _ e) in Hxz.
      destruct Hxz as [_ Hxz].
      assumption.
  - intros Hxz.
    apply to_statelt in Hxz. rewrite Hx in Hxz.
    destruct Hxz as [_ Hxz].
    assumption.
  - intros Hxz.
    apply Hzx. 2:assumption.
    destruct (cnf v) as [f'|] eqn:Hv.
    + pose proof (clos_nf _ _ _ Hv Hyv) as Hy.
      congruence.
    + pose proof (clos_nf0 _ _ Hv Hvx). subst.
      apply to_statelt in Hxz.
      rewrite Hv in Hxz. contradiction Hxz.
Qed.

(* No infinite sequence of transitions starts from a well-formed state with a formula. *)
Lemma trans_acc : forall s f, cnf s = Some f -> Acc (flip (WellFormedTrans rs)) s.
Proof.
  intros s f Hs. apply Acc_incl' with (R2:=StateLt f).
  2:apply state_lt_well_founded.
  intros z y Hxy Hyz.
  apply clos_refl_trans_flip in Hxy.
  apply (statelt_incl _ _ Hs); assumption.
Qed.

(* There are no infinite sequences of transitions from well-formed states (the converse relation is well-founded). *)
Lemma trans_well_founded: well_founded (flip (WellFormedTrans rs)).
Proof.
  intros s. destruct (cnf s) eqn:Hs.
  - now apply trans_acc in Hs.
  - constructor. intros s' H. apply to_statelt in H. now rewrite Hs in H.
Qed.

(* Likewise for strict derivations; Solve.v recurses on this relation. *)
Lemma strict_derivation_well_founded: well_founded (flip (clos_trans _ (WellFormedTrans rs))).
Proof.
  apply (wf_incl _ _ (clos_trans _ (flip (WellFormedTrans rs)))).
  - unfold inclusion. intros. now apply clos_trans_flip.
  - apply wf_clos_trans. apply trans_well_founded.
Qed.
End Termination.
