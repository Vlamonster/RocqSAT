From Stdlib Require Import Basics.
From Stdlib Require Import Relations.
From Stdlib Require Import Wellfounded.
From Stdlib Require Import Lia.

From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import State.
From RocqSAT Require Import Rule.
From RocqSAT Require Import Trans.
From RocqSAT Require Import Measure.
From RocqSAT.utils Require Import Invariant.

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

(* A transition from a well-formed state never increases the largest atom of the formula. *)
Lemma trans_max_atom: forall (rs: list Rule) (m m': PA) (f f': CNF),
  WellFormed (state m f) -> state m f ==>[rs] state m' f' -> max_atom_f f' <= max_atom_f f.
Proof.
  intros rs m m' f f' Hwf Htrans. apply trans__state_lt in Htrans.
  - now apply state_lt_max_atom in Htrans.
  - assumption.
Qed.

(* Hence the largest atom of the formula stays bounded along transitions from well-formed states. *)
Lemma max_atom_invariant: forall (rs: list Rule) (f: CNF) (s s': State),
  clos_refl_trans _ (WellFormedTrans rs) s s' ->
  match s with fail => True | state _ g => max_atom_f g <= max_atom_f f end ->
  match s' with fail => True | state _ g => max_atom_f g <= max_atom_f f end.
Proof.
  intros rs f. apply clos_refl_trans_invariant.
  intros [|m g] [|m' g'] [Hwf Htrans] Hle.
  - easy.
  - inversion Htrans.
  - easy.
  - apply trans_max_atom in Htrans.
    + lia.
    + assumption.
Qed.

(* There are no infinite sequences of transitions from well-formed states (the converse relation is well-founded): every step decreases StateLt f for the formula f of the starting state. *)
Lemma trans_well_founded: forall (rs: list Rule), well_founded (flip (WellFormedTrans rs)).
Proof.
  intros rs [|m f].
  - constructor. intros s [_ Htrans]. inversion Htrans.
  - apply Acc_incl' with (R2 := StateLt f).
    + intros s' s Hreach [Hwf Htrans]. destruct s as [|m' f'].
      * inversion Htrans.
      * apply clos_refl_trans_flip in Hreach. apply max_atom_invariant with (f := f) in Hreach.
        -- apply state_lt_incl with f'.
          ++ assumption.
          ++ now apply trans__state_lt in Htrans.
        -- apply le_n.
    + apply state_lt_well_founded.
Qed.

(* Likewise for strict derivations, so a solver that takes strict derivation steps terminates. *)
Lemma strict_derivation_well_founded: forall (rs: list Rule), well_founded (flip (clos_trans _ (WellFormedTrans rs))).
Proof.
  intros rs. apply (wf_incl _ _ (clos_trans _ (flip (WellFormedTrans rs)))).
  - unfold inclusion. intros. now apply clos_trans_flip.
  - apply wf_clos_trans. apply trans_well_founded.
Qed.
