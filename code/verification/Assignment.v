From Stdlib Require Import List.
Import ListNotations.

From Equations Require Import Equations.

From RocqSAT Require Import Lit.

(* An annotation on a literal (Lit * Ann) describing how its value was assigned. *)
Inductive Ann: Type :=
| dec
| prop.

(* A partial assignment for annotated literals. Evaluation is defined in Evaluation.v. *)
Definition PA: Type := list (Lit * Ann).

Declare Scope pa_scope.
Notation "m ++a n" := (n ++ m) (at level 54, left associativity): pa_scope.
Notation "m ++d l" := ((l, dec) :: m) (at level 54, left associativity): pa_scope.
Notation "m ++p l" := ((l, prop) :: m) (at level 54, left associativity): pa_scope.
Open Scope pa_scope.

(* An assignment without decision literals. *)
Definition NoDecisions (m: PA): Prop := ~ exists (l: Lit), In (l, dec) m.

(* Splits off the most recent decision literal, if any. *)
Equations split_last_decision (m: PA): option (PA * Lit) :=
split_last_decision [] := None;
split_last_decision (m ++d l) := Some (m, l);
split_last_decision (m ++p l) := split_last_decision m.

(* If l' is the most recent decision in m, then m is m' ++d l' followed by literals that are all propagations. *)
Lemma split_decomp: forall (m m': PA) (l': Lit),
  split_last_decision m = Some (m', l') -> exists (n': PA), m = m' ++d l' ++a n' /\ NoDecisions n'.
Proof.
  unfold NoDecisions. unfold not. intros. funelim (split_last_decision m).
  - discriminate.
  - rewrite <- Heqcall in H. injection H as <- <-. exists []. intuition. now destruct H.
  - rewrite <- Heqcall in H0. destruct (H m' l' H0). destruct H1. rewrite H1. exists (x ++p l).
    intuition. apply H2. destruct H3. destruct H3.
    + discriminate.
    + now exists x0.
Qed.

Lemma split_none_iff: forall (m: PA), split_last_decision m = None <-> NoDecisions m.
Proof. 
  unfold NoDecisions. unfold not. intros. split.
  - intros. funelim (split_last_decision m).
    + destruct H0. destruct H0.
    + discriminate.
    + destruct H1. destruct H1.
      * discriminate.
      * apply (H m H0).
        -- now exists x.
        -- reflexivity.
        -- reflexivity.
  - intros. funelim (split_last_decision m).
    + reflexivity.
    + exfalso. apply H. exists l. now left.
    + apply H. intros. apply H0. destruct H1. exists x. now right.
Qed.
