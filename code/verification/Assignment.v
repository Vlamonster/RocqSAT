From Stdlib Require Import List.
Import ListNotations.

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
Fixpoint split_last_decision (m: PA): option (PA * Lit) :=
match m with
| []      => None
| m ++d l => Some (m, l)
| m ++p l => split_last_decision m
end.

Lemma split_last_decision_some_iff: forall (m m': PA) (l': Lit),
  split_last_decision m = Some (m', l') <-> exists (n': PA), m = m' ++d l' ++a n' /\ NoDecisions n'.
Proof.
  intros m m' l'. split.
  - induction m as [|[l [|]] m IH]; simpl.
    + discriminate.
    + intros Hsplit. injection Hsplit as <- <-. exists []. split.
      * reflexivity.
      * intros [l'' []].
    + intros Hsplit. apply IH in Hsplit as [n' [Heq Hno_dec]]. exists (n' ++p l). split.
      * now rewrite Heq.
      * intros [l'' [Heq'|Hin]].
        -- discriminate.
        -- apply Hno_dec. now exists l''.
  - intros [n' [-> Hno_dec]]. induction n' as [|[l [|]] n' IH]; simpl.
    + reflexivity.
    + exfalso. apply Hno_dec. exists l. now left.
    + apply IH. intros [l'' Hin]. apply Hno_dec. exists l''. now right.
Qed.

Lemma split_last_decision_none_iff: forall (m: PA), split_last_decision m = None <-> NoDecisions m.
Proof.
  induction m as [|[l [|]] m IH]; simpl.
  - split.
    + intros _ [l []].
    + reflexivity.
  - split.
    + discriminate.
    + intros Hno_dec. exfalso. apply Hno_dec. exists l. now left.
  - rewrite IH. split.
    + intros Hno_dec [l' [Heq|Hin]].
      * discriminate.
      * apply Hno_dec. now exists l'.
    + intros Hno_dec [l' Hin]. apply Hno_dec. exists l'. now right.
Qed.
