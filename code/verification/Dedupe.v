From Equations Require Import Equations.
From Stdlib Require Import Nat Arith List.
Import ListNotations.

(* The following has to be wrapped in a section due to a bug in Equations. *)
Section dedupe_by.
  Context {A: Type} (eq: A -> A -> bool).

  Equations neqb_of (l l': A): bool :=
  neqb_of a b := negb (eq a b).

  Equations dedupe_by (m: list A): list A by wf (length m) lt :=
  dedupe_by []       := [];
  dedupe_by (l :: m) := l :: dedupe_by (filter (neqb_of l) m).
  Next Obligation.
    eapply Nat.le_lt_trans.
    - apply filter_length_le.
    - auto with arith.
  Qed.
End dedupe_by.

Lemma incl_dedupe {A: Type} (eq: A -> A -> bool) (l: list A):
  incl (dedupe_by eq l) l.
Proof.
  unfold incl. funelim (dedupe_by eq l); simp dedupe_by; cbn.
  intros a [Heq | H0].
  - rewrite Heq. left; reflexivity.
  - specialize (H _ H0). apply filter_In in H as [Inal eqa].
    right; assumption.
Qed.
