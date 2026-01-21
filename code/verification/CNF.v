From Equations Require Import Equations.
From Stdlib Require Import List Bool.
From RocqSAT Require Import Lit Neg Clause.

(* A formula is a conjunction of clauses. *)
Definition CNF: Type := list Clause.

Equations l_in_f (f: CNF) (l: Lit): bool :=
l_in_f f l := existsb (fun (c: Clause) => l_in_c c l) f.

Lemma l_in_f_true_iff: forall (f: CNF) (l: Lit),
  l_in_f f l = true <-> exists (c: Clause), (In l c \/ In (¬l) c) /\ In c f.
Proof.
  intros. split.
  - intros. simp l_in_f in H. apply existsb_exists in H as [c [Hc_in_f Hl_in_c]].
    apply l_in_c_true_iff in Hl_in_c. now exists c.
  - intros. destruct H as [c [Hx_in_c Hc_in_f]]. simp l_in_f.
    apply existsb_exists. exists c. split.
    + assumption.
    + now apply l_in_c_true_iff.
Qed.

Lemma l_in_f_false_iff: forall (f: CNF) (l: Lit),
  l_in_f f l = false <-> forall (c: Clause), (~ In l c /\ ~ In (¬l) c) \/ ~ In c f.
Proof.
  intros. pose proof (l_in_f_true_iff f l). apply not_iff_compat in H. 
  rewrite not_true_iff_false in H. split.
  - intros. apply H in H0. destruct (l_in_c c l) eqn:Hl_in_c.
    + apply l_in_c_true_iff in Hl_in_c. right. unfold not. intros. apply H0. now exists c.
    + apply l_in_c_false_iff in Hl_in_c. intuition.
  - intros. apply H. unfold not. intros. destruct H1. specialize (H0 x). intuition.
Qed.
