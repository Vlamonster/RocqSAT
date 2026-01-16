From Equations Require Import Equations.
From Stdlib Require Import List.
From RocqSAT Require Import Lit Neg Clause.

(* A formula is a conjunction of clauses. *)
Definition CNF: Type := list Clause.

Equations l_in_f (f: CNF) (l: Lit): bool :=
l_in_f f l := existsb (fun (c: Clause) => l_in_c c l) f.

Lemma l_in_f_iff: forall (f: CNF) (l: Lit),
  l_in_f f l = true <-> exists (c: Clause), (In l c \/ In (¬l) c) /\ In c f.
Proof.
  intros. split.
  - intros. simp l_in_f in H. apply existsb_exists in H as [c [Hc_in_f Hl_in_c]].
    apply l_in_c_iff in Hl_in_c. now exists c.
  - intros. destruct H as [c [Hx_in_c Hc_in_f]]. simp l_in_f.
    apply existsb_exists. exists c. split.
    + assumption.
    + now apply l_in_c_iff.
Qed.
