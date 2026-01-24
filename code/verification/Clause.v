From Equations Require Import Equations.
From Stdlib Require Import List Bool.
From RocqSAT Require Import Lit Neg.

(* A clause is a disjunction of literals. *)
Definition Clause: Type := list Lit.

(* Remove a literal from a clause. *)
Equations l_remove (c: Clause) (l: Lit): Clause :=
l_remove c l := filter (fun (l': Lit) => negb (l =? l')) c.

Lemma l_remove_in_iff: forall (c: Clause) (l l': Lit),
  In l' (l_remove c l) <-> In l' c /\ l <> l'.
Proof.
  intros. split.
  - intros. simp l_remove in H. apply filter_In in H.
    rewrite negb_true_iff in H. now rewrite eqb_neq in H.
  - intros. simp l_remove. apply filter_In.
    rewrite negb_true_iff. now rewrite eqb_neq.
Qed.

Equations l_in_c (c: Clause) (l: Lit): bool :=
l_in_c c l := existsb (eqb l) c || existsb (eqb (¬l)) c.

Lemma l_in_c_true_iff: forall (c: Clause) (l: Lit),
  l_in_c c l = true <-> In l c \/ In (¬l) c.
Proof.
  intros. split.
  - intros. simp l_in_c in H. apply orb_true_iff in H as [Hl_in_c|Hnegl_in_c].
    + apply existsb_exists in Hl_in_c as [l' [Hl_in_c Heq]].
      rewrite eqb_eq in Heq. subst l'. now left.
    + apply existsb_exists in Hnegl_in_c as [l' [Hnegl_in_c Heq]].
      rewrite eqb_eq in Heq. subst l'. now right.
  - intros. simp l_in_c. apply orb_true_iff. destruct H as [Hl_in_c|Hnegl_in_c].
    + left. apply existsb_exists. exists l. intuition. apply eqb_refl.
    + right. apply existsb_exists. exists (¬l). intuition. apply eqb_refl.
Qed.

Lemma l_in_c_false_iff: forall (c: Clause) (l: Lit),
  l_in_c c l = false <-> ~ In l c /\ ~ In (¬l) c.
Proof.
  intros. pose proof (l_in_c_true_iff c l). apply not_iff_compat in H. 
  rewrite not_true_iff_false in H. intuition.
Qed.
