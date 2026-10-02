From Equations Require Import Equations.
From Stdlib Require Import List Bool Morphisms MSets.MSetAVL MSets.MSetEqProperties.
From RocqSAT Require Import Lit Neg.

Module LitSet := MSetAVL.Make(Lit_as_OT).
Module LitSetEqProperties := MSetEqProperties.EqProperties(LitSet).

(* A clause is a disjunction of literals. *)
Definition Clause: Type := LitSet.t.

Lemma c_equal_exists: forall (f: Lit -> bool) (c1 c2: Clause), 
  LitSet.Equal c1 c2 -> LitSet.exists_ f c1 = LitSet.exists_ f c2.
Proof.
  intros f c1 c2 Heq. destruct (LitSet.exists_ f c1) eqn:Hexists, (LitSet.exists_ f c2) eqn:Hexists'.
  - reflexivity.
  - apply LitSet.exists_spec in Hexists as [l [Hin Hf]].
    + apply Heq in Hin. assert (LitSet.exists_ f c2 = true) as contra.
      * apply LitSet.exists_spec.
        -- now intros ? ? ->.
        -- now exists l.
      * congruence.
    + now intros ? ? ->.
  - apply LitSet.exists_spec in Hexists' as [l [Hin Hf]].
    + apply Heq in Hin. assert (LitSet.exists_ f c1 = true) as contra.
      * apply LitSet.exists_spec.
        -- now intros ? ? ->.
        -- now exists l.
      * congruence.
    + now intros ? ? ->.
  - reflexivity.
Qed.

Lemma c_equal_forall: forall (f: Lit -> bool) (c1 c2: Clause),
  LitSet.Equal c1 c2 -> LitSet.for_all f c1 = LitSet.for_all f c2.
Proof.
  intros f c1 c2 Heq. destruct (LitSet.for_all f c1) eqn:Hforall, (LitSet.for_all f c2) eqn:Hforall'.
  - reflexivity.
  - apply LitSet.for_all_spec in Hforall.
    + apply LitSetEqProperties.for_all_mem_4 in Hforall' as [l [Hin Hf]].
      * apply LitSet.mem_spec in Hin. apply Heq in Hin. apply Hforall in Hin as Hf'. congruence.
      * now intros ? ? ->.
    + now intros ? ? ->.
  - apply LitSet.for_all_spec in Hforall'.
    + apply LitSetEqProperties.for_all_mem_4 in Hforall as [l [Hin Hf]].
      * apply LitSet.mem_spec in Hin. apply Heq in Hin. apply Hforall' in Hin as Hf'. congruence.
      * now intros ? ? ->.
    + now intros ? ? ->.
  - reflexivity.
Qed.

Definition l_in_c (c: Clause) (l: Lit): bool :=
LitSet.exists_ (eqb l) c || LitSet.exists_ (eqb (¬l)) c.

Lemma l_in_c_true_iff: forall (c: Clause) (l: Lit),
  l_in_c c l = true <-> LitSet.In l c \/ LitSet.In (¬l) c.
Proof.
  intros c l. split.
  - intros Hl_in_c. unfold l_in_c in Hl_in_c. apply orb_true_iff in Hl_in_c as [Hl_in_c|Hnegl_in_c].
    + left. apply LitSet.exists_spec in Hl_in_c as [l' [Hin Heq]].
      * rewrite eqb_eq in Heq. now subst l'.
      * now intros ? ? ->.
    + right. apply LitSet.exists_spec in Hnegl_in_c as [l' [Hin Heq]]. 
      * rewrite eqb_eq in Heq. now subst l'.
      * now intros ? ? ->.
  - intros [Hl_in_c|Hnegl_in_c].
    + unfold l_in_c. assert (LitSet.exists_ (eqb l) c = true) as Hexists.
      * apply LitSet.exists_spec.
        -- now intros ? ? ->.
        -- exists l. split.
          ++ assumption.
          ++ apply eqb_refl.
      * now rewrite Hexists.
    + unfold l_in_c. assert (LitSet.exists_ (eqb (¬l)) c = true).
      * apply LitSet.exists_spec.
        -- now intros ? ? ->.
        -- exists (¬l). split.
          ++ assumption.
          ++ apply eqb_refl.
      * rewrite H. apply orb_true_r. 
Qed.

Lemma l_in_c_false_iff: forall (c: Clause) (l: Lit),
  l_in_c c l = false <-> ~ LitSet.In l c /\ ~ LitSet.In (¬l) c.
Proof.
  intros. pose proof (l_in_c_true_iff c l). apply not_iff_compat in H. 
  rewrite not_true_iff_false in H. intuition.
Qed.
