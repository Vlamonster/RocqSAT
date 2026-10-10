From Stdlib Require Import Logic List Bool Morphisms MSets.MSetAVL MSets.MSetEqProperties.

From RocqSAT Require Import Lit Neg.

Module LitSet := MSetAVL.Make(Lit_as_OT).
Module LitSetEqProperties := MSetEqProperties.EqProperties(LitSet).

Include LitSet.
Include LitSetEqProperties.

Module Definitions.
  (* A clause is a disjunction of literals. *)
  Definition Clause: Type := t.

  Definition l_in_c (c: Clause) (l: Lit): bool :=
  exists_ (eqb l) c || exists_ (eqb (¬l)) c.
End Definitions.

Include Definitions.

Module Lemmas.
  Lemma c_equal_exists: forall (f: Lit -> bool) (c1 c2: Clause), 
    Equal c1 c2 -> exists_ f c1 = exists_ f c2.
  Proof.
    intros f c1 c2 Heq. destruct (exists_ f c1) eqn:Hexists, (exists_ f c2) eqn:Hexists'.
    - reflexivity.
    - apply exists_spec in Hexists as [l [Hin Hf]].
      + apply Heq in Hin. assert (exists_ f c2 = true) as contra.
        * apply exists_spec.
          -- now intros ? ? ->.
          -- now exists l.
        * congruence.
      + now intros ? ? ->.
    - apply exists_spec in Hexists' as [l [Hin Hf]].
      + apply Heq in Hin. assert (exists_ f c1 = true) as contra.
        * apply exists_spec.
          -- now intros ? ? ->.
          -- now exists l.
        * congruence.
      + now intros ? ? ->.
    - reflexivity.
  Qed.

  Lemma c_equal_forall: forall (f: Lit -> bool) (c1 c2: Clause),
    Equal c1 c2 -> for_all f c1 = for_all f c2.
  Proof.
    intros f c1 c2 Heq. destruct (for_all f c1) eqn:Hforall, (for_all f c2) eqn:Hforall'.
    - reflexivity.
    - apply for_all_spec in Hforall.
      + apply for_all_mem_4 in Hforall' as [l [Hin Hf]].
        * apply mem_spec in Hin. apply Heq in Hin. apply Hforall in Hin as Hf'. congruence.
        * now intros ? ? ->.
      + now intros ? ? ->.
    - apply for_all_spec in Hforall'.
      + apply for_all_mem_4 in Hforall as [l [Hin Hf]].
        * apply mem_spec in Hin. apply Heq in Hin. apply Hforall' in Hin as Hf'. congruence.
        * now intros ? ? ->.
      + now intros ? ? ->.
    - reflexivity.
  Qed.

  Lemma l_in_c_true_iff: forall (c: Clause) (l: Lit),
    l_in_c c l = true <-> In l c \/ In (¬l) c.
  Proof.
    intros c l. split.
    - intros Hl_in_c. unfold l_in_c in Hl_in_c. apply orb_true_iff in Hl_in_c as [Hl_in_c|Hnegl_in_c].
      + left. apply exists_spec in Hl_in_c as [l' [Hin Heq]].
        * rewrite eqb_eq in Heq. now subst l'.
        * now intros ? ? ->.
      + right. apply exists_spec in Hnegl_in_c as [l' [Hin Heq]]. 
        * rewrite eqb_eq in Heq. now subst l'.
        * now intros ? ? ->.
    - intros [Hl_in_c|Hnegl_in_c].
      + unfold l_in_c. assert (exists_ (eqb l) c = true) as Hexists.
        * apply exists_spec.
          -- now intros ? ? ->.
          -- exists l. split.
            ++ assumption.
            ++ apply eqb_refl.
        * now rewrite Hexists.
      + unfold l_in_c. assert (exists_ (eqb (¬l)) c = true).
        * apply exists_spec.
          -- now intros ? ? ->.
          -- exists (¬l). split.
            ++ assumption.
            ++ apply eqb_refl.
        * rewrite H. apply orb_true_r. 
  Qed.

  Lemma l_in_c_false_iff: forall (c: Clause) (l: Lit),
    l_in_c c l = false <-> ~ In l c /\ ~ In (¬l) c.
  Proof.
    intros. pose proof (l_in_c_true_iff c l). apply not_iff_compat in H. 
    rewrite not_true_iff_false in H. intuition.
  Qed.
End Lemmas.

Include Lemmas.
