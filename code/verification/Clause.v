From Stdlib Require Import MSets.MSetAVL.
From Stdlib Require Import MSets.MSetEqProperties.

From RocqSAT Require Import Lit.

Module Clause.
  Include MSetAVL.Make(LitOrderType).
  Include MSetEqProperties.EqProperties.

  Module Definitions.
    (* A clause is a disjunction of literals. *)
    Abbreviation Clause := t.

    (* Print elements as literals rather than as Clause.elt. *)
    Notation "'Lit'" := elt (only printing).
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
  End Lemmas.

  Include Lemmas.
End Clause.

Export Clause.Definitions.
