From Stdlib Require Import Bool.
From Stdlib Require Import MSets.MSetAVL.
From Stdlib Require Import MSets.MSetEqProperties.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.

Module CNF.
  Module ClauseSet := MSetAVL.Make(Clause).
  Module ClauseSetEqProperties := MSetEqProperties.EqProperties(ClauseSet).

  Include ClauseSet.
  Include ClauseSetEqProperties.

  Module Definitions.
    (* A formula is a conjunction of clauses. *)
    Definition CNF := ClauseSet.t.

    Definition l_in_f (f: CNF) (l: Lit): bool :=
    ClauseSet.exists_ (fun (c: Clause) => Clause.mem l c || Clause.mem (¬l) c) f.
  End Definitions.

  Include Definitions.

  Module Lemmas.
    Lemma l_in_f_true_iff: forall (f: CNF) (l: Lit),
      l_in_f f l = true <-> exists (c: Clause), (Clause.In l c \/ Clause.In (¬l) c) /\ ClauseSet.In c f.
    Proof.
      intros. unfold l_in_f. rewrite ClauseSet.exists_spec.
      - split.
        + intros [c [Hc_in_f Hmem]]. exists c. split.
          * apply orb_true_iff in Hmem as [Hl_mem|Hnegl_mem].
            -- left. now apply Clause.mem_spec.
            -- right. now apply Clause.mem_spec.
          * assumption.
        + intros [c [[Hl_in_c|Hnegl_in_c] Hc_in_f]].
          * exists c. split.
            -- assumption.
            -- apply orb_true_iff. left. now apply Clause.mem_spec.
          * exists c. split.
            -- assumption.
            -- apply orb_true_iff. right. now apply Clause.mem_spec.
      - intros c1 c2 Heq. now rewrite Heq.
    Qed.

    Lemma l_in_f_false_iff: forall (f: CNF) (l: Lit),
      l_in_f f l = false <-> forall (c: Clause), (~ Clause.In l c /\ ~ Clause.In (¬l) c) \/ ~ ClauseSet.In c f.
    Proof.
      intros. pose proof (l_in_f_true_iff f l). apply not_iff_compat in H. 
      rewrite not_true_iff_false in H. split.
      - intros. apply H in H0. destruct (Clause.mem l c || Clause.mem (¬l) c) eqn:Hmem.
        + right. unfold not. intros. apply H0. exists c. split.
          * apply orb_true_iff in Hmem as [Hl_mem|Hnegl_mem].
            -- left. now apply Clause.mem_spec.
            -- right. now apply Clause.mem_spec.
          * assumption.
        + left. apply orb_false_iff in Hmem as [Hl_mem Hnegl_mem]. split.
          * unfold not. intros Hl_in_c. apply Clause.mem_spec in Hl_in_c. congruence.
          * unfold not. intros Hnegl_in_c. apply Clause.mem_spec in Hnegl_in_c. congruence.
      - intros. apply H. unfold not. intros. destruct H1. specialize (H0 x). intuition.
    Qed.
  End Lemmas.

  Include Lemmas.
End CNF.

Export CNF.Definitions.
