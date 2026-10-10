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
    ClauseSet.exists_ (fun (c: Clause) => l_in_c c l) f.
  End Definitions.

  Include Definitions.

  Module Lemmas.
    Lemma l_in_f_true_iff: forall (f: CNF) (l: Lit),
      l_in_f f l = true <-> exists (c: Clause), (Clause.In l c \/ Clause.In (¬l) c) /\ ClauseSet.In c f.
    Proof.
      intros. split.
      - intros. apply ClauseSet.exists_spec in H as [c [Hc_in_f Hl_in_c]].
        + apply Clause.l_in_c_true_iff in Hl_in_c. now exists c.
        + intros c1 c2 Heq. unfold l_in_c. 
          rewrite (Clause.c_equal_exists _ c1 c2 Heq). now rewrite (Clause.c_equal_exists _ c1 c2 Heq).
      - intros. destruct H as [c [Hx_in_c Hc_in_f]]. unfold l_in_f.
        apply ClauseSet.exists_spec.
        + intros c1 c2 Heq. unfold l_in_c.
          rewrite (Clause.c_equal_exists _ c1 c2 Heq). now rewrite (Clause.c_equal_exists _ c1 c2 Heq).
        + exists c. split.
          * assumption.
          * unfold l_in_c. destruct Hx_in_c as [Hl_in_c|Hnegl_in_c].
            -- assert (Clause.exists_ (eqb l) c = true) as Hexists.
              ++ apply Clause.exists_spec.
                ** now intros ? ? ->.
                ** exists l. split.
                  --- assumption.
                  --- apply Lit.eqb_refl.
              ++ now rewrite Hexists.
            -- assert (Clause.exists_ (eqb (¬l)) c = true) as Hexists.
              ++ apply Clause.exists_spec.
                ** now intros ? ? ->.
                ** exists (¬l). split.
                  --- assumption.
                  --- apply Lit.eqb_refl.
              ++ rewrite Hexists. apply orb_true_r.
    Qed.

    Lemma l_in_f_false_iff: forall (f: CNF) (l: Lit),
      l_in_f f l = false <-> forall (c: Clause), (~ Clause.In l c /\ ~ Clause.In (¬l) c) \/ ~ ClauseSet.In c f.
    Proof.
      intros. pose proof (l_in_f_true_iff f l). apply not_iff_compat in H. 
      rewrite not_true_iff_false in H. split.
      - intros. apply H in H0. destruct (l_in_c c l) eqn:Hl_in_c.
        + apply Clause.l_in_c_true_iff in Hl_in_c. right. unfold not. intros. apply H0. now exists c.
        + apply Clause.l_in_c_false_iff in Hl_in_c. intuition.
      - intros. apply H. unfold not. intros. destruct H1. specialize (H0 x). intuition.
    Qed.
  End Lemmas.

  Include Lemmas.
End CNF.

Export CNF.Definitions.
