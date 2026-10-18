From Stdlib Require Import Bool.
From Stdlib Require Import MSets.MSetAVL.
From Stdlib Require Import MSets.MSetEqProperties.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT.utils Require Export Member.

Module CNF.
  Include MSetAVL.Make(Clause).
  Include MSetEqProperties.EqProperties.

  Module Definitions.
    (* A formula is a conjunction of clauses. *)
    Abbreviation CNF := t.

    (* Print elements as clauses rather than as CNF.elt. *)
    Notation "'Clause'" := elt (only printing).

    #[export]
    Instance MemberCNF: Member Clause CNF := In.

    (* A literal occurs in f when it occurs in one of its clauses. *)
    #[export]
    Instance MemberLitCNF: Member Lit CNF := fun (l: Lit) (f: CNF) => exists (c: Clause), l ∈ c /\ c ∈ f.

    (* Whether l occurs in f, as a Boolean. *)
    Definition mem_lit (l: Lit) (f: CNF): bool := CNF.exists_ (fun (c: Clause) => Clause.mem l c) f.
  End Definitions.

  Include Definitions.

  Module Lemmas.
    Lemma mem_lit_spec: forall (f: CNF) (l: Lit), mem_lit l f = true <-> l ∈ f.
    Proof.
      intros f l. unfold mem_lit. rewrite CNF.exists_spec.
      - split.
        + intros [c [Hc_in_f Hl_mem]]. exists c. split.
          * now apply Clause.mem_spec.
          * assumption.
        + intros [c [Hl_in_c Hc_in_f]]. exists c. split.
          * assumption.
          * now apply Clause.mem_spec.
      - intros c1 c2 Heq. now rewrite Heq.
    Qed.

    Lemma not_mem_lit_iff: forall (f: CNF) (l: Lit), l ∉ f <-> mem_lit l f = false.
    Proof. intros f l. now rewrite <- not_true_iff_false, mem_lit_spec. Qed.
  End Lemmas.

  Include Lemmas.
End CNF.

Export CNF.Definitions.
