From Stdlib Require Import Arith.

From RocqSAT Require Export EqB.

Module Atom.
  Module Definitions.
    (* Atoms are propositional symbols mapped to the naturals. *)
    Definition Atom: Type := nat.

    #[export]
    Instance EqBAtom: EqB Atom := Nat.eqb.
  End Definitions.

  Include Definitions.

  Module Lemmas.
    Lemma eqb_refl: forall (p: Atom), (p =? p) = true.
    Proof. apply Nat.eqb_refl. Qed.

    Lemma eqb_sym: forall (p1 p2: Atom), (p1 =? p2) = (p2 =? p1).
    Proof. apply Nat.eqb_sym. Qed.

    Lemma eqb_eq: forall (p1 p2: Atom), (p1 =? p2) = true <-> p1 = p2.
    Proof. apply Nat.eqb_eq. Qed.
  End Lemmas.

  Include Lemmas.
End Atom.

Export Atom.Definitions.
