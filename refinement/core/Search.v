From Stdlib Require Import SetoidList.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT.refinement Require Import Lookup.

(* The clause lists of a formula (clause_lists, ClauseOf), and deciding a literal with its last value (phase). *)

(* The elements of a clause are exactly its literals. *)
Lemma clause_elements_iff: forall (c: Clause) (l: Lit), In l (Clause.elements c) <-> l ∈ c.
Proof.
  intros c l. split.
  - intros Hin. apply Clause.elements_spec1. apply In_InA.
    + apply Clause.E.eq_equiv.
    + assumption.
  - intros Hl_in_c. apply Clause.elements_spec1 in Hl_in_c. apply InA_alt in Hl_in_c as [l' [-> Hin]].
    assumption.
Qed.

(* The literals of each clause of f, which are its clauses up to set equality. *)
Definition clause_lists (f: CNF): list (list Lit) := map Clause.elements (CNF.elements f).

Lemma in_clause_lists: forall (f: CNF) (ls: list Lit),
  In ls (clause_lists f) -> exists (c: Clause), ls = Clause.elements c /\ c ∈ f.
Proof.
  intros f ls Hin. apply in_map_iff in Hin as [c [<- Hin]]. exists c. split.
  - reflexivity.
  - apply CNF.elements_spec1. apply In_InA.
    + apply CNF.E.eq_equiv.
    + assumption.
Qed.

(* Every clause of f has the literals of a clause equal to it. *)
Lemma clause_lists_in: forall (f: CNF) (c: Clause),
  c ∈ f -> exists (c': Clause), Clause.Equal c c' /\ In (Clause.elements c') (clause_lists f).
Proof.
  intros f c Hc_in_f. apply CNF.elements_spec1, InA_alt in Hc_in_f as [c' [Heq Hin]]. exists c'. split.
  - assumption.
  - now apply in_map.
Qed.

(* ls has exactly the literals of a clause of f. *)
Definition ClauseOf (f: CNF) (ls: list Lit): Prop := exists (c: Clause), c ∈ f /\ forall (l: Lit), In l ls <-> l ∈ c.

Lemma clause_lists_clause_of: forall (f: CNF) (ls: list Lit), In ls (clause_lists f) -> ClauseOf f ls.
Proof.
  intros f ls Hin. apply in_clause_lists in Hin as [c [-> Hc_in_f]]. exists c. split.
  - assumption.
  - apply clause_elements_iff.
Qed.

(* The literals of f, without duplicates. *)
Definition formula_lits (f: CNF): Clause := CNF.fold Clause.union f Clause.empty.

Lemma formula_lits_spec: forall (f: CNF) (l: Lit), l ∈ formula_lits f <-> l ∈ f.
Proof.
  intros f l. unfold formula_lits.
  apply CNF.MP.fold_rec with (P := fun (g: CNF) (ls: Clause) => l ∈ ls <-> exists (c: Clause), l ∈ c /\ c ∈ g).
  - intros g Hempty. split.
    + intros Hl. now apply Clause.empty_spec in Hl.
    + intros [c [_ Hc_in_g]]. now apply Hempty in Hc_in_g.
  - intros c ls g g' _ _ Hadd IH. split.
    + intros Hl. apply Clause.union_spec in Hl as [Hl_in_c|Hl_in_ls].
      * exists c. split.
        -- assumption.
        -- apply Hadd. now left.
      * apply IH in Hl_in_ls as [c' [Hl_in_c' Hc'_in_g]]. exists c'. split.
        -- assumption.
        -- apply Hadd. now right.
    + intros [c' [Hl_in_c' Hc'_in_g']]. apply Clause.union_spec. apply Hadd in Hc'_in_g' as [Heq|Hc'_in_g].
      * left. now apply Heq.
      * right. apply IH. now exists c'.
Qed.

(* The literal of the atom of l with the value it last had in the phases ph, or l if it had none. *)
Definition phase (ph: Values) (l: Lit): Lit :=
match tget ph (extract l) with
| Some true  => Pos (extract l)
| Some false => Neg (extract l)
| None       => l
end.

(* The phase of l is l or ¬l. *)
Lemma phase_cases: forall (ph: Values) (l: Lit), phase ph l = l \/ phase ph l = ¬l.
Proof. intros ph [p|p]; unfold phase; simpl; destruct (tget ph p) as [[|]|]; simpl; tauto. Qed.

(* The phase of an unassigned literal is unassigned. *)
Lemma phase_undef: forall (v ph: Values) (l: Lit), lookup v l = None -> lookup v (phase ph l) = None.
Proof.
  intros v ph l Hl. destruct (phase_cases ph l) as [->| ->].
  - assumption.
  - now rewrite lookup_neg, Hl.
Qed.

(* The phase of l is a literal of f if l is. *)
Lemma phase_in: forall (ph: Values) (f: CNF) (l: Lit), l ∈ f -> phase ph l ∈ f \/ ¬(phase ph l) ∈ f.
Proof.
  intros ph f l Hl_in_f. destruct (phase_cases ph l) as [->| ->].
  - now left.
  - right. now rewrite Neg.involutive.
Qed.
