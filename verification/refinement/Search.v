From Stdlib Require Import Bool.
From Stdlib Require Import SetoidList.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Evaluation.
From RocqSAT.refinement Require Import Lookup.

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

(* The literals ls from the first one without a value on. *)
Fixpoint skip_assigned (v: Values) (ls: list Lit): list Lit :=
match ls with
| []       => []
| l :: ls' => if lookup_undef v l then ls else skip_assigned v ls'
end.

(* The literals ls to decide on: they are literals of f, and include every literal of f without a value. *)
Definition Cursor (v: Values) (f: CNF) (ls: list Lit): Prop :=
  (forall (l: Lit), In l ls -> l ∈ f) /\ (forall (l: Lit), l ∈ f -> lookup v l = None -> In l ls).

(* A cursor depends only on the values of literals. *)
Lemma cursor_ext: forall (v v': Values) (f: CNF) (ls: list Lit),
  (forall (l: Lit), lookup v l = lookup v' l) -> Cursor v f ls -> Cursor v' f ls.
Proof.
  intros v v' f ls Hext [Hsound Hcomplete]. split.
  - assumption.
  - intros l Hl_in_f Hl. apply Hcomplete.
    + assumption.
    + now rewrite Hext.
Qed.

Lemma skip_assigned_cursor: forall (v: Values) (f: CNF) (ls: list Lit),
  Cursor v f ls -> Cursor v f (skip_assigned v ls).
Proof.
  intros v f ls. induction ls as [|l ls IH]; simpl.
  - easy.
  - intros [Hsound Hcomplete]. unfold lookup_undef. destruct (lookup v l) as [b|] eqn:Hl.
    + apply IH. split.
      * intros l' Hl'. apply Hsound. now right.
      * intros l' Hl'_in_f Hl'. destruct (Hcomplete l' Hl'_in_f Hl') as [<-|Hin].
        -- congruence.
        -- assumption.
    + now split.
Qed.

(* The first literal after skipping has no value. *)
Lemma skip_assigned_head: forall (v: Values) (ls ls': list Lit) (l: Lit),
  skip_assigned v ls = l :: ls' -> lookup v l = None.
Proof.
  intros v ls ls' l. induction ls as [|l0 ls IH]; simpl.
  - discriminate.
  - unfold lookup_undef. destruct (lookup v l0) eqn:Hl0.
    + assumption.
    + intros Heq. injection Heq as <- _. assumption.
Qed.

(* Assigning a literal keeps a cursor valid: literals without a value had none before. *)
Lemma cursor_set_value: forall (v: Values) (f: CNF) (ls: list Lit) (l: Lit),
  Cursor v f ls -> Cursor (set_value v l) f ls.
Proof.
  intros v f ls l [Hsound Hcomplete]. split.
  - assumption.
  - intros l' Hl'_in_f Hl'. apply Hcomplete.
    + assumption.
    + rewrite lookup_add in Hl'. unfold l_eval_step in Hl'.
      destruct (l' =? l).
      * discriminate.
      * destruct (l' =? ¬l).
        -- discriminate.
        -- assumption.
Qed.
