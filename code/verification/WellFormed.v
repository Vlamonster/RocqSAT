From Stdlib Require Import List.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import State.

(* No atom is assigned more than once, in either polarity. *)
Definition NoDuplicates (m: PA): Prop := NoDup (atoms m).

(* Every assigned literal belongs to the formula: it or its negation occurs in it. *)
Definition Bounded (m: PA) (f: CNF): Prop :=
  forall (l: Lit), l ∈ m -> l ∈ f \/ ¬l ∈ f.

(* The states the transition system works with: fail, and assignments without duplicates that are bounded by their formula. *)
Definition WellFormed (s: State): Prop :=
match s with
| fail      => True
| state m f => NoDuplicates m /\ Bounded m f
end.

(* NoDuplicates and Bounded only look at the literals, so the lemmas below about ⟨m, l⟩ also hold for ⟨m; l⟩. *)

Lemma nodup_cons__nodup: forall (m: PA) (l: Lit), NoDuplicates ⟨m, l⟩ -> NoDuplicates m.
Proof. intros m l Hnodup. now inversion Hnodup. Qed.

Lemma nodup_app__nodup: forall (m n: PA), NoDuplicates ⟨m ++ n⟩ -> NoDuplicates m.
Proof.
  intros m n. induction n as [|n IH l|n IH l].
  - now intros.
  - intros Hnodup. inversion Hnodup. now apply IH.
  - intros Hnodup. inversion Hnodup. now apply IH.
Qed.

Lemma bounded_cons__bounded: forall (m: PA) (f: CNF) (l: Lit), Bounded ⟨m, l⟩ f -> Bounded m f.
Proof.
  unfold Bounded. intros m f l Hbounded l' Hin. apply Hbounded. now right.
Qed.

Lemma well_formed_tail: forall (m: PA) (f: CNF) (l: Lit),
  WellFormed (state ⟨m, l⟩ f) -> WellFormed (state m f).
Proof.
  intros m f l [Hnodup Hbounded]. split.
  - now apply nodup_cons__nodup in Hnodup.
  - now apply bounded_cons__bounded in Hbounded.
Qed.

(* The literal on top of an assignment without duplicates was unassigned in the rest. *)
Lemma nodup_cons__undef: forall (m: PA) (l: Lit), NoDuplicates ⟨m, l⟩ -> Undef m l.
Proof.
  unfold NoDuplicates, Undef. intros m l Hnodup. simpl in Hnodup.
  inversion Hnodup as [|? ? Hnot_in]. destruct (l_eval m l) eqn:Hl.
  - exfalso. apply Hnot_in. apply PA.in_atoms.
    destruct (proj1 (l_eval_some_iff m l) (ex_intro _ _ Hl)) as [Hin|Hin].
    + now exists l.
    + exists (¬l). split.
      * assumption.
      * apply Neg.extract_eq. now right.
  - reflexivity.
Qed.

(* Adding an unassigned literal keeps an assignment free of duplicates. *)
Lemma nodup_cons: forall (m: PA) (l: Lit), NoDuplicates m -> Undef m l -> NoDuplicates ⟨m, l⟩.
Proof.
  unfold NoDuplicates, Undef. intros m l Hnodup Hundef. simpl. constructor.
  - intros Hin. apply PA.in_atoms in Hin as [l' [Hin Heq]].
    destruct (proj2 (l_eval_some_iff m l)) as [b Hb].
    + apply Neg.extract_eq in Heq as [<- | ->].
      * now left.
      * now right.
    + congruence.
  - assumption.
Qed.

Lemma bounded_incl: forall (m m': PA) (f: CNF),
  (forall (l: Lit), l ∈ m -> l ∈ m') -> Bounded m' f -> Bounded m f.
Proof.
  unfold Bounded. intros m m' f Hincl Hbounded l Hin.
  apply Hincl in Hin. now apply Hbounded in Hin.
Qed.

(* Adding a literal of the formula keeps an assignment bounded. *)
Lemma bounded_cons: forall (m: PA) (f: CNF) (l: Lit),
  Bounded m f -> l ∈ f \/ ¬l ∈ f -> Bounded ⟨m, l⟩ f.
Proof.
  unfold Bounded. intros m f l Hbounded Hl_in_f l' [<-|Hin].
  - assumption.
  - now apply Hbounded.
Qed.

(* Adding an unassigned literal of the formula keeps an assignment well-formed. *)
Lemma well_formed_cons: forall (m: PA) (f: CNF) (l: Lit),
  WellFormed (state m f) -> Undef m l -> l ∈ f \/ ¬l ∈ f -> WellFormed (state ⟨m, l⟩ f).
Proof.
  intros m f l [Hnodup Hbounded] Hundef Hl_in_f. split.
  - now apply nodup_cons.
  - now apply bounded_cons.
Qed.

Lemma initial_well_formed: forall (f: CNF), WellFormed (state ⟨⟩ f).
Proof.
  unfold WellFormed, NoDuplicates, Bounded. split.
  - constructor.
  - now intros.
Qed.
