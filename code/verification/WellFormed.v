From Stdlib Require Import List.
Import ListNotations.

From Equations Require Import Equations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import State.

(* No atom is assigned more than once, in either polarity. *)
Definition NoDuplicates (m: PA): Prop := 
  NoDup (map extract (map fst m)).

(* Every assigned literal belongs to the formula: it or its negation occurs in some clause. *)
Definition Bounded (m: PA) (f: CNF): Prop := 
  forall (l: Lit) (a: Ann), In (l, a) m -> 
  exists (c: Clause), CNF.In c f /\ (Clause.In l c \/ Clause.In (¬l) c).

(* The states the transition system works with: fail, and assignments without duplicates that are bounded by their formula. *)
Definition WellFormed (s: State): Prop :=
match s with
| fail      => True
| state m f => NoDuplicates m /\ Bounded m f
end.

Lemma nodup_cons__nodup: forall (m: PA) (l: Lit) (a: Ann),
  NoDuplicates (add m l a) -> NoDuplicates m.
Proof. intros. now inversion H. Qed.
Lemma nodup_app__nodup: forall (m n: PA),
  NoDuplicates ⟨m ++ n⟩ -> NoDuplicates m.
Proof.
  induction n.
  - now intros.
  - intros. simpl in H. apply nodup_cons__nodup in H. now apply IHn.
Qed.
Lemma bounded_cons__bounded: forall (m: PA) (f: CNF) (l: Lit) (a: Ann),
  Bounded (add m l a) f -> Bounded m f.
Proof.
  unfold Bounded. intros m f l a Hbounded l' a' Hin. apply (Hbounded l' a'). now right.
Qed.
Lemma well_formed_tail: forall (m: PA) (f: CNF) (l: Lit) (a: Ann),
  WellFormed (state (add m l a) f) -> WellFormed (state m f).
Proof.
  unfold WellFormed. intros. destruct H. split.
  - now apply nodup_cons__nodup in H.
  - now apply bounded_cons__bounded in H0.
Qed.
(* The literal on top of an assignment without duplicates was unassigned in the rest. *)
Lemma nodup_cons__undef: forall (m: PA) (l: Lit) (a: Ann),
  NoDuplicates (add m l a) -> Undef m l.
Proof. 
  unfold NoDuplicates, Undef. intros. simpl in *. inversion H.
  destruct (l_eval m l) eqn:G.
  - exfalso. apply H2. apply in_map_iff.
    destruct (proj1 (l_eval_some_iff m l) (ex_intro _ _ G)) as [a' [Hin|Hin]].
    + exists l. intuition. apply in_map_iff. now exists (l, a').
    + exists (¬l). split.
      * destruct l; reflexivity.
      * apply in_map_iff. now exists (¬l, a').
  - reflexivity.
Qed.

(* Adding an unassigned literal keeps an assignment free of duplicates. *)
Lemma nodup_cons: forall (m: PA) (l: Lit) (a: Ann),
  NoDuplicates m -> Undef m l -> NoDuplicates (add m l a).
Proof.
  unfold Undef, NoDuplicates. intros. simpl. constructor.
  - unfold not. intros. funelim (l_eval m l).
    + contradiction.
    + congruence.
    + congruence.
    + simpl in *. destruct H2. 
      * destruct l, l'.
        -- simp extract in H2. subst p0. now rewrite Lit.eqb_refl in Heq0.
        -- simp extract in H2. subst p0. simp neg in Heq. now rewrite Lit.eqb_refl in Heq.
        -- simp extract in H2. subst p0. simp neg in Heq. now rewrite Lit.eqb_refl in Heq.
        -- simp extract in H2. subst p0. now rewrite Lit.eqb_refl in Heq0.
      * apply (H m l dec).
        -- now inversion H0.
        -- congruence.
        -- assumption.
        -- reflexivity.
        -- reflexivity.  
  - assumption.
Qed.

Lemma bounded_incl: forall (m m': PA) (f: CNF),
  incl m m' -> Bounded m' f -> Bounded m f.
Proof.
  unfold Bounded, incl. intros m m' f Hincl Hbounded l a Hin.
  apply Hincl in Hin. now apply Hbounded in Hin.
Qed.

(* Adding a literal of the formula keeps an assignment bounded. *)
Lemma bounded_cons: forall (m: PA) (f: CNF) (l: Lit) (a: Ann),
  Bounded m f -> l_in_f f l = true -> Bounded (add m l a) f.
Proof.
  unfold Bounded. intros m f l a Hbounded Hl_in_f l' a' Hin. 
  apply CNF.l_in_f_true_iff in Hl_in_f as [c [[Hl_in_c|Hnegl_in_c] Hc_in_f ]].
  - destruct Hin.
    + injection H as <- <-. exists c. intuition.
    + now apply Hbounded in H.
  - destruct Hin.
    + injection H as <- <-. exists c. intuition.
    + now apply Hbounded in H.
Qed.

(* Adding an unassigned literal of the formula keeps an assignment well-formed. *)
Lemma well_formed_cons: forall (m: PA) (f: CNF) (l: Lit) (a: Ann),
  WellFormed (state m f) -> Undef m l -> l_in_f f l = true -> WellFormed (state (add m l a) f).
Proof.
  intros m f l a [Hnodup Hbounded] Hundef Hl_in_f. split.
  - now apply nodup_cons.
  - now apply bounded_cons.
Qed.

Lemma initial_well_formed: forall (f: CNF), WellFormed (state ⟨⟩ f).
Proof.
  unfold WellFormed, NoDuplicates, Bounded. split.
  - constructor.
  - now intros.
Qed.
