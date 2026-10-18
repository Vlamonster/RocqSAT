From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.

(* m is a model of f. *)
Definition Model (m: PA) (f: CNF): Prop := f_eval m f = Some true.

(* A literal as a formula: the single unit clause {l}. *)
Definition unit_cnf (l: Lit): CNF := CNF.singleton (Clause.singleton l).

(* An assignment as a formula: one unit clause per assigned literal. *)
Fixpoint units (m: PA): CNF :=
match m with
| ⟨⟩     => CNF.empty
| ⟨m, l⟩ => CNF.add (Clause.singleton l) (units m)
| ⟨m; l⟩ => CNF.add (Clause.singleton l) (units m)
end.

Lemma model_union_iff: forall (m: PA) (f g: CNF), Model m (CNF.union f g) <-> Model m f /\ Model m g.
Proof.
  intros m f g. unfold Model. rewrite !f_eval_true_iff. split.
  - intros H. split.
    + intros c Hc. apply H. apply CNF.union_spec. now left.
    + intros c Hc. apply H. apply CNF.union_spec. now right.
  - intros [Hf Hg] c Hc. apply CNF.union_spec in Hc as [Hc|Hc].
    + now apply Hf.
    + now apply Hg.
Qed.

Lemma model_unit_cnf_iff: forall (m: PA) (l: Lit), Model m (unit_cnf l) <-> l_eval m l = Some true.
Proof.
  intros m l. unfold Model, unit_cnf. rewrite f_eval_true_iff. split.
  - intros H. apply (c_eval_singleton_true_iff m (Clause.singleton l)).
    + reflexivity.
    + apply H. now apply CNF.singleton_spec.
  - intros Hl c Hc. apply CNF.singleton_spec in Hc. now apply (c_eval_singleton_true_iff m c l).
Qed.

(* Adding the unit clause {l} to a formula adds the requirement that l is true. *)
Lemma model_add_unit_iff: forall (m: PA) (f: CNF) (l: Lit),
  Model m (CNF.add (Clause.singleton l) f) <-> l_eval m l = Some true /\ Model m f.
Proof.
  intros m f l. unfold Model. rewrite !f_eval_true_iff. split.
  - intros H. split.
    + apply (c_eval_singleton_true_iff m (Clause.singleton l)).
      * reflexivity.
      * apply H. apply CNF.add_spec. now left.
    + intros c Hc. apply H. apply CNF.add_spec. now right.
  - intros [Hl Hf] c Hc. apply CNF.add_spec in Hc as [Hc|Hc].
    + now apply (c_eval_singleton_true_iff m c l Hc).
    + now apply Hf.
Qed.

(* A clause as a formula is true exactly when the clause is. *)
Lemma model_singleton_iff: forall (m: PA) (c: Clause), Model m (CNF.singleton c) <-> c_eval m c = Some true.
Proof.
  intros m c. unfold Model. rewrite f_eval_true_iff. split.
  - intros H. apply H. now apply CNF.singleton_spec.
  - intros Hc c' Hc'. apply CNF.singleton_spec in Hc'. rewrite c_eval_true_iff in *.
    destruct Hc as [l [Hl_in_c Hl]]. exists l. split.
    + now apply Hc'.
    + assumption.
Qed.

(* m satisfies the unit clauses of m' exactly when it makes every literal of m' true. *)
Lemma model_units_iff: forall (m m': PA),
  Model m (units m') <-> forall (l: Lit), l ∈ m' -> l_eval m l = Some true.
Proof.
  intros m m'. induction m' as [|m' IH l|m' IH l]; simpl.
  - split.
    + intros _ l [].
    + intros _. unfold Model. rewrite f_eval_true_iff. intros c Hc. now apply CNF.empty_spec in Hc.
  - rewrite model_add_unit_iff, IH. split.
    + intros [Hl Hall] l' [<-|Hin].
      * assumption.
      * now apply Hall.
    + intros Hall. split.
      * apply Hall. now left.
      * intros l' Hin. apply Hall. now right.
  - rewrite model_add_unit_iff, IH. split.
    + intros [Hl Hall] l' [<-|Hin].
      * assumption.
      * now apply Hall.
    + intros Hall. split.
      * apply Hall. now left.
      * intros l' Hin. apply Hall. now right.
Qed.

(* Assigning l keeps a model of f a model, as long as ¬l does not occur in f. *)
Lemma model_cons: forall (m: PA) (f: CNF) (l: Lit), ¬l ∉ f -> Model m f -> Model ⟨m, l⟩ f.
Proof.
  unfold Model. intros m f l Hnegl Hm. rewrite f_eval_true_iff in *. intros c Hc_in_f.
  apply Hm in Hc_in_f as Hc. rewrite c_eval_true_iff in *. destruct Hc as [l' [Hl'_in_c Hl']].
  exists l'. split.
  - assumption.
  - apply l_eval_cons_true.
    + intros ->. apply Hnegl. now exists c.
    + assumption.
Qed.

(* A model of the units of m' makes every literal false that m' makes false. *)
Lemma units_transfer_l: forall (m m': PA) (l: Lit),
  Model m (units m') -> l_eval m' l = Some false -> l_eval m l = Some false.
Proof.
  intros m m' l Hm Hl. apply l_eval_neg_some_iff. simpl. rewrite model_units_iff in Hm.
  apply l_eval_false_in in Hl. now apply Hm in Hl.
Qed.

(* Hence it also makes every clause false that m' makes false. *)
Lemma units_transfer_c: forall (m m': PA) (c: Clause),
  Model m (units m') -> c_eval m' c = Some false -> c_eval m c = Some false.
Proof.
  intros m m' c Hm Hc. apply c_eval_false_iff. intros l Hin.
  rewrite c_eval_false_iff in Hc. apply Hc in Hin.
  now apply (units_transfer_l _ m').
Qed.

(* And every formula. *)
Lemma units_transfer_f: forall (m m': PA) (f: CNF),
  Model m (units m') -> f_eval m' f = Some false -> f_eval m f = Some false.
Proof.
  intros m m' f Hm Hf. rewrite f_eval_false_iff in *. destruct Hf as [c [Hin Hc]].
  exists c. split.
  - assumption.
  - now apply (units_transfer_c m m').
Qed.

(* The negation of an assignment as a clause: the negations of its literals. *)
Fixpoint neg_clause (m: PA): Clause :=
match m with
| ⟨⟩     => Clause.empty
| ⟨m, l⟩ => Clause.add (¬l) (neg_clause m)
| ⟨m; l⟩ => Clause.add (¬l) (neg_clause m)
end.

Lemma neg_clause_spec: forall (m: PA) (l: Lit), l ∈ neg_clause m <-> ¬l ∈ m.
Proof.
  intros m l. induction m as [|m IH l'|m IH l']; cbn.
  - split.
    + intros Hin. now apply Clause.empty_spec in Hin.
    + intros [].
  - rewrite Clause.add_spec, IH. split.
    + intros [->|Hin].
      * left. now rewrite Neg.involutive.
      * now right.
    + intros [->|Hin].
      * left. now rewrite Neg.involutive.
      * now right.
  - rewrite Clause.add_spec, IH. split.
    + intros [->|Hin].
      * left. now rewrite Neg.involutive.
      * now right.
    + intros [->|Hin].
      * left. now rewrite Neg.involutive.
      * now right.
Qed.

(* Semantic consequence: every model of f is a model of g. *)
Definition Consequence (f g: CNF): Prop := forall (m: PA), Model m f -> Model m g.

Notation "f ⊨ g" := (Consequence f g) (at level 70).

(* Equivalence: f and g have the same models. *)
Definition Equivalent (f g: CNF): Prop := f ⊨ g /\ g ⊨ f.

Lemma equivalent_refl: forall (f: CNF), Equivalent f f.
Proof. intros f. split; now intros m. Qed.

Lemma equivalent_sym: forall (f g: CNF), Equivalent f g -> Equivalent g f.
Proof. intros f g [Hfg Hgf]. now split. Qed.

Lemma equivalent_trans: forall (f g h: CNF), Equivalent f g -> Equivalent g h -> Equivalent f h.
Proof.
  intros f g h [Hfg Hgf] [Hgh Hhg]. split.
  - intros m Hm. apply Hgh. now apply Hfg.
  - intros m Hm. apply Hgf. now apply Hhg.
Qed.

(* Replacing part of a union by an equivalent formula keeps its models. *)
Lemma model_union_equivalent: forall (m: PA) (f f' g: CNF),
  Equivalent f f' -> Model m (CNF.union f g) <-> Model m (CNF.union f' g).
Proof.
  intros m f f' g [Hff' Hf'f]. rewrite !model_union_iff. split.
  - intros [Hf Hg]. split.
    + now apply Hff'.
    + assumption.
  - intros [Hf' Hg]. split.
    + now apply Hf'f.
    + assumption.
Qed.
