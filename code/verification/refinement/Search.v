From Stdlib Require Import Bool.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT.refinement Require Import Lookup.

(* Some clause of f that is false under v, if there is one. *)
Definition find_conflict (v: Values) (f: CNF): option Clause :=
CNF.choose (CNF.filter (c_lookup_false v) f).

Lemma find_conflict_c_in_f: forall (m: PA) (f: CNF) (c: Clause), 
  find_conflict (values m) f = Some c -> c ∈ f.
Proof.
  intros m f c Hfind. unfold find_conflict in Hfind. apply CNF.choose_spec1 in Hfind.
  apply CNF.filter_spec in Hfind as [Hc_in_f _].
  - assumption.
  - intros c1 c2 Heq. now apply c_lookup_false_equal.
Qed.

Lemma find_conflict_conflicting: forall (m: PA) (f: CNF) (c: Clause), 
  find_conflict (values m) f = Some c -> c_eval m c = Some false.
Proof.
  intros m f c Hfind. unfold find_conflict in Hfind. apply CNF.choose_spec1 in Hfind.
  apply CNF.filter_spec in Hfind as [_ Hc].
  - rewrite c_lookup_false_values in Hc. unfold c_false in Hc. destruct (c_eval m c) as [[|]|]; easy.
  - intros c1 c2 Heq. now apply c_lookup_false_equal.
Qed.

Lemma find_conflict_exists_iff: forall (m: PA) (f: CNF),
  (exists (c: Clause), find_conflict (values m) f = Some c) <-> exists (c: Clause), c ∈ f /\ c_eval m c = Some false.
Proof.
  intros m f. split.
  - intros [c Hfind]. exists c. split.
    + now apply find_conflict_c_in_f in Hfind.
    + now apply find_conflict_conflicting in Hfind.
  - intros [c [Hc_in_f Hc]]. unfold find_conflict.
    destruct (CNF.choose (CNF.filter (c_lookup_false (values m)) f)) as [c'|] eqn:Hchoose.
    + now exists c'.
    + apply CNF.choose_spec2 in Hchoose. exfalso. apply (Hchoose c). apply CNF.filter_spec.
      * intros c1 c2 Heq. now apply c_lookup_false_equal.
      * split.
        -- assumption.
        -- rewrite c_lookup_false_values. unfold c_false. now rewrite Hc.
Qed.

(* A literal of c that is unassigned while the rest of c is false, i.e. the unit literal if c is a unit clause. *)
Definition find_unit_l (v: Values) (c: Clause): option Lit :=
Clause.choose (Clause.filter (fun (l: Lit) => lookup_undef v l && c_lookup_false v (Clause.remove l c)) c).

(* The first clause of f that is a unit clause, together with its unit literal. *)
Definition find_unit (v: Values) (f: CNF): option (Clause * Lit) :=
CNF.fold (fun (c: Clause) (r: option (Clause * Lit)) =>
  match r with
  | Some p => Some p
  | None   => option_map (pair c) (find_unit_l v c)
  end) f None.

Lemma find_unit_decomp: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  find_unit (values m) f = Some (c, l) -> find_unit_l (values m) c = Some l /\ c ∈ f.
Proof.
  intros m f c l. unfold find_unit. apply CNF.MP.fold_rec_nodep.
  - discriminate.
  - intros c' r Hc'_in_f IH Hr. destruct r as [p|].
    + now apply IH.
    + destruct (find_unit_l (values m) c') as [l'|] eqn:Hfind.
      * simpl in Hr. injection Hr as <- <-. now split.
      * discriminate.
Qed.

Lemma find_unit_undef: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  find_unit (values m) f = Some (c, l) -> Undef m l.
Proof.
  intros m f c l Hfind. apply find_unit_decomp in Hfind as [Hfind _].
  unfold find_unit_l in Hfind. apply Clause.choose_spec1 in Hfind.
  apply Clause.filter_spec in Hfind as [_ Hl].
  - apply andb_true_iff in Hl as [Hundef _]. rewrite lookup_undef_values in Hundef. unfold Undef. unfold l_undef in Hundef.
    destruct (l_eval m l); easy.
  - now intros ? ? ->.
Qed.

Lemma find_unit_l_l_in_c: forall (m: PA) (c: Clause) (l: Lit),
  find_unit_l (values m) c = Some l -> l ∈ c.
Proof.
  intros m c l Hfind. unfold find_unit_l in Hfind. apply Clause.choose_spec1 in Hfind.
  apply Clause.filter_spec in Hfind as [Hl_in_c _].
  - assumption.
  - now intros ? ? ->.
Qed.

Lemma find_unit_l_in_c: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  find_unit (values m) f = Some (c, l) -> l ∈ c.
Proof.
  intros m f c l Hfind. apply find_unit_decomp in Hfind as [Hfind _].
  now apply find_unit_l_l_in_c in Hfind.
Qed.

Lemma find_unit_c_in_f: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  find_unit (values m) f = Some (c, l) -> c ∈ f.
Proof. intros m f c l Hfind. now apply find_unit_decomp in Hfind. Qed.

Lemma find_unit_bounded: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  find_unit (values m) f = Some (c, l) -> l ∈ f.
Proof.
  intros m f c l Hfind. exists c. split.
  - now apply find_unit_l_in_c in Hfind.
  - now apply find_unit_c_in_f in Hfind.
Qed.

(* Some literal of c without a value. *)
Definition find_undef_l (v: Values) (c: Clause): option Lit :=
Clause.choose (Clause.filter (lookup_undef v) c).

Lemma find_undef_l_in_c: forall (m: PA) (c: Clause) (l: Lit), 
  find_undef_l (values m) c = Some l -> l ∈ c.
Proof.
  intros m c l Hfind. unfold find_undef_l in Hfind. apply Clause.choose_spec1 in Hfind.
  apply Clause.filter_spec in Hfind as [Hl_in_c _].
  - assumption.
  - now intros ? ? ->.
Qed.

Lemma find_undef_l_undef: forall (m: PA) (c: Clause) (l: Lit), 
  find_undef_l (values m) c = Some l -> Undef m l.
Proof.
  intros m c l Hfind. unfold find_undef_l in Hfind. apply Clause.choose_spec1 in Hfind.
  apply Clause.filter_spec in Hfind as [_ Hundef].
  - rewrite lookup_undef_values in Hundef. unfold Undef. unfold l_undef in Hundef. destruct (l_eval m l); easy.
  - now intros ? ? ->.
Qed.
Lemma find_undef_l_exists : forall (m: PA) (c: Clause) (l: Lit),
  l ∈ c -> Undef m l -> exists (l': Lit), find_undef_l (values m) c = Some l'.
Proof.
  intros m c l Hl_in_c Hundef. unfold find_undef_l.
  destruct (Clause.choose (Clause.filter (lookup_undef (values m)) c)) as [l'|] eqn:Hchoose.
  - now exists l'.
  - apply Clause.choose_spec2 in Hchoose. exfalso. apply (Hchoose l). apply Clause.filter_spec.
    + now intros ? ? ->.
    + split.
      * assumption.
      * rewrite lookup_undef_values. unfold l_undef. unfold Undef in Hundef. now rewrite Hundef.
Qed.

(* Some literal of f without a value, taken from the first clause that has one. *)
Definition find_decision (v: Values) (f: CNF): option Lit :=
CNF.fold (fun (c: Clause) (r: option Lit) =>
  match r with
  | Some l => Some l
  | None   => find_undef_l v c
  end) f None.

Lemma find_decision_decomp: forall (m: PA) (f: CNF) (l: Lit), 
  find_decision (values m) f = Some l -> exists (c: Clause), find_undef_l (values m) c = Some l /\ c ∈ f.
Proof.
  intros m f l. unfold find_decision. apply CNF.MP.fold_rec_nodep.
  - discriminate.
  - intros c r Hc_in_f IH Hr. destruct r as [l'|].
    + now apply IH.
    + now exists c.
Qed.

Lemma find_decision_exists: forall (m: PA) (f: CNF) (l: Lit),
  l ∈ f -> Undef m l -> exists (l': Lit), find_decision (values m) f = Some l'.
Proof.
  intros m f l [c [Hl_in_c Hc_in_f]] Hundef. unfold find_decision. revert Hc_in_f.
  apply CNF.MP.fold_rec.
  - intros f' Hempty Hc_in_f'. now apply Hempty in Hc_in_f'.
  - intros c' r f' f'' _ _ Hadd IH Hc_in_f''. destruct r as [l'|].
    + now exists l'.
    + apply Hadd in Hc_in_f'' as [Hequal|Hc_in_f'].
      * apply Hequal in Hl_in_c. now apply (find_undef_l_exists m c' l).
      * apply IH in Hc_in_f' as [l' Hcontra]. discriminate.
Qed.

(* If f is undefined under m, there is still a literal to decide. *)
Lemma undef_decision_exists: forall (m: PA) (f: CNF),
  f_eval m f = None -> exists (l: Lit), find_decision (values m) f = Some l.
Proof.
  intros m f Hf. apply f_eval_none_iff in Hf as [_ [c [Hc_in_f Hc]]].
  apply c_eval_none_iff in Hc as [_ [l [Hl_in_c Hl]]].
  apply find_decision_exists with l.
  - now exists c.
  - assumption.
Qed.

Lemma find_decision_undef: forall (m: PA) (f: CNF) (l: Lit),
  find_decision (values m) f = Some l -> Undef m l.
Proof.
  intros m f l Hfind. apply find_decision_decomp in Hfind as [c [Hfind _]].
  now apply find_undef_l_undef in Hfind.
Qed.

Lemma find_decision_bounded: forall (m: PA) (f: CNF) (l: Lit),
  find_decision (values m) f = Some l -> l ∈ f.
Proof.
  intros m f l Hfind. apply find_decision_decomp in Hfind as [c [Hfind Hc_in_f]].
  exists c. split.
  - now apply find_undef_l_in_c in Hfind.
  - assumption.
Qed.

(* The unit clause that find_unit returns is false apart from its unit literal. *)
Lemma find_unit_conflicting: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  find_unit (values m) f = Some (c, l) -> c_eval m (Clause.remove l c) = Some false.
Proof.
  intros m f c l Hfind. apply find_unit_decomp in Hfind as [Hfind _].
  unfold find_unit_l in Hfind. apply Clause.choose_spec1 in Hfind.
  apply Clause.filter_spec in Hfind as [_ Hl].
  - apply andb_true_iff in Hl as [_ Hc]. rewrite c_lookup_false_values in Hc. unfold c_false in Hc.
    destruct (c_eval m (Clause.remove l c)) as [[|]|]; easy.
  - now intros ? ? ->.
Qed.
