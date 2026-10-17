From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import Relations.

From Equations Require Import Equations.

From RocqSAT Require Import Atom.
From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import State.
From RocqSAT Require Import Rule.
From RocqSAT Require Import Trans.
From RocqSAT.rules Require Import Decide.
From RocqSAT Require Import WellFormed.

(* Assign l as a decision if it has no value yet. *)
Definition l_totalize (m: PA) (l: Lit): PA :=
match l_eval m l with
| None => ⟨m; l⟩
| _    => m
end.

(* Assign every literal of a clause that has no value yet. *)
Definition c_totalize (m: PA) (c: Clause): PA :=
Clause.fold (fun (l: Lit) (m': PA) => l_totalize m' l) c m.

(* Assign every literal of a formula that has no value yet. *)
Definition f_totalize (m: PA) (f: CNF): PA :=
CNF.fold (fun (c: Clause) (m': PA) => c_totalize m' c) f m.

(* Totalizing keeps every value that is already defined, for literals, clauses and formulas. *)
Lemma l_totalize_l: forall (m: PA) (l l': Lit) (b: bool),
  l_eval m l' = Some b -> l_eval (l_totalize m l) l' = Some b.
Proof.
  intros. unfold l_totalize. destruct (l_eval m l) eqn:Hl.
  - assumption.
  - now apply l_eval_cons_undef.
Qed.

Lemma l_totalize_c: forall (m: PA) (c: Clause) (l: Lit) (b: bool),
  c_eval m c = Some b -> c_eval (l_totalize m l) c = Some b.
Proof.
  intros. unfold l_totalize. destruct (l_eval m l) eqn:Hl.
  - assumption.
  - apply c_eval_preserve with m.
    + intros l' Hl'. now apply l_eval_cons_undef.
    + assumption.
Qed.

Lemma l_totalize_f: forall (m: PA) (f: CNF) (l: Lit) (b: bool),
  f_eval m f = Some b -> f_eval (l_totalize m l) f = Some b.
Proof.
  intros. unfold l_totalize. destruct (l_eval m l) eqn:Hl.
  - assumption.
  - apply f_eval_preserve with m.
    + intros l' Hl'. now apply l_eval_cons_undef.
    + assumption.
Qed.

Lemma c_totalize_l: forall (m: PA) (c: Clause) (l: Lit) (b: bool),
  l_eval m l = Some b -> l_eval (c_totalize m c) l = Some b.
Proof.
  intros m c l b. unfold c_totalize. rewrite Clause.fold_spec. revert m.
  induction (Clause.elements c) as [|l' c' IH].
  - now intros.
  - intros. simpl. apply IH. now apply l_totalize_l.
Qed.

Lemma c_totalize_c: forall (m: PA) (c c': Clause) (b: bool),
  c_eval m c = Some b -> c_eval (c_totalize m c') c = Some b.
Proof.
  intros m c c' b. unfold c_totalize. rewrite Clause.fold_spec. revert m.
  induction (Clause.elements c') as [|l c'' IH].
  - now intros.
  - intros. simpl. apply IH. now apply l_totalize_c.
Qed.

Lemma c_totalize_f: forall (m: PA) (f: CNF) (c: Clause) (b: bool),
  f_eval m f = Some b -> f_eval (c_totalize m c) f = Some b.
Proof.
  intros m f c b. unfold c_totalize. rewrite Clause.fold_spec. revert m.
  induction (Clause.elements c) as [|l c' IH].
  - now intros.
  - intros. simpl. apply IH. now apply l_totalize_f.
Qed.

Lemma f_totalize_l: forall (m: PA) (f: CNF) (l: Lit) (b: bool),
  l_eval m l = Some b -> l_eval (f_totalize m f) l = Some b.
Proof.
  intros m f l b. unfold f_totalize. rewrite CNF.fold_spec. revert m.
  induction (CNF.elements f) as [|c f' IH].
  - now intros.
  - intros. simpl. apply IH. now apply c_totalize_l.
Qed.

Lemma f_totalize_c: forall (m: PA) (f: CNF) (c: Clause) (b: bool),
  c_eval m c = Some b -> c_eval (f_totalize m f) c = Some b.
Proof.
  intros m f c b. unfold f_totalize. rewrite CNF.fold_spec. revert m.
  induction (CNF.elements f) as [|c' f' IH].
  - now intros.
  - intros. simpl. apply IH. now apply c_totalize_c.
Qed.

Lemma f_totalize_f: forall (m: PA) (f: CNF),
  f_eval m f = Some true -> f_eval (f_totalize m f) f = Some true.
Proof.
  intros m f Hf. rewrite f_eval_true_iff in *. intros c Hin. apply f_totalize_c. now apply Hf.
Qed.

(* After totalizing a clause, every literal of it has a value. *)
Lemma c_totalize_all_def: forall (m: PA) (c: Clause) (l: Lit),
  l ∈ c -> Def (c_totalize m c) l.
Proof.
  intros m c l. unfold c_totalize. apply Clause.MP.fold_rec.
  - intros c' Hempty Hl_in_c'. now apply Hempty in Hl_in_c'.
  - intros l' m' c' c'' _ _ Hadd IH Hl_in_c''. apply Hadd in Hl_in_c'' as [->|Hl_in_c'].
    + unfold Def, l_totalize. destruct (l_eval m' l) eqn:Hl.
      * now exists b.
      * exists true. simpl. unfold l_eval_step. now rewrite Lit.eqb_refl.
    + apply IH in Hl_in_c' as [b Hl]. exists b. now apply l_totalize_l.
Qed.

(* After totalizing a formula, every literal occurring in it has a value. *)
Lemma f_totalize_all_def: forall (m: PA) (f: CNF) (l: Lit),
  l ∈ f -> Def (f_totalize m f) l.
Proof.
  intros m f l. unfold f_totalize. apply CNF.MP.fold_rec.
  - intros f' Hempty [c [_ Hc_in_f']]. now apply Hempty in Hc_in_f'.
  - intros c m' f' f'' _ _ Hadd IH [c' [Hl_in_c' Hc'_in_f'']].
    apply Hadd in Hc'_in_f'' as [Hequal|Hc'_in_f'].
    + apply Hequal in Hl_in_c'. now apply c_totalize_all_def.
    + destruct IH as [b Hl].
      * now exists c'.
      * exists b. now apply c_totalize_l.
Qed.

(* Turn every assigned literal into a decision. *)
Fixpoint convert_prop (m: PA): PA :=
match m with
| ⟨⟩     => ⟨⟩
| ⟨m, l⟩ => ⟨(convert_prop m); l⟩
| ⟨m; l⟩ => ⟨(convert_prop m); l⟩
end.

(* Turning literals into decisions does not change the value of any literal. *)
Lemma convert_prop_l: forall (m: PA) (l: Lit) (v: option bool),
  l_eval m l = v -> l_eval (convert_prop m) l = v.
Proof.
  intros m l v <-. induction m as [|m IH l'|m IH l'].
  - reflexivity.
  - simpl. now rewrite IH.
  - simpl. now rewrite IH.
Qed.

Lemma convert_prop_c: forall (m: PA) (c: Clause),
  c_eval m c = Some true -> c_eval (convert_prop m) c = Some true.
Proof.
  intros m c Hc. rewrite c_eval_true_iff in *. destruct Hc as [l [Hin Hl]].
  exists l. split.
  - assumption.
  - now apply convert_prop_l.
Qed.

Lemma convert_prop_f: forall (m: PA) (f: CNF),
  f_eval m f = Some true -> f_eval (convert_prop m) f = Some true.
Proof.
  intros m f Hf. rewrite f_eval_true_iff in *. intros c Hin. apply convert_prop_c. now apply Hf.
Qed.

Lemma convert_prop_only_dec: forall (m: PA), NoPropagations (convert_prop m).
Proof.
  induction m as [|m IH l|m IH l].
  - easy.
  - assumption.
  - assumption.
Qed.

Lemma convert_prop_all_def: forall (m: PA) (f: CNF) (l: Lit),
  l ∈ f ->
  Def m l ->
  Def (convert_prop m) l.
Proof. unfold Def. intros m f l _ [b Hb]. exists b. now apply convert_prop_l. Qed.

(* Drop the literals whose atom does not occur in f. *)
Fixpoint bound (m: PA) (f: CNF): PA :=
match m with
| ⟨⟩     => ⟨⟩
| ⟨m, l⟩ => if mem_lit l f || mem_lit (¬l) f then ⟨(bound m f), l⟩ else bound m f
| ⟨m; l⟩ => if mem_lit l f || mem_lit (¬l) f then ⟨(bound m f); l⟩ else bound m f
end.

(* Dropping literals outside f does not change the value of a literal that occurs in f, in either polarity. *)
Lemma bound_l_eq: forall (m: PA) (f: CNF) (l: Lit),
  l ∈ f \/ ¬l ∈ f -> l_eval (bound m f) l = l_eval m l.
Proof.
  intros m f l Hl. induction m as [|m IH l'|m IH l'].
  - reflexivity.
  - simpl. destruct (mem_lit l' f || mem_lit (¬l') f) eqn:Hl'.
    + simpl. now rewrite IH.
    + rewrite orb_false_iff, <- !CNF.not_mem_lit_iff in Hl'.
      rewrite IH. unfold l_eval_step. destruct (l =? l') eqn:G1.
      * apply Lit.eqb_eq in G1. subst l'. tauto.
      * destruct (l =? ¬l') eqn:G2.
        -- apply Lit.eqb_eq in G2. subst l. rewrite Neg.involutive in Hl. tauto.
        -- reflexivity.
  - simpl. destruct (mem_lit l' f || mem_lit (¬l') f) eqn:Hl'.
    + simpl. now rewrite IH.
    + rewrite orb_false_iff, <- !CNF.not_mem_lit_iff in Hl'.
      rewrite IH. unfold l_eval_step. destruct (l =? l') eqn:G1.
      * apply Lit.eqb_eq in G1. subst l'. tauto.
      * destruct (l =? ¬l') eqn:G2.
        -- apply Lit.eqb_eq in G2. subst l. rewrite Neg.involutive in Hl. tauto.
        -- reflexivity.
Qed.

(* Hence a true literal of f stays true. *)
Lemma bound_l: forall (m: PA) (f: CNF) (l: Lit),
  l ∈ f \/ ¬l ∈ f -> l_eval m l = Some true -> l_eval (bound m f) l = Some true.
Proof. intros m f l Hl Htrue. now rewrite bound_l_eq. Qed.

(* Hence a true clause of f stays true as well. *)
Lemma bound_c: forall (m: PA) (f: CNF) (c: Clause),
  c ∈ f -> c_eval m c = Some true -> c_eval (bound m f) c = Some true.
Proof.
  intros m f c Hc_in_f Hc. rewrite c_eval_true_iff in *. destruct Hc as [l [Hl_in_c Hl]].
  exists l. split.
  - assumption.
  - apply bound_l.
    + left. now exists c.
    + assumption.
Qed.

Lemma bound_f: forall (m: PA) (f: CNF),
  f_eval m f = Some true -> f_eval (bound m f) f = Some true.
Proof.
  intros m f Hf. rewrite f_eval_true_iff in *. intros c Hc_in_f. apply bound_c.
  - assumption.
  - now apply Hf.
Qed.

Lemma bound_bounded: forall (m: PA) (f: CNF), Bounded (bound m f) f.
Proof.
  unfold Bounded. intros m f. induction m as [|m IH l|m IH l]; simpl.
  - intros l [].
  - destruct (mem_lit l f || mem_lit (¬l) f) eqn:Hl.
    + intros l' [<-|Hin].
      * now rewrite orb_true_iff, !CNF.mem_lit_spec in Hl.
      * now apply IH.
    + assumption.
  - destruct (mem_lit l f || mem_lit (¬l) f) eqn:Hl.
    + intros l' [<-|Hin].
      * now rewrite orb_true_iff, !CNF.mem_lit_spec in Hl.
      * now apply IH.
    + assumption.
Qed.

Lemma bound_incl: forall (m: PA) (f: CNF) (l: Lit), l ∈ bound m f -> l ∈ m.
Proof.
  intros m f l. induction m as [|m IH l'|m IH l']; simpl.
  - easy.
  - destruct (mem_lit l' f || mem_lit (¬l') f).
    + intros [Heq|Hin].
      * now left.
      * right. now apply IH.
    + intros Hin. right. now apply IH.
  - destruct (mem_lit l' f || mem_lit (¬l') f).
    + intros [Heq|Hin].
      * now left.
      * right. now apply IH.
    + intros Hin. right. now apply IH.
Qed.

Lemma bound_only_dec: forall (m: PA) (f: CNF), NoPropagations m -> NoPropagations (bound m f).
Proof.
  intros m f. induction m as [|m IH l|m IH l]; simpl.
  - easy.
  - intros [].
  - intros Hdec. destruct (mem_lit l f || mem_lit (¬l) f).
    + now apply IH.
    + now apply IH.
Qed.

Lemma bound_all_def: forall (m: PA) (f: CNF) (l: Lit),
  l ∈ f ->
  Def m l ->
  Def (bound m f) l.
Proof.
  unfold Def. intros m f l Hl_in_f [b Hb]. exists b. rewrite bound_l_eq.
  - assumption.
  - now left.
Qed.

(* m without the literals whose atom is p. *)
Fixpoint remove_atom (p: Atom) (m: PA): PA :=
match m with
| ⟨⟩     => ⟨⟩
| ⟨m, l⟩ => if extract l =? p then remove_atom p m else ⟨(remove_atom p m), l⟩
| ⟨m; l⟩ => if extract l =? p then remove_atom p m else ⟨(remove_atom p m); l⟩
end.

(* Keep only the most recent assignment of every atom. *)
Fixpoint dedupe (m: PA): PA :=
match m with
| ⟨⟩     => ⟨⟩
| ⟨m, l⟩ => ⟨(remove_atom (extract l) (dedupe m)), l⟩
| ⟨m; l⟩ => ⟨(remove_atom (extract l) (dedupe m)); l⟩
end.

(* A literal that differs from both l' and ¬l' has a different atom than l'. *)
Lemma extract_neqb_iff: forall (l l': Lit),
  (l =? l') = false ->
  (l =? ¬l') = false ->
  (extract l =? extract l') = false.
Proof. intros. destruct l, l'; now simpl in *. Qed.

(* Assigning a literal with another atom does not change the value of l. *)
Lemma l_eval_step_other: forall (l l': Lit) (v: option bool),
  (extract l' =? extract l) = false -> l_eval_step l l' v = v.
Proof.
  intros l l' v Hatom. unfold l_eval_step. destruct (l =? l') eqn:G1.
  - apply Lit.eqb_eq in G1. subst l'. now rewrite Atom.eqb_refl in Hatom.
  - destruct (l =? ¬l') eqn:G2.
    + apply Lit.eqb_eq in G2. assert (extract l = extract l') as Heq.
      * apply Neg.extract_eq. now right.
      * now rewrite Heq, Atom.eqb_refl in Hatom.
    + reflexivity.
Qed.

(* Removing the literals of another atom does not change the value of l. *)
Lemma remove_atom_l: forall (m: PA) (p: Atom) (l: Lit),
  (p =? extract l) = false -> l_eval (remove_atom p m) l = l_eval m l.
Proof.
  intros m p l Hp. induction m as [|m IH l'|m IH l'].
  - reflexivity.
  - simpl. destruct (extract l' =? p) eqn:Hl'.
    + apply Atom.eqb_eq in Hl'. subst p. rewrite IH. symmetry. now apply l_eval_step_other.
    + simpl. now rewrite IH.
  - simpl. destruct (extract l' =? p) eqn:Hl'.
    + apply Atom.eqb_eq in Hl'. subst p. rewrite IH. symmetry. now apply l_eval_step_other.
    + simpl. now rewrite IH.
Qed.

Lemma remove_atom_incl: forall (m: PA) (p: Atom) (l: Lit), l ∈ remove_atom p m -> l ∈ m.
Proof.
  intros m p l. induction m as [|m IH l'|m IH l']; simpl.
  - easy.
  - destruct (extract l' =? p).
    + intros Hin. right. now apply IH.
    + intros [Heq|Hin].
      * now left.
      * right. now apply IH.
  - destruct (extract l' =? p).
    + intros Hin. right. now apply IH.
    + intros [Heq|Hin].
      * now left.
      * right. now apply IH.
Qed.

Lemma remove_atom_not_in: forall (m: PA) (p: Atom), ~ In p (atoms (remove_atom p m)).
Proof.
  intros m p. induction m as [|m IH l|m IH l]; simpl.
  - easy.
  - destruct (extract l =? p) eqn:Hl.
    + assumption.
    + intros [Heq|Hin].
      * rewrite Heq, Atom.eqb_refl in Hl. discriminate.
      * now apply IH.
  - destruct (extract l =? p) eqn:Hl.
    + assumption.
    + intros [Heq|Hin].
      * rewrite Heq, Atom.eqb_refl in Hl. discriminate.
      * now apply IH.
Qed.

Lemma remove_atom_no_propagations: forall (m: PA) (p: Atom),
  NoPropagations m -> NoPropagations (remove_atom p m).
Proof.
  intros m p. induction m as [|m IH l|m IH l]; simpl.
  - easy.
  - intros [].
  - intros Hdec. destruct (extract l =? p).
    + now apply IH.
    + now apply IH.
Qed.

Lemma nodup_remove_atom: forall (m: PA) (p: Atom), NoDuplicates m -> NoDuplicates (remove_atom p m).
Proof.
  unfold NoDuplicates. intros m p. induction m as [|m IH l|m IH l]; simpl.
  - easy.
  - intros Hnodup. inversion Hnodup as [|? ? Hnot_in Hnodup']. destruct (extract l =? p).
    + now apply IH.
    + constructor.
      * intros Hin. apply Hnot_in. apply PA.in_atoms in Hin as [l' [Hin Heq]].
        apply PA.in_atoms. exists l'. split.
        -- now apply remove_atom_incl with p.
        -- assumption.
      * now apply IH.
  - intros Hnodup. inversion Hnodup as [|? ? Hnot_in Hnodup']. destruct (extract l =? p).
    + now apply IH.
    + constructor.
      * intros Hin. apply Hnot_in. apply PA.in_atoms in Hin as [l' [Hin Heq]].
        apply PA.in_atoms. exists l'. split.
        -- now apply remove_atom_incl with p.
        -- assumption.
      * now apply IH.
Qed.

Lemma dedupe_incl: forall (m: PA) (l: Lit), l ∈ dedupe m -> l ∈ m.
Proof.
  intros m l. induction m as [|m IH l'|m IH l'].
  - easy.
  - intros [Heq|Hin].
    + now left.
    + right. apply IH. now apply remove_atom_incl in Hin.
  - intros [Heq|Hin].
    + now left.
    + right. apply IH. now apply remove_atom_incl in Hin.
Qed.

(* Removing older duplicate atoms does not change the value of any literal. *)
Lemma dedupe_l: forall (m: PA) (l: Lit) (v: option bool),
  l_eval m l = v -> l_eval (dedupe m) l = v.
Proof.
  intros m l v <-. induction m as [|m IH l'|m IH l'].
  - reflexivity.
  - simpl. unfold l_eval_step. destruct (l =? l') eqn:G1.
    + reflexivity.
    + destruct (l =? ¬l') eqn:G2.
      * reflexivity.
      * rewrite remove_atom_l.
        -- assumption.
        -- rewrite Atom.eqb_sym. now apply extract_neqb_iff.
  - simpl. unfold l_eval_step. destruct (l =? l') eqn:G1.
    + reflexivity.
    + destruct (l =? ¬l') eqn:G2.
      * reflexivity.
      * rewrite remove_atom_l.
        -- assumption.
        -- rewrite Atom.eqb_sym. now apply extract_neqb_iff.
Qed.

Lemma dedupe_c: forall (m: PA) (c: Clause),
  c_eval m c = Some true -> c_eval (dedupe m) c = Some true.
Proof.
  intros m c Hc. rewrite c_eval_true_iff in *. destruct Hc as [l [Hin Hl]].
  exists l. split.
  - assumption.
  - now apply dedupe_l.
Qed.

Lemma dedupe_f: forall (m: PA) (f: CNF),
  f_eval m f = Some true -> f_eval (dedupe m) f = Some true.
Proof.
  intros m f Hf. rewrite f_eval_true_iff in *. intros c Hin. apply dedupe_c. now apply Hf.
Qed.

Lemma dedupe_all_def: forall (m: PA) (f: CNF) (l: Lit),
  l ∈ f ->
  Def m l ->
  Def (dedupe m) l.
Proof. unfold Def. intros m f l _ [b Hb]. exists b. now apply dedupe_l. Qed.

Lemma dedupe_only_dec: forall (m: PA), NoPropagations m -> NoPropagations (dedupe m).
Proof.
  induction m as [|m IH l|m IH l]; simpl.
  - easy.
  - intros [].
  - intros Hdec. apply remove_atom_no_propagations. now apply IH.
Qed.

Lemma dedupe_bounded: forall (m: PA) (f: CNF), Bounded m f -> Bounded (dedupe m) f.
Proof. unfold Bounded. intros m f Hbounded l Hin. apply Hbounded. now apply dedupe_incl. Qed.

Lemma dedupe_no_duplicates: forall (m: PA), NoDuplicates (dedupe m).
Proof.
  unfold NoDuplicates. induction m as [|m IH l|m IH l]; simpl.
  - constructor.
  - constructor.
    + apply remove_atom_not_in.
    + now apply nodup_remove_atom.
  - constructor.
    + apply remove_atom_not_in.
    + now apply nodup_remove_atom.
Qed.

(* Turn any assignment into one made of decisions only, which assigns every literal of f, contains only literals of f, and has no duplicates. *)
Definition normalize (m: PA) (f: CNF): PA := dedupe (bound (convert_prop (f_totalize m f)) f).

Lemma normalize_f: forall (m: PA) (f: CNF),
  f_eval m f = Some true -> f_eval (normalize m f) f = Some true.
Proof.
  intros. unfold normalize.
  apply dedupe_f. apply bound_f. apply convert_prop_f. now apply f_totalize_f.
Qed.

Lemma normalize_all_def: forall (m: PA) (f: CNF) (l: Lit),
  l ∈ f -> Def (normalize m f) l.
Proof.
  intros. unfold normalize.
  apply (dedupe_all_def _ f).
  - assumption.
  - apply bound_all_def.
    + assumption.
    + apply (convert_prop_all_def _ f).
      * assumption.
      * now apply f_totalize_all_def.
Qed.

Lemma normalize_only_dec: forall (m: PA) (f: CNF), NoPropagations (normalize m f).
Proof.
  intros. unfold normalize. apply dedupe_only_dec. apply bound_only_dec. apply convert_prop_only_dec.
Qed.

Lemma normalize_bounded: forall (m: PA) (f: CNF), Bounded (normalize m f) f.
Proof. intros. unfold normalize. apply dedupe_bounded. apply bound_bounded. Qed.

Lemma normalize_no_duplicates: forall (m: PA) (f: CNF), NoDuplicates (normalize m f).
Proof. intros. unfold normalize. apply dedupe_no_duplicates. Qed.

Lemma normalize_well_formed: forall (m: PA) (f: CNF), WellFormed (state (normalize m f) f).
Proof.
  unfold WellFormed. intros. split.
  - apply normalize_no_duplicates.
  - apply normalize_bounded.
Qed.

(* Every well-formed assignment that consists of decisions only is reachable from the initial state, with any rules that include Decide. *)
Lemma normalize_derivation_aux: forall (rs: list Rule) (m: PA) (f: CNF),
  In Decide rs -> WellFormed (state m f) -> NoPropagations m -> state ⟨⟩ f ==>*[rs] state m f.
Proof.
  intros rs m. induction m as [|m IH l|m IH l].
  - intros. apply rt_refl.
  - intros f _ _ [].
  - intros f Hdecide Hwf Hdec. apply rt_trans with (y := state m f).
    + apply IH.
      * assumption.
      * now apply well_formed_tail in Hwf.
      * assumption.
    + apply rt_step. destruct Hwf as [Hno_dup Hbounded].
      apply nodup_cons__undef in Hno_dup as Hundef.
      apply (t_step Decide).
      * assumption.
      * apply r_decide.
        -- apply Hbounded. now left.
        -- assumption.
Qed.

(* Hence the normalization of any assignment is reachable from the initial state. *)
Lemma normalize_derivation: forall (rs: list Rule) (m: PA) (f: CNF),
  In Decide rs -> state ⟨⟩ f ==>*[rs] state (normalize m f) f.
Proof.
  intros rs m f Hdecide. apply normalize_derivation_aux.
  - assumption.
  - apply normalize_well_formed.
  - apply normalize_only_dec.
Qed.
