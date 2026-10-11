From Stdlib Require Import Arith.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT.refinement Require Export Table.

(* The value of each atom: Some true if it was assigned positively, Some false if negatively. *)
Definition Values: Type := Table (option bool).

(* Whether l is a positive literal. *)
Definition is_pos (l: Lit): bool :=
match l with
| Pos _ => true
| Neg _ => false
end.

(* v with l assigned. *)
Definition set_value (v: Values) (l: Lit): Values := tset v (extract l) (Some (is_pos l)).

(* The values of m, in a table with room for the atoms below sz: replaying the trail, so that the most recent
   assignment of each atom wins. *)
Fixpoint values (sz: nat) (m: PA): Values :=
match m with
| ⟨⟩     => tmake sz None
| ⟨m, l⟩ => set_value (values sz m) l
| ⟨m; l⟩ => set_value (values sz m) l
end.

Section Literals.
  (* The value of l according to v. *)
  Definition lookup (v: Values) (l: Lit): option bool :=
  option_map (fun (b: bool) => if is_pos l then b else negb b) (tget v (extract l)).

  (* Boolean tests for the three possible values of a literal. *)
  Definition lookup_true (v: Values) (l: Lit): bool :=
  match lookup v l with
  | Some true => true
  | _         => false
  end.

  Definition lookup_false (v: Values) (l: Lit): bool :=
  match lookup v l with
  | Some false => true
  | _          => false
  end.

  Definition lookup_undef (v: Values) (l: Lit): bool :=
  match lookup v l with
  | None => true
  | _    => false
  end.

  (* Adding the value of l' changes a lookup exactly as an assignment of l' changes l_eval. *)
  Lemma lookup_add: forall (v: Values) (l l': Lit), lookup (set_value v l') l = l_eval_step l l' (lookup v l).
  Proof.
    intros v l l'. unfold lookup, set_value, l_eval_step.
    destruct (Nat.eq_dec (extract l') (extract l)) as [Heq|Hneq].
    - rewrite <- Heq, tget_tset_same. apply Neg.extract_eq in Heq as [-> | ->].
      + rewrite Lit.eqb_refl. now destruct l.
      + rewrite Neg.self_neqb_neg, Neg.involutive, Lit.eqb_refl. now destruct l.
    - rewrite tget_tset_other.
      2: assumption.
      destruct (l =? l') eqn:G1.
      + apply Lit.eqb_eq in G1. subst l'. contradiction.
      + destruct (l =? ¬l') eqn:G2.
        * apply Lit.eqb_eq in G2. subst l. exfalso. apply Hneq. apply Neg.extract_eq. right.
          now rewrite Neg.involutive.
        * reflexivity.
  Qed.

  (* After adding the value of l, l is true and every literal other than l and ¬l keeps its value. *)
  Lemma lookup_add_self: forall (v: Values) (l: Lit), lookup (set_value v l) l = Some true.
  Proof. intros v l. rewrite lookup_add. unfold l_eval_step. now rewrite Lit.eqb_refl. Qed.

  Lemma lookup_add_other: forall (v: Values) (l l': Lit),
    l' <> l -> l' <> ¬l -> lookup (set_value v l) l' = lookup v l'.
  Proof.
    intros v l l' Hneq Hneq_neg. rewrite lookup_add. unfold l_eval_step. destruct (l' =? l) eqn:G1.
    - now apply Lit.eqb_eq in G1.
    - destruct (l' =? ¬l) eqn:G2.
      + now apply Lit.eqb_eq in G2.
      + reflexivity.
  Qed.

  (* Looking up the values of m agrees with l_eval. *)
  Lemma lookup_values: forall (sz: nat) (m: PA) (l: Lit), lookup (values sz m) l = l_eval m l.
  Proof.
    intros sz m l. induction m as [|m IH l'|m IH l'].
    - unfold lookup. simpl. now rewrite tget_tmake.
    - simpl. now rewrite lookup_add, IH.
    - simpl. now rewrite lookup_add, IH.
  Qed.

  Lemma lookup_true_values: forall (sz: nat) (m: PA) (l: Lit), lookup_true (values sz m) l = l_true m l.
  Proof. intros sz m l. unfold lookup_true, l_true. now rewrite lookup_values. Qed.

  Lemma lookup_false_values: forall (sz: nat) (m: PA) (l: Lit), lookup_false (values sz m) l = l_false m l.
  Proof. intros sz m l. unfold lookup_false, l_false. now rewrite lookup_values. Qed.

  Lemma lookup_undef_values: forall (sz: nat) (m: PA) (l: Lit), lookup_undef (values sz m) l = l_undef m l.
  Proof. intros sz m l. unfold lookup_undef, l_undef. now rewrite lookup_values. Qed.
End Literals.

Section Clauses.
  (* The value of c according to v, as c_eval. *)
  Definition c_lookup (v: Values) (c: Clause): option bool :=
  if Clause.exists_ (lookup_true v) c then
    Some true
  else if Clause.for_all (lookup_false v) c then
    Some false
  else
    None.

  Definition c_lookup_false (v: Values) (c: Clause): bool :=
  match c_lookup v c with
  | Some false => true
  | _          => false
  end.

  (* exists_ and for_all only depend on the values of the predicate. *)
  Lemma exists_ext: forall (p q: Lit -> bool) (c: Clause),
    (forall (l: Lit), p l = q l) -> Clause.exists_ p c = Clause.exists_ q c.
  Proof.
    intros p q c Hpq. destruct (Clause.exists_ p c) eqn:Hp, (Clause.exists_ q c) eqn:Hq.
    - reflexivity.
    - apply Clause.exists_spec in Hp as [l [Hin Hl]].
      + rewrite <- Hq. symmetry. apply Clause.exists_spec.
        * now intros ? ? ->.
        * exists l. split.
          -- assumption.
          -- now rewrite <- Hpq.
      + now intros ? ? ->.
    - apply Clause.exists_spec in Hq as [l [Hin Hl]].
      + rewrite <- Hp. apply Clause.exists_spec.
        * now intros ? ? ->.
        * exists l. split.
          -- assumption.
          -- now rewrite Hpq.
      + now intros ? ? ->.
    - reflexivity.
  Qed.

  Lemma for_all_ext: forall (p q: Lit -> bool) (c: Clause),
    (forall (l: Lit), p l = q l) -> Clause.for_all p c = Clause.for_all q c.
  Proof.
    intros p q c Hpq. destruct (Clause.for_all p c) eqn:Hp, (Clause.for_all q c) eqn:Hq.
    - reflexivity.
    - rewrite <- Hq. symmetry. apply Clause.for_all_spec.
      + now intros ? ? ->.
      + intros l Hin. rewrite <- Hpq. apply Clause.for_all_spec in Hp.
        * now apply Hp.
        * now intros ? ? ->.
    - rewrite <- Hp. apply Clause.for_all_spec.
      + now intros ? ? ->.
      + intros l Hin. rewrite Hpq. apply Clause.for_all_spec in Hq.
        * now apply Hq.
        * now intros ? ? ->.
    - reflexivity.
  Qed.

  (* Looking up the values of m agrees with c_eval. *)
  Lemma c_lookup_values: forall (sz: nat) (m: PA) (c: Clause), c_lookup (values sz m) c = c_eval m c.
  Proof.
    intros sz m c. unfold c_lookup, c_eval.
    rewrite (exists_ext _ (l_true m)), (for_all_ext _ (l_false m)).
    - reflexivity.
    - apply lookup_false_values.
    - apply lookup_true_values.
  Qed.

  Lemma c_lookup_false_values: forall (sz: nat) (m: PA) (c: Clause), c_lookup_false (values sz m) c = c_false m c.
  Proof. intros sz m c. unfold c_lookup_false, c_false. now rewrite c_lookup_values. Qed.

  (* A clause is false according to v exactly when all its literals are. *)
  Lemma c_lookup_false_iff: forall (v: Values) (c: Clause),
    c_lookup_false v c = true <-> forall (l: Lit), l ∈ c -> lookup v l = Some false.
  Proof.
    intros v c. unfold c_lookup_false, c_lookup.
    destruct (Clause.exists_ (lookup_true v) c) eqn:Htrue, (Clause.for_all (lookup_false v) c) eqn:Hfalse.
    - split.
      + discriminate.
      + intros Hall. apply Clause.exists_spec in Htrue as [l [Hl_in_c Hl]].
        * apply Hall in Hl_in_c. unfold lookup_true in Hl. now rewrite Hl_in_c in Hl.
        * now intros ? ? ->.
    - split.
      + discriminate.
      + intros Hall. apply Clause.exists_spec in Htrue as [l [Hl_in_c Hl]].
        * apply Hall in Hl_in_c. unfold lookup_true in Hl. now rewrite Hl_in_c in Hl.
        * now intros ? ? ->.
    - split.
      + intros _ l Hl_in_c. apply Clause.for_all_spec in Hfalse.
        * apply Hfalse in Hl_in_c. unfold lookup_false in Hl_in_c. destruct (lookup v l) as [[|]|]; easy.
        * now intros ? ? ->.
      + reflexivity.
    - split.
      + discriminate.
      + intros Hall. enough (Hforall: Clause.for_all (lookup_false v) c = true).
        * congruence.
        * apply Clause.for_all_spec.
          -- now intros ? ? ->.
          -- intros l Hl_in_c. unfold lookup_false. now rewrite Hall.
  Qed.

  (* c_lookup_false gives the same result on equal clauses. *)
  Lemma c_lookup_false_equal: forall (v: Values) (c1 c2: Clause),
    Clause.Equal c1 c2 -> c_lookup_false v c1 = c_lookup_false v c2.
  Proof.
    intros v c1 c2 Heq. unfold c_lookup_false, c_lookup.
    rewrite (Clause.c_equal_exists _ c1 c2 Heq). now rewrite (Clause.c_equal_forall _ c1 c2 Heq).
  Qed.
End Clauses.
