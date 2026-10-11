From Stdlib Require Import Structures.OrderedTypeEx.
From Stdlib Require Import FSets.FMapAVL.
From Stdlib Require Import FSets.FMapFacts.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.

(* Finite maps from atoms. *)
Module AtomMap := FMapAVL.Make(Nat_as_OT).
Module AtomMapFacts := FMapFacts.WFacts_fun(Nat_as_OT)(AtomMap).

(* The value of each assigned atom: true if it was assigned positively. *)
Definition Values: Type := AtomMap.t bool.

(* Whether l is a positive literal. *)
Definition is_pos (l: Lit): bool :=
match l with
| Pos _ => true
| Neg _ => false
end.

(* The values of m: replaying the trail, so that the most recent assignment of each atom wins. *)
Fixpoint values (m: PA): Values :=
match m with
| ⟨⟩     => AtomMap.empty bool
| ⟨m, l⟩ => AtomMap.add (extract l) (is_pos l) (values m)
| ⟨m; l⟩ => AtomMap.add (extract l) (is_pos l) (values m)
end.

Section Literals.
  (* The value of l according to v. *)
  Definition lookup (v: Values) (l: Lit): option bool :=
  option_map (fun (b: bool) => if is_pos l then b else negb b) (AtomMap.find (extract l) v).

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
  Lemma lookup_add: forall (v: Values) (l l': Lit),
    lookup (AtomMap.add (extract l') (is_pos l') v) l = l_eval_step l l' (lookup v l).
  Proof.
    intros v l l'. unfold lookup, l_eval_step. rewrite AtomMapFacts.add_o.
    destruct (Nat_as_OT.eq_dec (extract l') (extract l)) as [Heq|Hneq].
    - apply Neg.extract_eq in Heq as [-> | ->].
      + rewrite Lit.eqb_refl. now destruct l.
      + rewrite Neg.self_neqb_neg, Neg.involutive, Lit.eqb_refl. now destruct l.
    - destruct (l =? l') eqn:G1.
      + apply Lit.eqb_eq in G1. subst l'. contradiction.
      + destruct (l =? ¬l') eqn:G2.
        * apply Lit.eqb_eq in G2. subst l. exfalso. apply Hneq. apply Neg.extract_eq. right.
          now rewrite Neg.involutive.
        * reflexivity.
  Qed.

  (* Looking up the values of m agrees with l_eval. *)
  Lemma lookup_values: forall (m: PA) (l: Lit), lookup (values m) l = l_eval m l.
  Proof.
    intros m l. induction m as [|m IH l'|m IH l'].
    - reflexivity.
    - simpl. now rewrite lookup_add, IH.
    - simpl. now rewrite lookup_add, IH.
  Qed.

  Lemma lookup_true_values: forall (m: PA) (l: Lit), lookup_true (values m) l = l_true m l.
  Proof. intros m l. unfold lookup_true, l_true. now rewrite lookup_values. Qed.

  Lemma lookup_false_values: forall (m: PA) (l: Lit), lookup_false (values m) l = l_false m l.
  Proof. intros m l. unfold lookup_false, l_false. now rewrite lookup_values. Qed.

  Lemma lookup_undef_values: forall (m: PA) (l: Lit), lookup_undef (values m) l = l_undef m l.
  Proof. intros m l. unfold lookup_undef, l_undef. now rewrite lookup_values. Qed.
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
  Lemma c_lookup_values: forall (m: PA) (c: Clause), c_lookup (values m) c = c_eval m c.
  Proof.
    intros m c. unfold c_lookup, c_eval.
    rewrite (exists_ext _ (l_true m)), (for_all_ext _ (l_false m)).
    - reflexivity.
    - apply lookup_false_values.
    - apply lookup_true_values.
  Qed.

  Lemma c_lookup_false_values: forall (m: PA) (c: Clause), c_lookup_false (values m) c = c_false m c.
  Proof. intros m c. unfold c_lookup_false, c_false. now rewrite c_lookup_values. Qed.

  (* c_lookup_false gives the same result on equal clauses. *)
  Lemma c_lookup_false_equal: forall (v: Values) (c1 c2: Clause),
    Clause.Equal c1 c2 -> c_lookup_false v c1 = c_lookup_false v c2.
  Proof.
    intros v c1 c2 Heq. unfold c_lookup_false, c_lookup.
    rewrite (Clause.c_equal_exists _ c1 c2 Heq). now rewrite (Clause.c_equal_forall _ c1 c2 Heq).
  Qed.
End Clauses.
