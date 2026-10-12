From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.

Section Literals.
  (* The value of l after l' was assigned, given its value v before. *)
  Definition l_eval_step (l l': Lit) (v: option bool): option bool :=
  if l =? l' then Some true else if l =? ¬l' then Some false else v.

  (* The most recent assignment of l or ¬l determines the value. *)
  Fixpoint l_eval (m: PA) (l: Lit): option bool :=
  match m with
  | ⟨⟩      => None
  | ⟨m, l'⟩ => l_eval_step l l' (l_eval m l)
  | ⟨m; l'⟩ => l_eval_step l l' (l_eval m l)
  end.

  (* Boolean tests for the three possible values of a literal. *)
  Definition l_true (m: PA) (l: Lit): bool :=
  match l_eval m l with
  | Some true => true
  | _         => false
  end.

  Definition l_false (m: PA) (l: Lit): bool :=
  match l_eval m l with
  | Some false => true
  | _          => false
  end.

  Definition l_undef (m: PA) (l: Lit): bool :=
  match l_eval m l with
  | None => true
  | _    => false
  end.

  (* Whether a literal has a value under m. Since l_eval also looks at ¬l, either polarity being assigned counts. *)
  Definition Def (m: PA) (l: Lit): Prop := exists (b: bool), l_eval m l = Some b.
  Definition Undef (m: PA) (l: Lit): Prop := l_eval m l = None.

  Lemma def_iff_not_undef: forall (m: PA) (l: Lit), Def m l <-> ~ Undef m l.
  Proof.
    unfold Def, Undef. intros. destruct (l_eval m l).
    - intuition.
      + discriminate.
      + exists b. reflexivity.
    - intuition. destruct H. discriminate.
  Qed.

  (* Negating l negates the value of a step. *)
  Lemma l_eval_step_neg: forall (l l': Lit) (v: option bool),
    l_eval_step (¬l) l' (option_map negb v) = option_map negb (l_eval_step l l' v).
  Proof.
    intros l l' v. unfold l_eval_step.
    rewrite (Neg.eqb_compat (¬l) l'), Neg.involutive, <- Neg.eqb_compat.
    destruct (l =? l') eqn:G1, (l =? ¬l') eqn:G2.
    - apply Lit.eqb_eq in G1. subst l'. now rewrite Neg.self_neqb_neg in G2.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  (* Negation flips the value of a literal. *)
  Lemma l_eval_neg: forall (m: PA) (l: Lit), l_eval m (¬l) = option_map negb (l_eval m l).
  Proof.
    intros m l. induction m as [|m IH l'|m IH l'].
    - reflexivity.
    - simpl. rewrite IH. apply l_eval_step_neg.
    - simpl. rewrite IH. apply l_eval_step_neg.
  Qed.

  Lemma l_eval_neg_none_iff: forall (m: PA) (l: Lit), l_eval m l = None <-> l_eval m (¬l) = None.
  Proof.
    intros m l. rewrite l_eval_neg. destruct (l_eval m l).
    - split; discriminate.
    - reflexivity.
  Qed.

  Lemma l_eval_neg_some_iff: forall (m: PA) (l: Lit) (b: bool),
    l_eval m l = Some b <-> l_eval m (¬l) = Some (negb b).
  Proof.
    intros m l b. rewrite l_eval_neg. destruct (l_eval m l) as [b'|].
    - destruct b, b'; split; easy.
    - split; discriminate.
  Qed.

  (* A step assigns a value to l exactly when it assigns l or ¬l, or l already had a value. *)
  Lemma l_eval_step_some_iff: forall (l l': Lit) (v: option bool),
    (exists (b: bool), l_eval_step l l' v = Some b) <-> l' = l \/ l' = ¬l \/ exists (b: bool), v = Some b.
  Proof.
    intros l l' v. unfold l_eval_step. destruct (l =? l') eqn:G1.
    - apply Lit.eqb_eq in G1. subst l'. split.
      + now left.
      + now exists true.
    - destruct (l =? ¬l') eqn:G2.
      + apply Lit.eqb_eq in G2. subst l. split.
        * intros _. right. left. now rewrite Neg.involutive.
        * now exists false.
      + apply Lit.eqb_neq in G1, G2. split.
        * intros Hv. right. now right.
        * intros [<-|[->|Hv]].
          -- contradiction.
          -- rewrite Neg.involutive in G2. contradiction.
          -- assumption.
  Qed.

  (* A literal has a value exactly when it or its negation is assigned. *)
  Lemma l_eval_some_iff: forall (m: PA) (l: Lit),
    (exists (b: bool), l_eval m l = Some b) <-> l ∈ m \/ ¬l ∈ m.
  Proof.
    intros m l. induction m as [|m IH l'|m IH l']; cbn.
    - split.
      + now intros [b Hb].
      + now intros [[]|[]].
    - rewrite l_eval_step_some_iff, IH. tauto.
    - rewrite l_eval_step_some_iff, IH. tauto.
  Qed.

  (* A literal can only be true because it was assigned, and only be false because its negation was. *)
  Lemma l_eval_true_in: forall (m: PA) (l: Lit), l_eval m l = Some true -> l ∈ m.
  Proof.
    intros m l. induction m as [|m IH l'|m IH l']; simpl; unfold l_eval_step.
    - discriminate.
    - destruct (l =? l') eqn:G1.
      + intros _. left. symmetry. now apply Lit.eqb_eq.
      + destruct (l =? ¬l').
        * discriminate.
        * intros Hl. right. now apply IH.
    - destruct (l =? l') eqn:G1.
      + intros _. left. symmetry. now apply Lit.eqb_eq.
      + destruct (l =? ¬l').
        * discriminate.
        * intros Hl. right. now apply IH.
  Qed.

  Lemma l_eval_false_in: forall (m: PA) (l: Lit), l_eval m l = Some false -> ¬l ∈ m.
  Proof. intros m l Hl. apply l_eval_true_in. now rewrite l_eval_neg, Hl. Qed.

  (* Assigning a literal that was unassigned does not change the value of any literal that already had one. *)
  Lemma l_eval_cons_undef: forall (m: PA) (l l': Lit) (b: bool),
    Undef m l' -> l_eval m l = Some b -> l_eval ⟨m, l'⟩ l = Some b.
  Proof.
    unfold Undef. intros m l l' b Hundef Hl. simpl. unfold l_eval_step. destruct (l =? l') eqn:G1.
    - apply Lit.eqb_eq in G1. subst l'. congruence.
    - destruct (l =? ¬l') eqn:G2.
      + apply Lit.eqb_eq in G2. subst l. apply l_eval_neg_none_iff in Hundef. congruence.
      + assumption.
  Qed.

  (* Assigning l keeps every true literal true, except ¬l. *)
  Lemma l_eval_cons_true: forall (m: PA) (l l': Lit),
    l' <> ¬l -> l_eval m l' = Some true -> l_eval ⟨m, l⟩ l' = Some true.
  Proof.
    intros m l l' Hneq Hl'. simpl. unfold l_eval_step. destruct (l' =? l).
    - reflexivity.
    - destruct (l' =? ¬l) eqn:G.
      + now apply Lit.eqb_eq in G.
      + assumption.
  Qed.

  (* In m followed by n, a literal keeps the value n gives it. *)
  Lemma l_eval_app_some: forall (m n: PA) (l: Lit) (b: bool),
    l_eval n l = Some b -> l_eval ⟨m ++ n⟩ l = Some b.
  Proof.
    intros m n l b. induction n as [|n IH l'|n IH l']; simpl; unfold l_eval_step.
    - discriminate.
    - destruct (l =? l').
      + now intros.
      + destruct (l =? ¬l').
        * now intros.
        * apply IH.
    - destruct (l =? l').
      + now intros.
      + destruct (l =? ¬l').
        * now intros.
        * apply IH.
  Qed.

  (* A literal that n leaves unassigned has its value under m. *)
  Lemma l_eval_app_undef: forall (m n: PA) (l: Lit),
    Undef n l -> l_eval ⟨m ++ n⟩ l = l_eval m l.
  Proof.
    unfold Undef. intros m n l. induction n as [|n IH l'|n IH l']; simpl; unfold l_eval_step.
    - reflexivity.
    - destruct (l =? l').
      + discriminate.
      + destruct (l =? ¬l').
        * discriminate.
        * apply IH.
    - destruct (l =? l').
      + discriminate.
      + destruct (l =? ¬l').
        * discriminate.
        * apply IH.
  Qed.
End Literals.

Section Clauses.
  (* A clause is true if some literal is true, false if all literals are false, and undefined otherwise. *)
  Definition c_eval (m: PA) (c: Clause): option bool :=
  if Clause.exists_ (l_true m) c then
    Some true
  else if Clause.for_all (l_false m) c then
    Some false
  else
    None.

  (* Boolean tests for the three possible values of a clause. *)
  Definition c_true (m: PA) (c: Clause): bool :=
  match c_eval m c with
  | Some true => true
  | _         => false
  end.

  Definition c_false (m: PA) (c: Clause): bool :=
  match c_eval m c with
  | Some false => true
  | _          => false
  end.

  Definition c_undef (m: PA) (c: Clause): bool :=
  match c_eval m c with
  | None => true
  | _    => false
  end.

  Lemma c_eval_true_iff: forall (m: PA) (c: Clause),
    c_eval m c = Some true <-> exists (l: Lit), l ∈ c /\ l_eval m l = Some true.
  Proof.
    intros m c. split.
    - intros Hc. unfold c_eval in Hc. destruct (Clause.exists_ (l_true m) c) eqn:Hexists.
      + apply Clause.exists_spec in Hexists as [l [Hin Htrue]].
        * exists l. split.
          -- assumption.
          -- unfold l_true in Htrue. destruct (l_eval m l) as [[|]|]; easy.
        * now intros ? ? ->.
      + destruct (Clause.for_all (l_false m) c) eqn:Hforall; easy.
    - intros [l [Hin Hl]]. unfold c_eval. assert (Clause.exists_ (l_true m) c = true) as Hexists.
      + apply Clause.exists_spec.
        * now intros ? ? ->.
        * exists l. split.
          -- assumption.
          -- unfold l_true. now rewrite Hl.
      + now rewrite Hexists.
  Qed.

  Lemma c_eval_false_iff: forall (m: PA) (c: Clause),
    c_eval m c = Some false <-> forall (l: Lit), l ∈ c -> l_eval m l = Some false.
  Proof.
    intros m c. split.
    - intros Hc l Hin. unfold c_eval in Hc. destruct (Clause.exists_ (l_true m) c) eqn:Hexists.
      + discriminate.
      + destruct (Clause.for_all (l_false m) c) eqn:Hforall.
        * apply Clause.for_all_spec in Hforall.
          -- apply Hforall in Hin as Hfalse. unfold l_false in Hfalse. destruct (l_eval m l) as [[|]|]; easy.
          -- now intros ? ? ->.
        * discriminate.
    - intros Hforall. unfold c_eval. destruct (Clause.exists_ (l_true m) c) eqn:Hexists.
      + apply Clause.exists_spec in Hexists as [l [Hin Htrue]].
        * apply Hforall in Hin. unfold l_true in Htrue. now rewrite Hin in Htrue.
        * now intros ? ? ->.
      + assert (Clause.for_all (l_false m) c = true) as Hforall'.
        * apply Clause.for_all_spec.
          -- now intros ? ? ->.
          -- intros l Hin. apply Hforall in Hin as Hl. unfold l_false. destruct (l_eval m l) as [[|]|]; easy.
        * now rewrite Hforall'.
  Qed.

  (* A clause is undefined when no literal is true and at least one literal is unassigned. *)
  Lemma c_eval_none_iff: forall (m: PA) (c: Clause),
    c_eval m c = None <->
      (~ exists (l: Lit), l ∈ c /\ l_eval m l = Some true) /\
         exists (l: Lit), l ∈ c /\ l_eval m l = None.
  Proof.
    intros m c. split.
    - intros Hc. split.
      + unfold not. intros [l [Hin Hl]]. unfold c_eval in Hc. assert (Clause.exists_ (l_true m) c = true) as Hexists.
        * apply Clause.exists_spec.
          -- now intros ? ? ->.
          -- exists l. split.
            ++ assumption.
            ++ unfold l_true. destruct (l_eval m l) as [[|]|]; easy.
        * now rewrite Hexists in Hc.
      + unfold c_eval in Hc. destruct (Clause.exists_ (l_true m) c) eqn:Hexists.
        * discriminate.
        * destruct (Clause.for_all (l_false m) c) eqn:Hforall.
          -- discriminate.
          -- apply Clause.for_all_mem_4 in Hforall as [l [Hin Hfalse]].
            ++ exists l. unfold l_false in Hfalse. destruct (l_eval m l) as [[|]|] eqn:Hl.
              ** apply Clause.exists_mem_2 with (x:=l) in Hexists.
                --- unfold l_true in Hexists. now rewrite Hl in Hexists.
                --- now intros ? ? ->.
                --- assumption.
              ** discriminate.
              ** now apply Clause.mem_spec in Hin.
            ++ now intros ? ? ->.
    - intros [Hexists' [l [Hin Hl]]]. unfold c_eval. destruct (Clause.exists_ (l_true m) c) eqn:Hexists.
      + apply Clause.exists_spec in Hexists as [l' [Hin' Htrue']].
        * exfalso. apply Hexists'. exists l'. split.
          -- assumption.
          -- unfold l_true in Htrue'. destruct (l_eval m l') as [[|]|]; easy.
        * now intros ? ? ->.
      + destruct (Clause.for_all (l_false m) c) eqn:Hforall.
        * apply Clause.for_all_spec in Hforall.
          -- apply Hforall in Hin as Hfalse. unfold l_false in Hfalse. destruct (l_eval m l) as [[|]|]; easy.
          -- now intros ? ? ->.
        * reflexivity.
  Qed.

  (* If c without l is false and l is false, then c is false. *)
  Lemma c_eval_remove_false: forall (m: PA) (c: Clause) (l: Lit),
    c_eval m (Clause.remove l c) = Some false -> l_eval m l = Some false -> c_eval m c = Some false.
  Proof.
    intros m c l Hc Hl. apply c_eval_false_iff. intros l' Hin. rewrite c_eval_false_iff in Hc.
    destruct (l =? l') eqn:Heq.
    - rewrite Lit.eqb_eq in Heq. congruence.
    - rewrite Lit.eqb_neq in Heq. apply Hc. apply Clause.remove_spec. split.
      + assumption.
      + congruence.
  Qed.

  (* If c without l is false and l is unassigned, then c is undefined (it is a unit clause). *)
  Lemma c_eval_remove_none: forall (m: PA) (c: Clause) (l: Lit),
    l ∈ c -> c_eval m (Clause.remove l c) = Some false -> l_eval m l = None -> c_eval m c = None.
  Proof.
    intros m c l Hin Hc Hl. rewrite c_eval_false_iff in Hc. apply c_eval_none_iff. split.
    - unfold not. intros [l' [Hin' Hl']]. destruct (l =? l') eqn:Heq.
      + rewrite Lit.eqb_eq in Heq. congruence.
      + rewrite Lit.eqb_neq in Heq. assert (Hin_remove: l' ∈ Clause.remove l c).
        * apply Clause.remove_spec. split.
          -- assumption.
          -- congruence.
        * apply Hc in Hin_remove. congruence.
    - now exists l.
  Qed.

  (* A clause equal to {l} is true exactly when l is. *)
  Lemma c_eval_singleton_true_iff: forall (m: PA) (c: Clause) (l: Lit),
    Clause.Equal c (Clause.singleton l) -> c_eval m c = Some true <-> l_eval m l = Some true.
  Proof.
    intros m c l Heq. rewrite c_eval_true_iff. split.
    - intros [l' [Hin Hl']]. apply Heq in Hin. apply Clause.singleton_spec in Hin as ->. assumption.
    - intros Hl. exists l. split.
      + apply Heq. now apply Clause.singleton_spec.
      + assumption.
  Qed.

  (* If m' keeps every literal that is b under m at b, it keeps every clause that is b under m at b. *)
  Lemma c_eval_preserve: forall (m m': PA) (c: Clause) (b: bool),
    (forall (l: Lit), l_eval m l = Some b -> l_eval m' l = Some b) ->
    c_eval m c = Some b -> c_eval m' c = Some b.
  Proof.
    intros m m' c b Hl Hc. destruct b.
    - rewrite c_eval_true_iff in *. destruct Hc as [l [Hin Hl_true]].
      exists l. split.
      + assumption.
      + now apply Hl.
    - rewrite c_eval_false_iff in *. intros l Hin. apply Hl. now apply Hc.
  Qed.
End Clauses.

Section Formulas.
  (* A formula is true if all clauses are true, false if some clause is false, and undefined otherwise. *)
  Definition f_eval (m: PA) (f: CNF): option bool :=
  if CNF.for_all (c_true m) f then
    Some true
  else if CNF.exists_ (c_false m) f then
    Some false
  else
    None.

  (* Boolean tests for the three possible values of a formula. *)
  Definition f_true (m: PA) (f: CNF): bool :=
  match f_eval m f with
  | Some true => true
  | _         => false
  end.

  Definition f_false (m: PA) (f: CNF): bool :=
  match f_eval m f with
  | Some false => true
  | _          => false
  end.

  Definition f_undef (m: PA) (f: CNF): bool :=
  match f_eval m f with
  | None => true
  | _    => false
  end.

  Lemma f_eval_true_iff: forall (m: PA) (f: CNF),
    f_eval m f = Some true <-> forall (c: Clause), c ∈ f -> c_eval m c = Some true.
  Proof.
    intros m f. split.
    - intros Hf c Hin. unfold f_eval in Hf. destruct (CNF.for_all (c_true m) f) eqn:Hforall.
      + apply CNF.for_all_spec in Hforall.
        * apply Hforall in Hin as Htrue. unfold c_true in Htrue. destruct (c_eval m c) as [[|]|]; easy.
        * intros c1 c2 Heq. unfold c_true. unfold c_eval.
          rewrite (Clause.c_equal_exists _ c1 c2 Heq). now rewrite (Clause.c_equal_forall _ c1 c2 Heq).
      + destruct (CNF.exists_ (c_false m) f) eqn:Hexists.
        * discriminate.
        * discriminate.
    - intros Hforall. unfold f_eval. assert (CNF.for_all (c_true m) f = true) as Hforall'.
      + apply CNF.for_all_spec.
        * intros c1 c2 Heq. unfold c_true. unfold c_eval.
          rewrite (Clause.c_equal_exists _ c1 c2 Heq). now rewrite (Clause.c_equal_forall _ c1 c2 Heq).
        * intros c Hin. apply Hforall in Hin as Hc. unfold c_true. destruct (c_eval m c) as [[|]|]; easy.
      + now rewrite Hforall'.
  Qed.

  Lemma f_eval_false_iff: forall (m: PA) (f: CNF),
    f_eval m f = Some false <-> exists (c: Clause), c ∈ f /\ c_eval m c = Some false.
  Proof.
    intros m f. split.
    - intros Hf. unfold f_eval in Hf. destruct (CNF.for_all (c_true m) f) eqn:Hforall.
      + discriminate.
      + destruct (CNF.exists_ (c_false m) f) eqn:Hexists.
        * apply CNF.exists_spec in Hexists as [c [Hin Hfalse]].
          -- exists c. split.
            ++ assumption.
            ++ unfold c_false in Hfalse. destruct (c_eval m c) as [[|]|]; easy.
          -- intros c1 c2 Heq. unfold c_false. unfold c_eval.
             rewrite (Clause.c_equal_exists _ c1 c2 Heq). now rewrite (Clause.c_equal_forall _ c1 c2 Heq).
        * discriminate.
    - intros [c [Hin Hc]]. unfold f_eval. assert (CNF.for_all (c_true m) f = false) as Hforall.
      + apply CNF.for_all_mem_3 with (x:=c).
        * intros c1 c2 Heq. unfold c_true. unfold c_eval.
          rewrite (Clause.c_equal_exists _ c1 c2 Heq). now rewrite (Clause.c_equal_forall _ c1 c2 Heq).
        * now apply CNF.mem_spec.
        * unfold c_true. destruct (c_eval m c) as [[|]|]; easy.
      + rewrite Hforall. assert (CNF.exists_ (c_false m) f = true) as Hexists.
        * apply CNF.exists_spec.
          -- intros c1 c2 Heq. unfold c_false. unfold c_eval.
             rewrite (Clause.c_equal_exists _ c1 c2 Heq). now rewrite (Clause.c_equal_forall _ c1 c2 Heq).
          -- exists c. split.
            ++ assumption.
            ++ unfold c_false. destruct (c_eval m c) as [[|]|]; easy.
        * now rewrite Hexists.
  Qed.

  (* Likewise for formulas. *)
  Lemma f_eval_preserve: forall (m m': PA) (f: CNF) (b: bool),
    (forall (l: Lit), l_eval m l = Some b -> l_eval m' l = Some b) ->
    f_eval m f = Some b -> f_eval m' f = Some b.
  Proof.
    intros m m' f b Hl Hf. destruct b.
    - rewrite f_eval_true_iff in *. intros c Hin. apply c_eval_preserve with m.
      + assumption.
      + now apply Hf.
    - rewrite f_eval_false_iff in *. destruct Hf as [c [Hin Hc]].
      exists c. split.
      + assumption.
      + now apply c_eval_preserve with m.
  Qed.
End Formulas.
