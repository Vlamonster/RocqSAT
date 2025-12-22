From Equations Require Import Equations.
From Stdlib Require Import Nat Bool Arith List Relations Wellfounded Lia.
Import ListNotations.

Open Scope bool_scope.

Module Atom.
  (* Atoms are propositional symbols mapped to the naturals. *)
  Definition Atom: Type := nat.

  Definition eqb := Nat.eqb.

  Declare Scope atom_scope.
  Infix "=?" := eqb (at level 70): atom_scope.
  Open Scope atom_scope.

  Lemma eqb_refl: forall (p: Atom), p =? p = true.
  Proof. apply Nat.eqb_refl. Qed.

  Lemma eqb_sym: forall (p1 p2: Atom), (p1 =? p2) = (p2 =? p1).
  Proof. apply Nat.eqb_sym. Qed.

  Lemma eqb_eq: forall (p1 p2: Atom), p1 =? p2 = true <-> p1 = p2.
  Proof. apply Nat.eqb_eq. Qed.
End Atom. Import Atom.

Module Lit.
  (* Literals are either positive or negated variants of atoms. *)
  Inductive Lit: Type :=
  | Pos (p: Atom)
  | Neg (p: Atom).

  Equations eqb (l1 l2: Lit): bool :=
  eqb (Pos p1) (Pos p2) := p1 =? p2;
  eqb (Neg p1) (Neg p2) := p1 =? p2;
  eqb _        _        := false.

  Equations extract (l: Lit): Atom :=
  extract (Pos p) := p;
  extract (Neg p) := p.

  Declare Scope lit_scope.
  Infix "=?" := eqb (at level 70): lit_scope.
  Open Scope lit_scope.

  Lemma eqb_refl: forall (l: Lit), l =? l = true.
  Proof. destruct l; simp eqb; apply eqb_refl. Qed.

  Lemma eqb_sym: forall (l1 l2: Lit), (l1 =? l2) = (l2 =? l1).
  Proof. destruct l1, l2; simp eqb; try reflexivity; try now apply eqb_sym. Qed.

  Lemma eqb_eq: forall (l1 l2: Lit), l1 =? l2 = true <-> l1 = l2.
  Proof. destruct l1, l2; split; try simp eqb; try rewrite eqb_eq; try congruence. Qed.

  Lemma eqb_neq: forall (l1 l2: Lit), l1 =? l2 = false <-> l1 <> l2.
  Proof. 
    intros. rewrite <- not_iff_compat.
    - now rewrite not_true_iff_false.
    - apply eqb_eq.
  Qed.
End Lit. Import Lit.

Module Neg.
  (* Negates a literal (i.e. Pos becomes Neg and Neg becomes Pos). *)
  Equations neg (l: Lit): Lit :=
  neg (Pos p) := Neg p;
  neg (Neg p) := Pos p.

  Declare Scope neg_scope.
  Notation "¬ l" := (neg l) (at level 65, right associativity, format "'[' ¬ ']' l"): neg_scope.
  Open Scope neg_scope.

  Lemma self_neq_neg: forall (l: Lit), l <> ¬l.
  Proof. intros. apply eqb_neq. now funelim (l =? ¬l). Qed.

  Lemma self_neqb_neg: forall (l: Lit), l =? ¬l = false.
  Proof. intros. now funelim (l =? ¬l). Qed.

  Lemma involutive: forall (l: Lit), ¬¬l = l.
  Proof. intros. now funelim (¬l). Qed.

  Lemma eqb_compat: forall (l1 l2: Lit), (l1 =? l2) = (¬l1 =? ¬l2).
  Proof. now destruct l1, l2. Qed.

  Lemma eq_compat: forall (l1 l2: Lit), l1 = l2 <-> ¬l1 = ¬l2.
  Proof. intros. repeat rewrite <- eqb_eq. now rewrite eqb_compat. Qed.
End Neg. Import Neg.

Module Clause.
  (* A clause is a disjunction of literals. *)
  Definition Clause: Type := list Lit.

  (* Remove a literal from a clause. *)
  Equations l_remove (c: Clause) (l: Lit): Clause :=
  l_remove c l := filter (fun (l': Lit) => negb (l =? l')) c.
End Clause. Import Clause.

Module CNF.
  (* A formula is a conjunction of clauses. *)
  Definition CNF: Type := list Clause.
End CNF. Import CNF.

Module Evaluation.
  (* An annotation on a literal (Lit * Ann) describing how its value was assigned. *)
  Inductive Ann: Type :=
  | dec
  | prop.

  (* A partial assignment for annoted literals. See below for evaluation. *)
  Definition PA: Type := list (Lit * Ann).

  Declare Scope pa_scope.
  Notation "m ++a n" := (n ++ m) (at level 55, left associativity): pa_scope.
  Notation "m ++d l" := ((l, dec) :: m) (at level 55, left associativity): pa_scope.
  Notation "m ++p l" := ((l, prop) :: m) (at level 55, left associativity): pa_scope.
  Open Scope pa_scope.

  (* The first instance of `l` or `¬l` determines the value. *)
  Equations l_eval (m: PA) (l: Lit): option bool :=
  l_eval [] _ := None;
  l_eval ((l', _) :: m) l with l =? l', l =? ¬l' :=
    | true, _    := Some true
    | _   , true := Some false
    | _   , _    := l_eval m l.

  Equations c_eval (m: PA) (c: Clause): option bool :=
  c_eval m [] := Some false;
  c_eval m (l :: c) with l_eval m l, c_eval m c :=
    | Some true , _          := Some true
    | _         , Some true  := Some true
    | Some false, Some false := Some false
    | _         , _          := None.

  Equations f_eval (m: PA) (f: CNF): option bool :=
  f_eval m [] := Some true;
  f_eval m (c :: f) with c_eval m c, f_eval m f :=
    | Some true , r          := r
    | Some false, _          := Some false
    | _         , Some false := Some false
    | None      , _          := None.

  Definition Def (m: PA) (l: Lit): Prop := exists (b: bool), l_eval m l = Some b.
  Definition Undef (m: PA) (l: Lit): Prop := l_eval m l = None.

  Lemma def_undef: forall (m: PA) (l: Lit), Def m l <-> ~ Undef m l.
  Proof. 
    unfold Def, Undef. intros. destruct (l_eval m l).
    - intuition.
      + discriminate.
      + exists b. reflexivity.
    - intuition. destruct H. discriminate.
  Qed.
End Evaluation. Import Evaluation.

Module EvalExamples.
  Compute l_eval ([] ++p Pos 1) (Pos 1).
  Compute l_eval ([] ++p Pos 1) (Neg 1).
  Compute c_eval [] [Pos 1; Pos 2].
  Compute c_eval ([] ++p Pos 1) [Pos 1; Pos 2].
  Compute c_eval ([] ++p Neg 1) [Pos 1; Pos 2].
  Compute c_eval ([] ++p Pos 2) [Pos 1; Pos 2].
End EvalExamples.

Module Trans.
  Definition NoDuplicates (m: PA): Prop := 
    NoDup (map extract (map fst m)).

  Definition Bounded (m: PA) (f: CNF): Prop := 
    forall (l: Lit) (a: Ann), In (l, a) m -> 
    exists (c: Clause), In c f /\ (In l c \/ In (¬l) c).
  
  Definition WellFormed (m: PA) (f: CNF): Prop :=
    NoDuplicates m /\ Bounded m f.

  Inductive State: Type :=
  | fail
  | state (m: PA) (f: CNF) (Hwf: WellFormed m f).

  (* Propositions used in the transition relation `==>`. *)
  Definition NoDecisions (m: PA): Prop := ~ exists (l: Lit), In (l, dec) m.
  Definition Conflicting (m: PA) (c: Clause): Prop := c_eval m c = Some false.

  Inductive Trans: relation State :=
  (* Fail if all literals are assigned and there is a conflict. *)
  | t_fail (m: PA) (f: CNF) (c: Clause) (Hwf: WellFormed m f):
    In c f ->
    Conflicting m c ->
    NoDecisions m ->
    Trans (state m f Hwf) fail
  (* If a clause is false except for one unassigned literal, assign it to satisfy the clause. *)
  | t_unit (m: PA) (f: CNF) (c: Clause) (l: Lit) (Hwf: WellFormed m f) (Hwf': WellFormed (m ++p l) f):
    In l c ->
    In c f ->
    Conflicting m (l_remove c l) ->
    Undef m l ->
    Trans (state m f Hwf) (state (m ++p l) f Hwf')
  (* Arbitrarily set an unassigned literal in the formula to true. *)
  | t_decide (m: PA) (f: CNF) (c: Clause) (l: Lit) (Hwf: WellFormed m f) (Hwf': WellFormed (m ++d l) f):
    In l c \/ In (¬l) c ->
    In c f ->
    Undef m l ->
    Trans (state m f Hwf) (state (m ++d l) f Hwf')
  (* Backtrack by flipping the most recent decision literal. *)
  | t_backtrack (m n: PA) (f: CNF) (c: Clause) (l: Lit) (Hwf: WellFormed (m ++d l ++a n) f) (Hwf': WellFormed (m ++p ¬l) f):
    In c f ->
    Conflicting (m ++d l ++a n) c ->
    NoDecisions n ->
    Trans (state (m ++d l ++a n) f Hwf) (state (m ++p ¬l) f Hwf').
  
  (* The following is the reflexive-transitive closure of `==>`. *)
  Definition TransRTC: relation State := clos_refl_trans State Trans.

  Declare Scope trans_scope.
  Infix "==>" := Trans (at level 70): trans_scope.
  Infix "==>*" := TransRTC (at level 70): trans_scope.
  Open Scope trans_scope.

  (* A state is final if there are no states that follow from it by `==>`. *)
  Definition Final (s: State): Prop := ~ exists (s': State), s ==> s'.
End Trans. Import Trans.

Equations split_last_decision (m: PA): option (PA * Lit) :=
split_last_decision [] := None;
split_last_decision (m ++d l) := Some (m, l);
split_last_decision (m ++p l) := split_last_decision m.

Equations is_conflict (m: PA) (c: Clause): bool :=
is_conflict m c with c_eval m c :=
  | Some false := true
  | _          := false.

Equations find_conflict (m: PA) (f: CNF): option Clause :=
find_conflict m f := find (is_conflict m) f.

Equations find_unit_l (m: PA) (c: Clause): option Lit :=
find_unit_l m c := find (fun (l: Lit) => is_conflict m (l_remove c l)) c.

Equations find_unit (m: PA) (f: CNF): option (Clause * Lit) :=
find_unit m [] := None;
find_unit m (c :: f) with c_eval m c, find_unit_l m c :=
  | None, Some l := Some (c, l)
  | _   , _      := find_unit m f.

Equations is_undefined_l (m: PA) (l: Lit): bool :=
is_undefined_l m l with l_eval m l := 
  | None := true
  | _    := false.

Equations find_undef_l (m: PA) (c: Clause): option Lit :=
find_undef_l m c := find (is_undefined_l m) c.

Equations find_decision (m: PA) (f: CNF): option Lit :=
find_decision m [] := None;
find_decision m (c :: f) with find_undef_l m c, find_decision m f :=
  | Some l, _ := Some l
  | _     , r := r.

Definition inspect {A: Type} (a: A): {b | a = b} := exist _ a eq_refl.
Notation "x 'eqn' ':' p" := (exist _ x p) (only parsing, at level 20).

Lemma nodup_cons: forall (m: PA) (l: Lit) (a: Ann),
  NoDuplicates m -> Undef m l -> NoDuplicates ((l, a) :: m).
Proof.
  unfold Undef, NoDuplicates. intros. simpl. constructor.
  - unfold not. intros. funelim (l_eval m l).
    + contradiction.
    + congruence.
    + congruence.
    + simpl in *. destruct H2. 
      * destruct l, l'.
        -- simp extract in H2. subst p0. now rewrite eqb_refl in Heq0.
        -- simp extract in H2. subst p0. simp neg in Heq. now rewrite eqb_refl in Heq.
        -- simp extract in H2. subst p0. simp neg in Heq. now rewrite eqb_refl in Heq.
        -- simp extract in H2. subst p0. now rewrite eqb_refl in Heq0.
      * apply (H m l).
        -- assumption.
        -- now inversion H0.
        -- congruence.
        -- assumption.
        -- reflexivity.
        -- reflexivity.  
  - assumption.
Qed.

Equations l_in_c (c: Clause) (l: Lit): bool :=
l_in_c c l := existsb (eqb l) c || existsb (eqb (¬l)) c.

Equations l_in_f (f: CNF) (l: Lit): bool :=
l_in_f f l := existsb (fun (c: Clause) => l_in_c c l) f.

Lemma l_in_f_exists: forall (f: CNF) (l: Lit),
  l_in_f f l = true -> exists (c: Clause), (In l c \/ In (¬l) c) /\ In c f.
Proof.
  intros. simp l_in_f in H. apply existsb_exists in H. destruct H. destruct H.
  simp l_in_c in H0. apply orb_true_iff in H0. exists x. destruct H0.
  - apply existsb_exists in H0. destruct H0. destruct H0. apply eqb_eq in H1. subst x0. split.
    + now left.
    + assumption.
  - apply existsb_exists in H0. destruct H0. destruct H0. apply eqb_eq in H1. subst x0. split.
    + now right.
    + assumption.
Qed.

Lemma bounded_cons: forall (m: PA) (f: CNF) (l: Lit) (a: Ann),
  Bounded m f -> l_in_f f l = true -> Bounded ((l, a) :: m) f.
Proof.
  unfold Bounded. intros m f l a Hbounded Hl_in_f l' a' Hin. 
  apply l_in_f_exists in Hl_in_f as [c [[Hl_in_c|Hnegl_in_c] Hc_in_f ]].
  - inversion Hin.
    + injection H as <- <-. exists c. intuition.
    + now apply Hbounded in H.
  - inversion Hin.
    + injection H as <- <-. exists c. intuition.
    + now apply Hbounded in H.
Qed.

Lemma bounded_cons__bounded: forall (m: PA) (f: CNF) (l: Lit) (a: Ann),
  Bounded ((l, a) :: m) f -> Bounded m f.
Proof.
  unfold Bounded. intros m f l a Hbounded l' a' Hin. apply (Hbounded l' a'). now right.
Qed.

Lemma bounded_app__bounded: forall (m n: PA) (f: CNF),
  Bounded (m ++a n) f -> Bounded m f.
Proof.
  induction n.
  - now intros.
  - intros. simpl in H. destruct a. apply bounded_cons__bounded in H. now apply IHn.
Qed.

Lemma nodup_cons__nodup: forall (m: PA) (l: Lit) (a: Ann),
  NoDuplicates ((l, a) :: m) -> NoDuplicates m.
Proof. intros. now inversion H. Qed.

Lemma nodup_app__nodup: forall (m n: PA),
  NoDuplicates (m ++a n) -> NoDuplicates m.
Proof.
  induction n.
  - now intros.
  - intros. simpl in H. apply nodup_cons__nodup in H.
    + now apply IHn.
    + apply dec.
Qed.

Lemma wf_cons__wf: forall (m: PA) (f: CNF) (l: Lit) (a: Ann),
  WellFormed ((l, a) :: m) f -> WellFormed m f.
Proof.
  unfold WellFormed. intros. destruct H. split.
  - now apply nodup_cons__nodup in H.
  - now apply bounded_cons__bounded in H0.
Qed.

Lemma wf_app__wf: forall (m n: PA) (f: CNF),
  WellFormed (m ++a n) f -> WellFormed m f.
Proof.
  unfold WellFormed. intros. destruct H. split.
  - now apply nodup_app__nodup in H.
  - now apply bounded_app__bounded in H0.
Qed.

Lemma split_decomp: forall (m m': PA) (l': Lit),
  split_last_decision m = Some (m', l') -> exists (n': PA), m = m' ++d l' ++a n' /\ NoDecisions n'.
Proof.
  unfold NoDecisions. unfold not. intros. funelim (split_last_decision m).
  - discriminate.
  - rewrite <- Heqcall in H. injection H as H. subst. exists []. split.
    + reflexivity.
    + intros. destruct H. destruct H.
  - rewrite <- Heqcall in H0. destruct (H m' l' H0). destruct H1. rewrite H1. exists (x ++p l). split.
    + reflexivity.
    + intros. apply H2. destruct H3. destruct H3.
      * discriminate.
      * now exists x0.
Qed.

Lemma bounded_incl: forall (m m': PA) (f: CNF),
  incl m m' -> Bounded m' f -> Bounded m f.
Proof.
  unfold Bounded, incl. intros m m' f Hincl Hbounded l a Hin.
  apply Hincl in Hin. now apply Hbounded in Hin.
Qed.

Lemma l_eval_some_in: forall (m: PA) (l: Lit) (b: bool), 
  l_eval m l = Some b -> exists (a: Ann), In (l, a) m \/ In (¬l, a) m.
Proof. 
  intros. funelim (l_eval m l).
  - congruence.
  - rewrite eqb_eq in Heq. subst l'. exists a. left. now left.
  - rewrite eqb_eq in Heq. subst. exists a. right. rewrite Neg.involutive. now left.
  - rewrite H0 in Heqcall. apply H in Heqcall; auto. destruct Heqcall. destruct H1.
    + exists x. left. now right.
    + exists x. right. now right.
Qed.

Lemma nodup_cons__undef: forall (m: PA) (l: Lit) (a: Ann),
  NoDuplicates ((l, a) :: m) -> Undef m l.
Proof. 
  unfold NoDuplicates, Undef. intros. simpl in *. inversion H.
  destruct (l_eval m l) eqn:G.
  - apply l_eval_some_in in G. exfalso. apply H2. 
    apply in_map_iff. destruct G. destruct H4.
    + exists l. split.
      * reflexivity.
      * apply in_map_iff. exists (l, x0). intuition.
    + exists (¬l). split.
      * destruct l; reflexivity.
      * apply in_map_iff. exists (¬l, x0). intuition.
  - reflexivity.
Qed.

Lemma undef__neg_undef: forall (m: PA) (l: Lit), Undef m l <-> Undef m (¬l).
Proof.
  unfold Undef. intros. funelim (l_eval m l).
  - intuition.
  - intuition.
    + discriminate.
    + apply eqb_eq in Heq. subst. simp l_eval in H. rewrite eqb_refl in H. 
      rewrite eqb_sym in H. rewrite Neg.self_neqb_neg in H. discriminate.
  - intuition.
    + discriminate.
    + apply eqb_eq in Heq. subst. simp neg in H. rewrite Neg.involutive in H.
      simp l_eval in H. rewrite eqb_refl in H. rewrite Neg.self_neqb_neg in H. discriminate.
  - intuition.
    + simp l_eval. rewrite <- Neg.eqb_compat. rewrite Heq0. rewrite Neg.eqb_compat in Heq.
      rewrite Neg.involutive in Heq. rewrite Heq. simpl. assumption.
    + autorewrite with l_eval in H. rewrite <- Neg.eqb_compat in H. rewrite Heq0 in H.
      rewrite Neg.eqb_compat in Heq. rewrite Neg.involutive in Heq. rewrite Heq in H. simpl in H. 
      apply H1. apply H.
Qed.

Lemma wf_backtrack: forall (m m': PA) (f: CNF) (l: Lit),
  split_last_decision m = Some (m', l) ->
  WellFormed m f -> WellFormed (m' ++p ¬l) f.
Proof.
  unfold WellFormed. intros m m' f l Heq Hwf. apply split_decomp in Heq as [n [Heq _]].
  rewrite Heq in Hwf. split.
  - destruct Hwf as [Hnodup _]. apply (nodup_app__nodup (m' ++d l)) in Hnodup.
    assert (Hnodup': NoDuplicates m').
    + now apply (nodup_cons__nodup) in Hnodup.
    + apply nodup_cons__undef in Hnodup. apply undef__neg_undef in Hnodup.
      apply nodup_cons.
      * assumption.
      * assumption.
  - destruct Hwf as [_ Hbounded]. apply (bounded_incl (m' ++d l)) in Hbounded.
    + assert (Hbounded': Bounded m' f).
      * apply (bounded_incl m') in Hbounded.
        -- assumption.
        -- apply incl_tl. apply incl_refl.
      * assert (In (l, dec) (m' ++d l)).
        -- now left.
        -- apply Hbounded in H as [c [Hc_in_f [Hl_in_c|Hnegl_in_c]]].
          ++ intros l' a' Hin. inversion Hin.
            ** injection H as <- <-. exists c. rewrite Neg.involutive. intuition.
            ** now apply Hbounded' in H.
          ++ intros l' a' Hin. inversion Hin.
            ** injection H as <- <-. exists c. intuition.
            ** now apply Hbounded' in H.
    + apply incl_appr. apply incl_refl.
Qed.

Lemma c_eval_none__l_eval_none: forall (m: PA) (c: Clause), 
  c_eval m c = None -> exists (l: Lit), In l c /\ l_eval m l = None.
Proof. 
  induction c. intros.
  - discriminate.
  - intros. destruct (l_eval m a) eqn:G1.
    + destruct b.
      * simp c_eval in H. rewrite G1 in H. simpl in H. discriminate.
      * simp c_eval in H. rewrite G1 in H. simpl in H. destruct (c_eval m c) eqn:G2.
        -- destruct b; discriminate.
        -- apply IHc in H. destruct H. destruct H. exists x. split.
          ++ right. assumption.
          ++ assumption.
    + exists a. split.
      * left. reflexivity.
      * assumption.
Qed.

Lemma c_eval_false__l_eval_false: forall (m: PA) (c: Clause),
  c_eval m c = Some false -> forall (l: Lit), In l c -> l_eval m l = Some false.
Proof. 
  induction c.
  - intros. contradiction.
  - intros. simp c_eval in H. destruct (l_eval m a) eqn:G1.
    + destruct b.
      * simpl in H. discriminate.
      * simpl in H. destruct (c_eval m c) eqn:G2.
        -- destruct b.
          ++ discriminate.
          ++ inversion H0.
            ** subst. assumption.
            ** apply (IHc H l H1).
        -- discriminate.
    + simpl in H. destruct (c_eval m c) eqn:G2.
      * destruct b; discriminate.
      * discriminate.
Qed.

Lemma undef_remove_false__undef: forall (m: PA) (c: Clause) (l: Lit),
  c_eval m c = None -> c_eval m (l_remove c l) = Some false -> Undef m l.
Proof.
  unfold Undef. intros. 
  pose proof (c_eval_none__l_eval_none m c H).
  pose proof (c_eval_false__l_eval_false m (l_remove c l) H0).
  destruct H1. destruct H1. destruct (x =? l) eqn:G.
  - apply eqb_eq in G. subst. assumption.
  - pose proof (H2 x). assert (In x (l_remove c l)).
    + simp l_remove. rewrite filter_In. split.
      * assumption.
      * rewrite eqb_sym. rewrite G. reflexivity.
    + apply H4 in H5. congruence. 
Qed.

Lemma find_unit_l_l_in_c: forall (m: PA) (c: Clause) (l: Lit),
  find_unit_l m c = Some l -> In l c.
Proof.
  intros. funelim (find_unit_l m c). rewrite H in Heqcall. 
  apply find_some in Heqcall. destruct Heqcall. assumption.
Qed.

Lemma find_unit_l_in_c: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  find_unit m f = Some (c, l) -> In l c.
Proof. 
  intros. funelim (find_unit m f).
  - congruence.
  - apply H. rewrite <- H0. assumption.
  - rewrite H in Heqcall. injection Heqcall as Heqcall. subst. 
    apply (find_unit_l_l_in_c m c0 l0). assumption.
  - apply H. congruence.
Qed.

Lemma find_unit_c_in_f: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  find_unit m f = Some (c, l) -> In c f.
Proof. 
  intros. funelim (find_unit m f).
  - congruence.
  - right. apply (H c0 l0). congruence.
  - rewrite H in Heqcall. injection Heqcall as Heqcall. subst. left. reflexivity.
  - right. apply (H c0 l). congruence.
Qed.

Lemma find_unit__undef: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  find_unit m f = Some (c, l) -> Undef m l.
Proof. 
  unfold Undef. intros. funelim (find_unit m f).
  - congruence.
  - rewrite H0 in Heqcall. now apply H in Heqcall.
  - rewrite H in Heqcall. injection Heqcall as <- <-.
    simp find_unit_l in Heq. apply find_some in Heq.
    destruct Heq. simp is_conflict in H1. destruct (c_eval m (l_remove c l)) eqn:G.
    + destruct b.
      * discriminate.
      * apply (undef_remove_false__undef m c l); assumption.
    + discriminate.
  - rewrite H0 in Heqcall. now apply H in Heqcall.
Qed.

Lemma find_unit__bounded: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  find_unit m f = Some (c, l) -> l_in_f f l = true.
Proof.
  intros. simp l_in_f. apply existsb_exists. exists c. split.
  - now apply find_unit_c_in_f in H.
  - simp l_in_c. apply orb_true_iff. left. apply existsb_exists. exists l. split.
    + now apply find_unit_l_in_c in H.
    + apply eqb_refl.
Qed.

Lemma wf_unit: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  find_unit m f = Some (c, l) ->
  WellFormed m f -> WellFormed (m ++p l) f.
Proof.
  unfold WellFormed. intros m f c l Heq Hwf. split.
  - apply nodup_cons.
    + intuition congruence.
    + now apply find_unit__undef in Heq.
  - apply bounded_cons. 
    + intuition congruence. 
    + now apply find_unit__bounded in Heq.
Qed.

Lemma find_decision__undef: forall (m: PA) (f: CNF) (l: Lit),
  find_decision m f = Some l -> Undef m l.
Proof.
  unfold Undef. intros. funelim (find_decision m f).
  - congruence.
  - rewrite H in Heqcall. injection Heqcall as <-. funelim (find_undef_l m c).
    rewrite Heq in Heqcall. apply find_some in Heqcall. funelim (is_undefined_l m l).
    + intuition congruence.
    + assumption.
  - rewrite H in Heqcall. now apply Hind.
Qed.

Lemma find_decision__bounded: forall (m: PA) (f: CNF) (l: Lit),
  find_decision m f = Some l -> l_in_f f l = true.
Proof. 
  intros. funelim (find_decision m f).
  - congruence.
  - rewrite H in Heqcall. injection Heqcall as <-. funelim (find_undef_l m c).
    rewrite Heq in Heqcall. apply find_some in Heqcall.
    simp l_in_f. apply existsb_exists. exists c. split.
    + now left.
    + simp l_in_c. apply orb_true_iff. left. destruct Heqcall as [Hin _].
      apply existsb_exists. exists l. split.
      * assumption.
      * apply eqb_refl.
  - rewrite H in Heqcall. apply Hind in Heqcall. simp l_in_f in *.
    apply existsb_exists in Heqcall. destruct Heqcall. destruct H0.
    apply existsb_exists. exists x. split.
    + now right.
    + assumption.
Qed.

Lemma wf_decide: forall (m: PA) (f: CNF) (l: Lit),
  find_decision m f = Some l ->
  WellFormed m f -> WellFormed (m ++d l) f.
Proof.
  unfold WellFormed. intros m f l Heq Hwf. split.
  - apply nodup_cons.
    + intuition.
    + now apply find_decision__undef in Heq.
  - apply bounded_cons.
    + intuition.
    + now apply find_decision__bounded in Heq.
Qed.

Equations next_state (s: State): option State :=
next_state fail := None;
next_state (state m f Hwf) :=
  match find_conflict m f with
  | Some c =>
    match inspect (split_last_decision m) with
    (* t_fail *)
    | None         eqn:Heq => Some fail
    (* t_backtrack *)
    | Some (m', l) eqn:Heq => Some (state (m' ++p ¬l) f (wf_backtrack m m' f l Heq Hwf))
    end
  | _      =>
  (* t_unit *)
  match inspect (find_unit m f) with
  | Some (c, l)    eqn:Heq => Some (state (m ++p l) f (wf_unit m f c l Heq Hwf))
  | None           eqn:Heq =>
  (* t_decide *)
  match inspect (find_decision m f) with
  | Some l         eqn:Heq => Some (state (m ++d l) f (wf_decide m f l Heq Hwf))
  | None           eqn:Heq => None
  end end end.

Lemma find_conflict_c_in_f: forall (m: PA) (f: CNF) (c: Clause), find_conflict m f = Some c -> In c f.
Proof. intros. simp find_conflict in H. apply find_some in H as [H _]. assumption. Qed.

Lemma find_conflict_conflicting: forall (m: PA) (f: CNF) (c: Clause), find_conflict m f = Some c -> Conflicting m c.
Proof. 
  unfold Conflicting. intros. simp find_conflict in H. apply find_some in H as [_ H]. funelim (is_conflict m c).
  - congruence.
  - assumption.
  - congruence.
Qed.

Lemma no_split__no_decision: forall (m: PA), split_last_decision m = None -> NoDecisions m.
Proof. 
  unfold NoDecisions. unfold not. intros. funelim (split_last_decision m).
  - destruct H0. destruct H0.
  - discriminate.
  - destruct H1. destruct H1.
    + discriminate.
    + apply (H m).
      * assumption.
      * now exists x.
      * reflexivity.
      * reflexivity.
Qed.

Lemma find_unit_conflicting: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  find_unit m f = Some (c, l) -> Conflicting m (l_remove c l).
Proof.
  unfold Conflicting. intros. funelim (find_unit m f).
  - discriminate.
  - apply H. congruence.
  - rewrite H in Heqcall. injection Heqcall as Heqcall. subst.
    funelim (find_unit_l m c0). rewrite Heq in Heqcall. apply find_some in Heqcall.
    destruct Heqcall. funelim (is_conflict m (l_remove c l0)).
    + congruence.
    + assumption.
    + congruence.
  - apply H. congruence.
Qed.

Lemma find_unit_undef: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  find_unit m f = Some (c, l) -> Undef m l.
Proof.
  unfold Undef. intros. funelim (find_unit m f).
  - discriminate.
  - apply (H c0 l0). congruence.
  - rewrite H in Heqcall. injection Heqcall as Heqcall. subst. funelim (find_unit_l m c0).
    rewrite Heq in Heqcall. apply find_some in Heqcall. destruct Heqcall.
    funelim (is_conflict m (l_remove c l0)).
    + congruence.
    + apply (undef_remove_false__undef m c0 l0); assumption.
    + congruence.
  - apply (H c0 l). congruence.
Qed.

Lemma find_decision_decomp: forall (m: PA) (f: CNF) (l: Lit), 
  find_decision m f = Some l -> exists (c: Clause), find_undef_l m c = Some l /\ In c f.
Proof.
  intros. funelim (find_decision m f).
  - congruence.
  - rewrite H in Heqcall. injection Heqcall as Heqcall. subst l0. exists c. split.
    + assumption.
    + left. reflexivity.
  - rewrite H in Heqcall. apply Hind in Heqcall. destruct Heqcall. destruct H0.
    exists x. split.
    + assumption.
    + right. assumption.
Qed.

Lemma find_undef_l_in_c: forall (m: PA) (c: Clause) (l: Lit), find_undef_l m c = Some l -> In l c.
Proof.
  intros. funelim (find_undef_l m c). rewrite H in Heqcall. 
  apply find_some in Heqcall. destruct Heqcall. assumption.
Qed.

Lemma find_undef_l_undef: forall (m: PA) (c: Clause) (l: Lit), find_undef_l m c = Some l -> Undef m l.
Proof. 
  unfold Undef. intros. funelim (find_undef_l m c). rewrite H in Heqcall. 
  apply find_some in Heqcall. destruct Heqcall. funelim (is_undefined_l m l).
  - congruence.
  - assumption.
Qed.

Lemma next_state_sound: forall (s s': State), next_state s = Some s' -> s ==> s'.
Proof.
  intros. funelim (next_state s); rewrite H in Heqcall; clear H; symmetry in Heqcall.
  - discriminate.
  - destruct (find_conflict m f) as [c_conflict|] eqn:find_conflict.
    + destruct (inspect (split_last_decision m)) as [[(m_split, l_split)|] split_last_decision].
      (* t_backtrack *)
      * injection Heqcall as Heqcall. rewrite Heqcall. 
        pose proof (split_decomp _ _ _ split_last_decision) as decomp. 
        destruct decomp as [n_split [decomp no_dec]]. subst m.
        apply (t_backtrack m_split n_split f c_conflict l_split).
        -- apply (find_conflict_c_in_f (m_split ++d l_split ++a n_split) f c_conflict). assumption.
        -- apply (find_conflict_conflicting (m_split ++d l_split ++a n_split) f c_conflict). assumption.
        -- assumption.
      (* t_fail *)
      * injection Heqcall as Heqcall. rewrite Heqcall. apply (t_fail m f c_conflict).
        -- apply (find_conflict_c_in_f m f c_conflict). assumption.
        -- apply (find_conflict_conflicting m f c_conflict). assumption.
        -- apply (no_split__no_decision m). assumption.
    + destruct (inspect (find_unit m f)) as [[(c_unit, l_unit)|] find_unit].
      (* t_unit *)
      * injection Heqcall as Heqcall. rewrite Heqcall. apply (t_unit m f c_unit l_unit).
        -- apply (find_unit_l_in_c m f c_unit l_unit). assumption.
        -- apply (find_unit_c_in_f m f c_unit l_unit). assumption.
        -- apply (find_unit_conflicting m f c_unit l_unit). assumption.
        -- apply (find_unit_undef m f c_unit l_unit). assumption.
      * destruct (inspect (find_decision m f)) as [[l_decide|] find_decision].
        (* t_decide *)
        -- injection Heqcall as Heqcall. rewrite Heqcall.
           destruct (find_decision_decomp m f l_decide find_decision) as [c_decide [Hc Hc_in_f]].
           apply (t_decide m f c_decide l_decide).
          ++ left. apply (find_undef_l_in_c m c_decide l_decide). assumption.
          ++ assumption.
          ++ apply (find_undef_l_undef m c_decide l_decide). assumption.
        -- discriminate.
Qed.

Lemma find_conflict_exists: forall (m: PA) (f: CNF) (c: Clause),
  In c f -> Conflicting m c -> exists (c': Clause), find_conflict m f = Some c'.
Proof.
  unfold Conflicting. intros m f c Hin Hc. destruct (find_conflict m f) as [c'|] eqn:Hfind.
  - now exists c'.
  - simp find_conflict in Hfind. pose proof (find_none (is_conflict m) f Hfind c Hin) as contra.
    simp is_conflict in contra. rewrite Hc in contra. simpl in contra. discriminate.
Qed.

Lemma find_undef_l_exists : forall (m: PA) (c: Clause) (l: Lit),
  In l c -> Undef m l -> exists (l': Lit), find_undef_l m c = Some l'.
Proof.
  unfold Undef. intros. destruct (find_undef_l m c) eqn:G.
  - now exists l0.
  - simp find_undef_l in G. apply (find_none (is_undefined_l m) c G l) in H.
    simp is_undefined_l in H. rewrite H0 in H. discriminate.
Qed.

Lemma find_decision_exists: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  In l c -> In c f -> Undef m l -> exists (l': Lit), find_decision m f = Some l'.
Proof. 
  intros. funelim (find_decision m f).
  - contradiction.
  - now exists l.
  - apply (Hind c0 l); auto. inversion H0; auto. subst.
    destruct (find_undef_l_exists m c0 l H H1). congruence.
Qed.

(* The rhs is weaker because there could be multiple { s': State | s ==> s' }. *)
Lemma next_state_exists: forall (s s': State), s ==> s' -> exists (s'': State), next_state s = Some s''.
Proof.
  intros. inversion H as 
    [
      m f c_conflict Hwf Hc_in_f Hconflict Hno_dec |
      m f c_unit l_unit Hwf Hwf' Hl_in_c Hc_in_f Hconflict Hundef |
      m f c_decide l_decide Hwf Hwf' Hx_in_c Hc_in_f Hundef |
      m_split n_split f c_conflict l_split Hwf Hwf' Hc_in_f Hconflict Hno_dec
    ]; subst s s'.
  (* t_fail *)
  - funelim (next_state (state m f Hwf)).
    + discriminate.
    + injection eqargs as <- <-.
      destruct (find_conflict m f) as [c_conflict'|] eqn:Hfind_conflict.
      * destruct (inspect (split_last_decision m)) as [[(m_split, l_split)|] Hsplit].
        -- now exists (state (m_split ++p (¬l_split)) f (wf_backtrack m m_split f l_split Hsplit Hwf)).
        -- now exists fail.
      * destruct (find_conflict_exists m f c_conflict Hc_in_f Hconflict). congruence.
  (* t_unit *)
  - funelim (next_state (state m f Hwf)).
    + discriminate.
    + injection eqargs as <- <-.
      destruct (find_conflict m f) as [c_conflict'|] eqn:Hfind_conflict.
      * destruct (inspect (split_last_decision m)) as [[(m_split, l_split)|] Hsplit].
        -- now exists (state (m_split ++p (¬l_split)) f (wf_backtrack m m_split f l_split Hsplit Hwf)).
        -- now exists fail.
      * destruct (inspect (find_unit m f)) as [[(c_unit', l_unit')|] Hfind_unit].
        -- now exists (state (m ++p l_unit') f (wf_unit m f c_unit' l_unit' Hfind_unit Hwf)).
        -- destruct (inspect (find_decision m f)) as [[l_decide|] Hfind_dec].
          ++ now exists (state (m ++d l_decide) f (wf_decide m f l_decide Hfind_dec Hwf)).
          ++ destruct (find_decision_exists m f c_unit l_unit Hl_in_c Hc_in_f Hundef). congruence.
  (* t_decide *)
  - funelim (next_state (state m f Hwf)).
    + discriminate.
    + injection eqargs as <- <-.
      destruct (find_conflict m f) as [c_conflict'|] eqn:Hfind_conflict.
      * destruct (inspect (split_last_decision m)) as [[(m_split, l_split)|] Hsplit].
        -- now exists (state (m_split ++p (¬l_split)) f (wf_backtrack m m_split f l_split Hsplit Hwf)).
        -- now exists fail.
      * destruct (inspect (find_unit m f)) as [[(c_unit', l_unit')|] Hfind_unit].
        -- now exists (state (m ++p l_unit') f (wf_unit m f c_unit' l_unit' Hfind_unit Hwf)).
        -- destruct (inspect (find_decision m f)) as [[l_decide'|] Hfind_dec].
          ++ now exists (state (m ++d l_decide') f (wf_decide m f l_decide' Hfind_dec Hwf)).
          ++ destruct Hx_in_c as [Hl_in_c|Hnegl_in_c].
            ** destruct (find_decision_exists m f c_decide l_decide Hl_in_c Hc_in_f Hundef). congruence.
            ** apply undef__neg_undef in Hundef.
               destruct (find_decision_exists m f c_decide (¬l_decide) Hnegl_in_c Hc_in_f Hundef). congruence.
  (* t_backtrack *)
  - funelim (next_state (state (m_split ++d l_split ++a n_split) f Hwf)).
    + discriminate.
    + injection eqargs as ? <-. rewrite <- H0 in *. clear H0.
      destruct (find_conflict m f) as [c_conflict'|] eqn:Hfind_conflict.
      * destruct (inspect (split_last_decision m)) as [[(m_split', l_split')|] Hsplit].
        -- now exists (state (m_split' ++p (¬l_split')) f (wf_backtrack m m_split' f l_split' Hsplit Hwf)).
        -- now exists fail.
      * destruct (inspect (find_unit m f)) as [[(c_unit', l_unit')|] Hfind_unit].
        -- now exists (state (m ++p l_unit') f (wf_unit m f c_unit' l_unit' Hfind_unit Hwf)).
        -- destruct (inspect (find_decision m f)) as [[l_decide'|] Hfind_dec].
          ++ now exists (state (m ++d l_decide') f (wf_decide m f l_decide' Hfind_dec Hwf)).
          ++ destruct (find_conflict_exists m f c_conflict Hc_in_f Hconflict). congruence.
Qed.

Lemma next_state_final_refl: forall (s: State), next_state s = None <-> Final s.
Proof.
  unfold Final. unfold not. intros. split.
  - intros. destruct H0. apply next_state_exists in H0. destruct H0. congruence.
  - intros. destruct (next_state s) eqn:G.
    + apply next_state_sound in G. exfalso. apply H. exists s0. assumption.
    + reflexivity.
Qed.

Equations max_atom_c (c: Clause): nat :=
max_atom_c []           := 0;
max_atom_c (Pos p :: c) := max p (max_atom_c c);
max_atom_c (Neg p :: c) := max p (max_atom_c c).

Equations max_atom_f (f: CNF): nat :=
max_atom_f []       := 0;
max_atom_f (c :: f) := max (max_atom_c c) (max_atom_f f).

Equations score_aux (m: PA) (n x: nat): list nat :=
score_aux []        n x := [n - x];
score_aux (m ++p l) n x := score_aux m n (S x);
score_aux (m ++d l) n x := n - x :: score_aux m n 0.

Equations score (m: PA) (f: CNF): list nat :=
score m f :=
  let max_atom := max_atom_f f in
  let unpadded := rev (score_aux m (S max_atom) 0) in
  let  padding := repeat (S max_atom) (S (S max_atom) - length unpadded) in
  unpadded ++ padding.

Equations score_total (m: PA) (f: CNF): nat :=
score_total m f := S (max_atom_f f) - length m.

Module ScoreExamples.
  Example score_1: score [] [[Pos 0; Pos 1]] = [2; 2; 2].
  Proof. reflexivity. Qed.

  Example score_2: score ([] ++p Pos 0) [[Pos 0; Pos 1]] = [1; 2; 2].
  Proof. reflexivity. Qed.

  Example score_3: score ([] ++d Pos 0) [[Pos 0; Pos 1]] = [2; 2; 2].
  Proof. reflexivity. Qed.

  Example score_4: score ([] ++d Neg 0 ++p Pos 1) [[Pos 0; Pos 1]] = [2; 1; 2].
  Proof. reflexivity. Qed.

  Example score_total_1: score_total [] [[Pos 0; Pos 1]] = 2.
  Proof. reflexivity. Qed.

  Example score_total_2: score_total ([] ++p Pos 0) [[Pos 0; Pos 1]] = 1.
  Proof. reflexivity. Qed.

  Example score_total_3: score_total ([] ++d Pos 0) [[Pos 0; Pos 1]] = 1.
  Proof. reflexivity. Qed.

  Example score_total_4: score_total ([] ++d Neg 0 ++p Pos 1) [[Pos 0; Pos 1]] = 0.
  Proof. reflexivity. Qed.
End ScoreExamples.

Inductive FailLt: relation State :=
| f_fail (m: PA) (f: CNF) (Hwf: WellFormed m f):
  FailLt fail (state m f Hwf).

Lemma wf_fail_lt: well_founded FailLt.
Proof.
  unfold well_founded. intros m. constructor. intros m' Hlt. destruct Hlt.
  constructor. intros m' Hlt. inversion Hlt.
Qed.

Inductive PrefixLt (x: nat): relation (list nat) :=
| p_head (m m': list nat) (n n': nat):
  length (n :: m) <= x ->
  length (n' :: m') <= x ->
  n < n' ->
  PrefixLt x (n :: m) (n' :: m')
| p_tail (m m': list nat) (n: nat):
  length (n :: m) <= x ->
  length (n :: m') <= x ->
  PrefixLt x m m' ->
  PrefixLt x (n :: m) (n :: m').

Inductive cll: relation (list nat) :=
| hd_less (n n': nat) (m m': list nat):
  n < n' ->
  cll (n :: m) (n' :: m')
| tl_less (n: nat) (m m': list nat):
  cll m m' ->
  cll (n :: m) (n :: m').

Definition bcll (n: nat) (m m': list nat): Prop :=
  length m <= n /\ length m' <= n /\ cll m m'.

Lemma bcll__prefix_lt: forall (x: nat) (m m': list nat),
  bcll x m m' <-> PrefixLt x m m'.
Proof.
  intros. split.
  - intros. inversion H as [H1 [H2 H3]]. induction H3.
    + apply p_head.
      * assumption.
      * assumption.
      * assumption.
    + apply p_tail.
      * assumption.
      * assumption.
      * apply IHcll.
        -- unfold bcll. split.
          ++ simpl in H1. apply le_S in H1. now apply le_S_n.
          ++ split. 
            ** simpl in H2. apply le_S in H2. now apply le_S_n.
            ** assumption.
        -- simpl in H1. apply le_S in H1. now apply le_S_n.
        -- simpl in H2. apply le_S in H2. now apply le_S_n.
  - intros. 
    + induction H.
      * unfold bcll. split.
        -- assumption.
        -- split.
          ++ assumption.
          ++ apply hd_less. assumption.
      * unfold bcll. split.
        -- assumption.
        -- split.
          ++ assumption.
          ++ apply tl_less. destruct IHPrefixLt as [_ [_ H2]]. assumption.
Qed.

Definition list_to_sum (n: nat) (m: list nat): nat * list nat + unit :=
  if List.length m <=? n then
  match m with
  | nil => inr tt
  | h :: t => inl (h, t)
  end else inr tt.

Definition bcll' (n: nat) (m m': list nat): Prop :=
  le_AsB _ _ (slexprod _ _ lt (bcll n)) (fun _ _ => False) (list_to_sum (S n) m) (list_to_sum (S n) m').

Lemma cll_incl {n} (m m': list nat): bcll (S n) m m' -> bcll' n m m'.
Proof.
  intros [Hl1 [Hl2 H]]. unfold bcll'. unfold list_to_sum.
  rewrite 2 leb_correct; auto.
  destruct H; constructor.
  + constructor 1. auto.
  + constructor 2. simpl in *; split; [| split]; auto; lia.
Qed.

Lemma wf_bcll: forall (x: nat), well_founded (bcll x).
Proof.
  induction x.
  - intros l. constructor. intros [] [H1 [H2 H3]].
    + inversion H3.
    + simpl in H1; lia.
  - apply (wf_incl _ _ (fun l1 l2 => bcll' x l1 l2)).
    + red. apply cll_incl.
    + unfold bcll'.
      apply wf_inverse_image.
      apply wf_disjoint_sum.
      * apply wf_slexprod.
        -- apply lt_wf.
        -- apply IHx.
      * constructor; intros ? [].
Qed.

Lemma wf_prefix_lt: forall x, well_founded (PrefixLt x).
Proof.
  intro x. apply (wf_incl _ _ (bcll x)).
  - unfold inclusion. now apply bcll__prefix_lt.
  - apply wf_bcll.
Qed.

Definition TotalLt: relation nat := lt.

Lemma wf_total_lt: well_founded TotalLt.
Proof. apply lt_wf. Qed.

Definition StateLexLt (f: CNF): relation (list nat * nat) :=
  slexprod _ _ (PrefixLt (S (S (max_atom_f f)))) TotalLt.

Lemma wf_state_lex_lt: forall (f: CNF), well_founded (StateLexLt f).
Proof.
  intros. apply wf_slexprod.
  - apply wf_prefix_lt.
  - apply wf_total_lt.
Qed.

Equations state_measure (s: State): list nat * nat :=
state_measure fail          := ([]       , 0              );
state_measure (state m f _) := (score m f, score_total m f).

Definition StateLt (f: CNF): relation State := union _ FailLt (MR (StateLexLt f) state_measure).

Lemma wf_state_lt: forall (f: CNF), well_founded (StateLt f).
Proof.
  intros. apply wf_union.
  - unfold commut. intros. inversion H. subst. exists (state m f0 Hwf).
    + unfold MR in H0. simp state_measure in H0. inversion H0.
      * subst. inversion H3.
      * subst. inversion H3.
    + unfold MR in H0. simp state_measure in H0. inversion H0.
      * subst. inversion H3.
      * subst. inversion H3.
  - apply wf_fail_lt.
  - apply wf_MR. apply wf_state_lex_lt.
Qed.
  
Notation "s '>>[' f ']' s'" := (StateLt f s' s) (at level 40, format "s '/ ' '[' >>[ ']' f ] '/ ' s'").

Equations prefix_lt (x: nat) (m m': list nat): bool :=
prefix_lt _     []       _            := false;
prefix_lt _     _        []           := false;
prefix_lt 0     _        _            := false;
prefix_lt (S x) (n :: m) (n' :: m') :=
  (length m <=? x) && 
  (length m' <=? x) &&
  ((n <? n') || (n =? n')%nat && (prefix_lt x m m')).

Lemma prefix_step: forall (x: nat) (m m': list nat),
  length m <= x -> length m' <= x -> PrefixLt x m m' <-> PrefixLt (S x) m m'.
Proof. 
  intros. split.
  - intros. induction H1.
    + apply p_head.
      * now apply le_S in H1.
      * now apply le_S in H2.
      * assumption.
    + apply p_tail.
      * now apply le_S in H1.
      * now apply le_S in H2.
      * apply IHPrefixLt.
        -- apply le_S in H1. now apply le_S_n.
        -- apply le_S in H2. now apply le_S_n.
  - intros. induction H1.
    + apply p_head.
      * assumption.
      * assumption.
      * assumption.
    + apply p_tail.
      * assumption.
      * assumption.
      * apply IHPrefixLt.
        -- now apply le_S_n.
        -- now apply le_S_n. 
Qed.

Lemma prefix_lt_refl: forall (x: nat) (m m': list nat), 
  prefix_lt x m m' = true <-> PrefixLt x m m'.
Proof.
  intros. funelim (prefix_lt x m m').
  - split.
    + intros. discriminate.
    + intros. inversion H.
  - split.
    + intros. discriminate.
    + intros. inversion H.
  - split.
    + intros. discriminate.
    + intros. inversion H; subst.
      * simpl in H4. inversion H4.
      * simpl in H4. inversion H4.
  - split.
    + intros. rewrite Heqcall in H0. simp prefix_lt in H0. destruct (n <? n') eqn:G.
      * apply p_head.
        -- apply andb_true_iff in H0 as [H1 H2]. apply andb_true_iff in H1 as [H1 H3].
           simpl. apply le_n_S. now apply Nat.leb_le.
        -- apply andb_true_iff in H0 as [H1 H2]. apply andb_true_iff in H1 as [H1 H3].
           simpl. apply le_n_S. now apply Nat.leb_le.
        -- now apply Nat.ltb_lt.
      * simpl in H0. apply andb_true_iff in H0 as [H1 H2].
        apply andb_true_iff in H1 as [H1 H3]. apply andb_true_iff in H2 as [H2 H4].
        rewrite Nat.eqb_eq in H2. subst n'. apply p_tail.
        -- simpl. apply le_n_S. now apply Nat.leb_le.
        -- simpl. apply le_n_S. now apply Nat.leb_le.
        -- apply H in H4. rewrite <- prefix_step.
          ++ assumption.
          ++ now apply Nat.leb_le.
          ++ now apply Nat.leb_le.
    + intros. inversion H0; subst.
      * apply Nat.ltb_lt in H7. rewrite H7. simpl.
        simpl in H5, H6. apply le_S_n in H5, H6.
        apply Nat.leb_le in H5, H6. now rewrite H5, H6.
      * simpl in H5, H6. apply le_S_n in H5, H6.
        apply (prefix_step x m m' H5 H6) in H7.
        apply Nat.leb_le in H5, H6. rewrite H5, H6.
        simpl. rewrite <- H in H7. rewrite H7.
        rewrite Nat.eqb_refl. simpl. apply orb_true_r.
Qed.

Lemma max_atom_c_le: forall (c: Clause) (l: Lit) (p: Atom),
  In l c ->
  extract l = p ->
  p <= max_atom_c c.
Proof.
  intros c l p Hin Heq. funelim (max_atom_c c).
  - contradiction.
  - inversion Hin.
    + subst l. simp extract. apply Nat.max_le_iff. now left.
    + destruct l as [p'|p'].
      * simp extract. apply (H (Pos p') p') in H0.
        -- apply Nat.max_le_iff. now right.
        -- reflexivity.
      * simp extract. apply (H (Neg p') p') in H0.
        -- apply Nat.max_le_iff. now right.
        -- reflexivity.
  - inversion Hin.
    + subst l. simp extract. apply Nat.max_le_iff. now left.
    + destruct l as [p'|p'].
      * simp extract. apply (H (Pos p') p') in H0.
        -- apply Nat.max_le_iff. now right.
        -- reflexivity.
      * simp extract. apply (H (Neg p') p') in H0.
        -- apply Nat.max_le_iff. now right.
        -- reflexivity.
Qed.

Lemma max_atom_f_le: forall (f: CNF) (c: Clause) (l: Lit) (p: Atom),
  In l c ->
  In c f ->
  extract l = p ->
  p <= max_atom_f f.
Proof.
  intros f c l p Hl_in_c Hc_in_f Heq. funelim (max_atom_f f).
  - contradiction.
  - inversion Hc_in_f.
    + subst c0. destruct l as [p|p].
      * simp extract. apply Nat.max_le_iff. left. apply (max_atom_c_le c (Pos p) p).
        -- assumption.
        -- reflexivity.
      * simp extract. apply Nat.max_le_iff. left. apply (max_atom_c_le c (Neg p) p).
        -- assumption.
        -- reflexivity.
    + destruct l as [p|p].
      * apply Nat.max_le_iff. right. simp extract. apply (H c0 (Pos p) p).
        -- assumption.
        -- assumption.
        -- reflexivity.
      * apply Nat.max_le_iff. right. simp extract. apply (H c0 (Neg p) p).
        -- assumption.
        -- assumption.
        -- reflexivity.
Qed.

Lemma wf_le: forall (m: PA) (f: CNF) (p: Atom),
  WellFormed m f ->
  In p (map extract (map fst m)) ->
  p <= max_atom_f f.
Proof.
  intros m f p Hwf Hin. apply in_map_iff in Hin as [l [Heq Hin]].
  apply in_map_iff in Hin as [(l', a) [Heq' Hin]]. simpl in Heq'. subst l'.
  destruct Hwf as [Hnodup Hbounded]. apply Hbounded in Hin as [c [Hc_in_f [Hl_in_c|Hnegl_in_c]]].
  - destruct l as [p'|p'].
    + simp extract in Heq. subst p'. apply (max_atom_f_le f c (Pos p)).
      * assumption.
      * assumption.
      * reflexivity.
    + simp extract in Heq. subst p'. apply (max_atom_f_le f c (Neg p)).
      * assumption.
      * assumption.
      * reflexivity.
  - destruct l as [p'|p'].
    + simp extract in Heq. subst p'. apply (max_atom_f_le f c (Neg p)).
      * assumption.
      * assumption.
      * reflexivity.
    + simp extract in Heq. subst p'. apply (max_atom_f_le f c (Pos p)).
      * assumption.
      * assumption.
      * reflexivity.
Qed.

Lemma pigeon: forall (l: list nat) (m: nat),
  NoDup l ->
  (forall (n: nat), In n l -> n <= m) ->
  length l <= S m.
Proof.
  intros l m Hnodup Hin_le.
  assert (Hincl: incl l (seq 0 (S m))).
  - unfold incl. intros n Hin. apply in_seq. specialize (Hin_le n Hin). lia.
  - apply (@NoDup_incl_length _ _ (seq 0 (S m))) in Hnodup.
    + now rewrite length_seq in Hnodup.
    + assumption.
Qed.

Lemma wf_length_le: forall (m: PA) (f: CNF),
  WellFormed m f ->
  length m <= S (max_atom_f f).
Proof.
  intros m f Hwf. assert (Heq: length m = length (map extract (map fst m))).
  - now repeat rewrite length_map.
  - rewrite Heq. apply pigeon.
    + now destruct Hwf.
    + intros. apply (wf_le m); assumption.
Qed.

Lemma score_aux_length: forall (m: PA) (n n': nat),
  length (score_aux m n n') <= S (length m).
Proof.
  intros. funelim (score_aux m n n').
  - simpl. apply le_n.
  - simpl. now apply le_n_S.
  - simpl. lia.
Qed.

Lemma score_aux_length_le: forall (m: PA) (f: CNF) (l: Lit) (a: Ann) (n x: nat),
  WellFormed ((l, a) :: m) f ->
  length (score_aux m n x) <= S (max_atom_f f).
Proof.
  intros. 
  pose proof (score_aux_length m n x).
  pose proof (score_aux_length (m ++d l) n x).
  pose proof (wf_length_le ((l, a) :: m) f H).
  simpl in *. lia.
Qed.

Lemma score_aux_in_le: forall (m: PA) (n x k: nat),
  In k (score_aux m n x) -> k <= n.
Proof.
  intros m n x k Hin. funelim (score_aux m n x).
  - simp score_aux in Hin. inversion Hin.
    + lia.
    + inversion H.
  - rewrite <- Heqcall in Hin. inversion Hin.
    + lia.
    + now apply H.
  - rewrite <- Heqcall in Hin. now apply H.
Qed.

Lemma score_dec: forall (m: PA) (f: CNF) (l: Lit),
  WellFormed (m ++d l) f ->
  score (m ++d l) f = score m f.
Proof.
  intros. simp score. simpl. simp score_aux. simpl.
  rewrite length_app. simpl. rewrite Nat.add_1_r. rewrite <- app_assoc.
  destruct (length (rev (score_aux m (S (max_atom_f f)) 0))) eqn:G.
  - reflexivity.
  - destruct n.
    + simp pad. now rewrite Nat.sub_0_r.
    + rewrite length_rev in G. 
      pose proof (score_aux_length_le m f l dec (S (max_atom_f f)) 0 H).
      assert (T: S (max_atom_f f - S n) = max_atom_f f - n).
      * lia.
      * now rewrite <- T.
Qed.

Lemma total_decide: forall (m: PA) (f: CNF) (l: Lit),
  WellFormed (m ++d l) f ->
  TotalLt (score_total (m ++d l) f) (score_total m f).
Proof.
  intros m f l Hwf. pose proof (wf_length_le (m ++d l) f Hwf).
  unfold TotalLt. simp score_total. simpl in *. destruct (length m); lia.
Qed.

Lemma prefix_repeat: forall (l1 l2: list nat) (m n x x': nat),
  (forall (k: nat), In k l1 -> k <= n) ->
  (forall (k: nat), In k l2 -> k <= n) ->
  length l1 + x  <= m ->
  length l2 + x' <= m ->
  PrefixLt m l1 l2 -> PrefixLt m (l1 ++ repeat n x) (l2 ++ repeat n x').
Proof.
  intros l1 l2 m n x x' Hin_l1 Hin_l2 Hle_l1 Hle_l2 Hlt. 
  induction Hlt as [l1 l2 a1 a2 _ _ Hlt|l1 l2 a _ _ _ IH].
  - simpl. apply p_head.
    + simpl. rewrite length_app. now rewrite repeat_length.
    + simpl. rewrite length_app. now rewrite repeat_length.
    + assumption.
  - simpl. apply p_tail.
    + simpl. rewrite length_app. now rewrite repeat_length.
    + simpl. rewrite length_app. now rewrite repeat_length.
    + apply IH.
      * intros. apply Hin_l1. now right.
      * intros. apply Hin_l2. now right.
      * simpl in Hle_l1. lia.
      * simpl in Hle_l2. lia.
Qed.

Lemma prefix_postfix: forall (m1 m2 n: list nat) (x: nat),
  length (m1 ++a n) <= x ->
  length (m2 ++a n) <= x ->
  PrefixLt x m1 m2 ->
  PrefixLt x (m1 ++a n) (m2 ++a n).
Proof. 
  intros m1 m2 n. generalize dependent m1. generalize dependent m2.
  induction n.
  - now intros.
  - intros. simpl in *. apply p_tail.
    + assumption.
    + assumption.
    + apply IHn.
      * lia.
      * lia.
      * assumption.
Qed.

Lemma prefix_shift: forall (m: PA) (f: CNF) (x: nat),
  WellFormed m f ->
  x + length m <= max_atom_f f ->
  PrefixLt (S (S (max_atom_f f))) 
           (rev (score_aux m (S (max_atom_f f)) (S x)))
           (rev (score_aux m (S (max_atom_f f)) x)).
Proof.
  intros m f x Hwf Hle. generalize dependent x.
  induction m as [|[l [|]] m IH].
  - intros. simp score_aux. simpl. destruct x eqn:Heq.
    + apply p_head.
      * simpl. lia.
      * simpl. lia.
      * lia.
    + apply p_head.
      * simpl. lia.
      * simpl. lia.
      * lia.
  - intros. simp score_aux. simpl. destruct x eqn:Heq.
    * apply prefix_postfix.
      -- pose proof (score_aux_length_le m f l dec (S (max_atom_f f)) 0 Hwf).
         rewrite length_app. rewrite length_rev. simpl. lia.
      -- pose proof (score_aux_length_le m f l dec (S (max_atom_f f)) 0 Hwf).
         rewrite length_app. rewrite length_rev. simpl. lia.
      -- apply p_head.
        ++ simpl. lia.
        ++ simpl. lia.
        ++ lia.
    * apply prefix_postfix.
      -- pose proof (score_aux_length_le m f l dec (S (max_atom_f f)) 0 Hwf).
         rewrite length_app. rewrite length_rev. simpl. lia.
      -- pose proof (score_aux_length_le m f l dec (S (max_atom_f f)) 0 Hwf).
         rewrite length_app. rewrite length_rev. simpl. lia.
      -- apply p_head.
        ++ simpl. lia.
        ++ simpl. lia.
        ++ lia.
  - intros. simp score_aux. apply IH.
    * now apply wf_cons__wf in Hwf.
    * simpl in Hle. lia.
Qed.

Lemma prefix_prefix: forall (m1 m2 n: list nat) (x: nat),
  length (n ++a m2) <= x ->
  PrefixLt x m1 m2 ->
  PrefixLt x m1 (n ++a m2).
Proof.
  intros m1 m2. generalize dependent m1.
  induction m2.
  - intros m1 n x Hle Hlt. inversion Hlt.
  - intros m1 n x Hle Hlt. destruct m1.
    + inversion Hlt.
    + simpl. inversion Hlt.
      * apply p_head.
        -- assumption.
        -- assumption.
        -- assumption.
      * apply p_tail.
        -- assumption.
        -- assumption.
        -- apply IHm2.
          ++ rewrite length_app in *. simpl in Hle. lia.
          ++ assumption.
Qed.

Lemma score_aux_split: forall (m1 m2: PA) (l: Lit) (n x: nat),
  score_aux (m1 ++d l ++a m2) n x = (score_aux m1 n 0) ++a (score_aux m2 n x).
Proof.
  intros.
  generalize dependent x.
  induction m2.
  - intros. rewrite app_nil_l. simp score_aux. simpl. reflexivity.
  - intros. simpl. destruct a. destruct a.
    + simp score_aux. simpl. now rewrite IHm2.
    + simp score_aux.
Qed.

Lemma prefix_prop: forall (m: PA) (f: CNF) (l: Lit),
  WellFormed (m ++p l) f ->
  PrefixLt (S (S (max_atom_f f))) (score (m ++p l) f) (score m f).
Proof.
  intros m f l Hwf. 
  pose proof (wf_cons__wf m f l prop Hwf) as Hwf'. 
  simp score. simpl. apply prefix_repeat.
  - intros. rewrite <- in_rev in H. now apply score_aux_in_le in H.
  - intros. rewrite <- in_rev in H. now apply score_aux_in_le in H.
  - repeat rewrite length_rev.
    destruct (length (score_aux (m ++p l) (S (max_atom_f f)) 0)) eqn:Heq.
    + lia.
    + destruct n.
      * lia.
      * pose proof (score_aux_length (m ++p l) (S (max_atom_f f)) 0).
        pose proof (wf_length_le (m ++p l) f Hwf) .
        simpl in *. lia.
  - repeat rewrite length_rev.
    destruct (length (score_aux m (S (max_atom_f f)) 0)) eqn:Heq.
    + lia.
    + destruct n.
      * lia.
      * pose proof (score_aux_length m (S (max_atom_f f)) 0).
        pose proof (wf_length_le m f Hwf').
        simpl in *. lia.
  - simp score_aux. apply prefix_shift.
    + assumption.
    + apply wf_length_le in Hwf. simpl in Hwf. lia.
Qed.

Lemma prefix_app: forall (m n: PA) (f: CNF) (l l': Lit),
  WellFormed (m ++p l) f ->
  WellFormed (m ++d l' ++a n) f ->
  PrefixLt (S (S (max_atom_f f))) (score (m ++p l) f) (score (m ++d l' ++a n) f).
Proof.
  intros m n f l l' Hwf Hwf'. simp score. simpl. apply prefix_repeat.
  - intros. rewrite <- in_rev in H. now apply score_aux_in_le in H.
  - intros. rewrite <- in_rev in H. now apply score_aux_in_le in H.
  - repeat rewrite length_rev.
    destruct (length (score_aux (m ++p l) (S (max_atom_f f)) 0)) eqn:Heq.
    + lia.
    + destruct n0.
      * lia.
      * pose proof (score_aux_length (m ++p l) (S (max_atom_f f)) 0).
        pose proof (wf_length_le (m ++p l) f Hwf) .
        simpl in *. lia.
  - repeat rewrite length_rev.
    destruct (length (score_aux (m ++d l' ++a n) (S (max_atom_f f)) 0)) eqn:Heq.
    + lia.
    + destruct n0.
      * lia.
      * pose proof (score_aux_length (m ++d l' ++a n) (S (max_atom_f f)) 0).
        pose proof (wf_length_le (m ++d l' ++a n) f Hwf').
        simpl in *. lia.
  - rewrite score_aux_split. rewrite rev_app_distr. simp score_aux. apply prefix_prefix.
    + rewrite length_app. repeat rewrite length_rev.
      apply wf_length_le in Hwf'. rewrite length_app in Hwf'. simpl in Hwf'.
      pose proof (score_aux_length m (S (max_atom_f f)) 0).
      pose proof (score_aux_length n (S (max_atom_f f)) 0).
      lia.
    + apply prefix_shift.
      * now apply wf_cons__wf in Hwf.
      * apply wf_length_le in Hwf. simpl in Hwf. lia.
Qed.

Lemma trans__state_lt: forall (m: PA) (f: CNF) (s': State) (Hwf: WellFormed m f),
  state m f Hwf ==> s' -> state m f Hwf >>[f] s'.
Proof.
  intros. inversion H as 
    [
      m' f' c_conflict Hwf' Hc_in_f Hconflict Hno_dec |
      m' f' c_unit l_unit ? Hwf' Hl_in_c Hc_in_f Hconflict Hundef |
      m' f' c_decide l_decide ? Hwf' Hx_in_c Hc_in_f Hundef |
      m_split n_split f' c_conflict l_split ? Hwf' Hc_in_f Hconflict Hno_dec
    ]; subst s'; try subst m'; try subst f'.
  (* t_fail *)
  - unfold StateLt. now left.
  (* t_unit *)
  - unfold StateLt. right. unfold MR. simp state_measure. apply left_slex.
    now apply prefix_prop.
  (* t_decide *)
  - unfold StateLt. right. unfold MR. simp state_measure. rewrite score_dec.
    + apply right_slex. now apply total_decide.
    + assumption.
  (* t_backtrack *)
  - unfold StateLt. right. unfold MR. simp state_measure. rewrite <- H0. apply left_slex.
    apply prefix_app.
    + assumption.
    + now rewrite H0.
Qed.

Lemma next_state__state_lt: forall (m: PA) (f: CNF) (Hwf: WellFormed m f) (s': State), 
  next_state (state m f Hwf) = Some s' -> state m f Hwf >>[f] s'.
Proof. intros. apply trans__state_lt. apply next_state_sound. assumption. Qed.

Lemma next_state_options: forall (m: PA) (f: CNF) (Hwf: WellFormed m f),
  next_state (state m f Hwf) = None \/
  next_state (state m f Hwf) = Some fail \/ 
  exists (m': PA) (Hwf': WellFormed m' f), next_state (state m f Hwf) = Some (state m' f Hwf').
Proof.
  intros. funelim (next_state (state m f Hwf)).
  - left. reflexivity.
  - injection eqargs as eqargs. subst m0 f0. rewrite Heqcall. destruct (find_conflict m f).
    + destruct (inspect (split_last_decision m)) as [[(m_split, l_split)|] Hsplit].
      -- right. right. now exists (m_split ++p ¬l_split), ((wf_backtrack m m_split f l_split Hsplit Hwf)).
      -- right. now left.
    + destruct (inspect (find_unit m f)) as [[(c_unit, l_unit)|] Hfind_unit].
      * right. right. now exists (m ++p l_unit), (wf_unit m f c_unit l_unit Hfind_unit Hwf).
      * destruct (inspect (find_decision m f)) as [[l_dec|] Hfind_dec].
        -- right. right. now exists (m ++d l_dec), (wf_decide m f l_dec Hfind_dec Hwf).
        -- now left.
Qed.

Lemma trans_same_formula: forall (m m': PA) (f f': CNF) (Hwf: WellFormed m f) (Hwf': WellFormed m' f'), 
  state m f Hwf ==> state m' f' Hwf' -> f = f'.
Proof. intros. inversion H; subst; reflexivity. Qed.

Lemma trans_clos_same_formula: forall (m m': PA) (f f': CNF) (Hwf: WellFormed m f) (Hwf': WellFormed m' f'), 
  state m f Hwf ==>* state m' f' Hwf' -> f = f'.
Proof. 
  intros m m' f f' Hwf Hwf' H. apply clos_rt_rtn1_iff in H. 
  remember (state m f Hwf) as s eqn:Heqs.
  remember (state m' f' Hwf') as s' eqn:Heqs'.
  generalize dependent m. generalize dependent m'. generalize dependent f. generalize dependent f'.
  induction H.
  - intros. congruence.
  - intros. destruct y, z; try congruence.
    + inversion H.
    + subst. injection Heqs' as Heqs'. subst. apply trans_same_formula in H. subst.
      apply IHclos_refl_trans_n1 with (m':=m0) (m:=m) (Hwf':=Hwf0) (Hwf:=Hwf). reflexivity. reflexivity.
Qed.

Lemma initial_wf: forall (f: CNF), WellFormed [] f.
Proof.
  unfold WellFormed, NoDuplicates, Bounded. split.
  - constructor.
  - now intros.
Qed.

Lemma initial_refl: forall (f: CNF), state [] f (initial_wf f) ==>* state [] f (initial_wf f).
Proof. intros. apply rt_refl. Qed.

Section solve.
  Context (f: CNF). 
  
  Instance wf_state_lt_f: WellFounded (StateLt f) := wf_state_lt f.

  Equations solve_aux (s: State) (H: state [] f (initial_wf f) ==>* s): State by wf s (StateLt f) :=
  solve_aux s H with inspect (next_state s) :=
    | Some s' eqn:ns := solve_aux s' ((rt_trans _ _ _ s s' H (rt_step _ _ s s' (next_state_sound s s' ns))))
    | None    eqn:ns := s.
  Next Obligation.
    destruct s.
    - inversion ns.
    - destruct (next_state_options m f0 Hwf) as [G|[G|G]].
      + congruence.
      + rewrite ns in G. injection G as ->. now constructor.
      + rewrite ns in G. destruct G. destruct H0. injection H0 as ->.
        apply next_state_sound in ns. assert (state [] f (initial_wf f) ==>* state x f0 x0).
        * apply (rt_trans _ _ _ (state m f0 Hwf)).
          -- assumption.
          -- now apply rt_step.
        * apply trans_clos_same_formula in H0. subst f0. now apply trans__state_lt.
  Qed.

  Definition solve: State := solve_aux (state [] f (initial_wf f)) (initial_refl f).
End solve.

Module Satisfiability.
  Definition Total (m: PA) (f: CNF): Prop := forall (l: Lit) (c: Clause), In l c -> In c f -> Def m l.
  Definition Model (m: PA) (f: CNF): Prop := f_eval m f = Some true.

  Definition Sat (f: CNF): Prop := exists (m: PA), Model m f.
  Definition Unsat (f: CNF): Prop := ~ Sat f.

  Definition Entails (f f': CNF): Prop := forall (m: PA), Model m f -> Model m f'.
  Definition Equivalent (f f': CNF): Prop := Entails f f' /\ Entails f' f.

  Theorem fail_final: Final fail.
  Proof. unfold Final. unfold not. intros. inversion H. inversion H0. Qed.

  Theorem final_exists: forall (f: CNF),
    exists (s: State), state [] f (initial_wf f) ==>* s /\ Final s.
  Admitted.

  Theorem final_sat_refl: forall (m: PA) (f: CNF) (Hwf: WellFormed m f),
    state [] f (initial_wf f) ==>* state m f Hwf /\ Final (state m f Hwf) <-> Sat f.
  Admitted.

  Theorem final_unsat_refl: forall (f: CNF),
    state [] f (initial_wf f) ==>* fail /\ Final fail <-> Unsat f.
  Admitted.

  Theorem sat_decidable: forall (f: CNF), Sat f \/ Unsat f.
  Proof.
    intros. destruct (final_exists f) as [[|m f' Hwf] ].
    - right. now apply final_unsat_refl.
    - left. destruct H. assert (f = f').
      + now apply (trans_clos_same_formula [] m f f' (initial_wf f) Hwf).
      + subst f'. now apply (final_sat_refl m f Hwf).
  Qed.
End Satisfiability.

(*
Equations l_ann (m: PA) (l: Lit): option Ann :=
l_ann [] _ := None;
l_ann ((l', a) :: m) l with l =? l', l =? ¬l' :=
  | true, _    := Some a
  | _   , true := Some a
  | _   , _    := l_ann m l.

Equations option_bind {A B: Type} (f: A -> option B) (o: option A): option B :=
option_bind _ None     := None;
option_bind f (Some a) := f a.

Equations is_undefined_c (m: PA) (c: Clause): bool :=
is_undefined_c m c with c_eval m c := 
  | None := true
  | _    := false.

Lemma l_ann_prop_eq: forall (m: PA) (l: Lit), l_ann (m ++p l) l = Some prop. 
Proof. intros. simp l_ann. rewrite eqb_refl. simpl. reflexivity. Qed.

Lemma l_ann_prop_eq_neg: forall (m: PA) (l: Lit), l_ann (m ++p l) (¬l) = Some prop. 
Proof. 
  intros. simp l_ann. rewrite eqb_refl. pose proof (Neg.self_neq_neg l). apply eqb_neq in H.
  rewrite eqb_sym in H. rewrite H. simpl. reflexivity.
Qed.

Lemma l_ann_prop_neq: forall (m: PA) (l l': Lit), l' <> l /\ l' <> ¬l -> l_ann (m ++p l) l' = l_ann m l'. 
Proof. 
  intros. destruct H. simp l_ann. rewrite <- eqb_neq in H, H0. rewrite H, H0. simpl. reflexivity.
Qed.

Lemma no_decision__no_split: forall (m: PA), NoDecisions m -> split_last_decision m = None.
Proof.
  unfold NoDecisions. unfold not. intros. funelim (split_last_decision m).
  - reflexivity.
  - exfalso. apply H. exists l. now left.
  - apply H. intros. apply H0. destruct H1. exists x. now right.
Qed.

Lemma app_cancel: forall (m n: PA), m ++a n = m -> n = [].
Proof.
  induction m.
  - intros. rewrite app_nil_r in H. assumption.
  - intros. apply IHm. apply (app_inv_tail (a::m) _ []) in H. rewrite H. simpl. reflexivity.
Qed.

Lemma l_in_c__c_in_f__l_in_f: forall (f: CNF) (c: Clause) (l: Lit),
  In l c -> In c f -> l_in_f l f = true.
Proof. 
  intros. simp l_in_f. rewrite existsb_exists. exists c. split.
  - assumption.
  - simp l_in_c. rewrite orb_true_iff. left. rewrite existsb_exists. exists l. split.
    + assumption.
    + apply eqb_refl.
Qed.

Lemma split_last_dec: forall (m m' n: PA) (l l': Lit),
  NoDecisions n -> split_last_decision (m ++d l ++a n) = Some (m', l') -> l = l'.
Proof. 
  unfold NoDecisions. unfold not. intros. funelim (split_last_decision (m ++d l ++a n)).
  - congruence.
  - rewrite H0 in Heqcall. injection Heqcall as <- <-. destruct n.
    + rewrite app_nil_l in eqargs. now injection eqargs as <-.
    + injection eqargs as <-. exfalso. apply H. exists l. now left.
  - destruct n.
    + discriminate.
    + injection eqargs as eqargs. destruct p. destruct a.
      * exfalso. apply H0. exists l1. now left.
      * injection eqargs as <-. simpl in H1. simp split_last_decision in H1.
        simpl in Heqcall. simp split_last_decision in Heqcall.
        apply (H m0 m' n l0 l').
        -- intros. apply H0. destruct H3. exists x. now right.
        -- assumption.
        -- assumption.
        -- assumption.
Qed.

Lemma existsb_false_iff: forall (A: Type) (f: A -> bool) (l : list A),
  existsb f l = false <-> (forall (x: A), In x l -> f x = false).
Proof.
  induction l as [|a l IH]; simpl; intros.
  - split.
    + intros. contradiction.
    + intros. reflexivity.
  - rewrite orb_false_iff. rewrite IH. split.
    + intros [Ha Hl] x [Hx | Hx].
      * now subst.
      * now apply Hl.
    + intros. split.
      * apply H. now left.
      * intros. apply H. now right.
Qed.

Lemma l_in_f__neg_l_in_f: forall (f: CNF) (l: Lit), l_in_f l f = l_in_f (¬l) f.
Proof.
  intros. destruct (l_in_f l f) eqn:G.
  - simp l_in_f in *. apply existsb_exists in G as [c [Hc_in_f Hl_in_c]].
    simp l_in_c in *. apply orb_true_iff in Hl_in_c as [Hl_in_c|Hnegl_in_c].
    + symmetry. apply existsb_exists. exists c. split.
      * assumption.
      * simp l_in_c. apply orb_true_iff. right. now rewrite Neg.involutive.
    + symmetry. apply existsb_exists. exists c. split.
      * assumption.
      * simp l_in_c. apply orb_true_iff. now left.
  - simp l_in_f in *. rewrite existsb_false_iff in G. symmetry. rewrite existsb_false_iff.
    intros. apply G in H. simp l_in_c in *. rewrite Neg.involutive. now rewrite orb_comm.
Qed.

(* Temporarily has `n` for testing, until termination in proven. *)
Equations solve_n (n: nat) (s: State): State :=
solve_n 0     _ := s;
solve_n (S n) s with next_state s :=
  | Some s' := solve_n n s'
  | None := s.

Lemma negl_in_c__c_in_f__l_in_f: forall (f: CNF) (c: Clause) (l: Lit),
  In (¬l) c -> In c f -> l_in_f l f = true.
Proof. 
  intros. simp l_in_f. rewrite existsb_exists. exists c. split.
  - assumption.
  - simp l_in_c. rewrite orb_true_iff. right. rewrite existsb_exists. exists (¬l). split.
    + assumption.
    + apply eqb_refl.
Qed.

Lemma in_l_eval_some: forall (m: PA) (l: Lit) (a: Ann), 
  In (l, a) m -> exists (b: bool), l_eval m l = Some b.
Proof.
  intros. funelim (l_eval m l).
  - contradiction.
  - now exists true.
  - now exists false.
  - apply (H a0). inversion H0.
    + injection H1 as <- <-. rewrite eqb_refl in Heq0. discriminate.
    + assumption. 
Qed.

Lemma l_eval_some_neg: forall (m: PA) (l: Lit) (b: bool),
  l_eval m l = Some b <-> l_eval m (¬l) = Some (negb b).
Proof.
  intros. funelim (l_eval m l).
  - split.
    + intros. discriminate.
    + intros. discriminate.
  - split.
    + intros. injection H as <-. rewrite eqb_eq in Heq. subst l'.
      simp l_eval. rewrite eqb_refl. rewrite eqb_sym. rewrite Neg.self_neqb_neg. simpl. reflexivity.
    + intros. rewrite eqb_eq in Heq. subst l'. simp l_eval in H.
      rewrite eqb_refl in H. rewrite eqb_sym in H. rewrite Neg.self_neqb_neg in H. simpl in H.
      injection H as H. destruct b; easy.
  - split.
    + intros. rewrite eqb_eq in Heq. subst. rewrite Neg.involutive.
      simp l_eval. rewrite eqb_refl. rewrite Neg.self_neqb_neg. simpl. f_equal.
      injection H as <-. reflexivity.
    + intros. f_equal. rewrite eqb_eq in Heq. subst. rewrite Neg.involutive in H.
      simp l_eval in H. rewrite Neg.self_neqb_neg in H. rewrite eqb_refl in H. simpl in H.
      injection H as H. destruct b; auto.
  - split.
    + intros. simp l_eval. rewrite <- Neg.eqb_compat. rewrite Heq0. 
      rewrite Neg.eqb_compat. rewrite Neg.involutive. rewrite Heq. simpl.
      apply H. assumption.
    + intros. simp l_eval in H0. rewrite <- Neg.eqb_compat in H0. rewrite Heq0 in H0.
      rewrite Neg.eqb_compat in H0. rewrite Neg.involutive in H0. rewrite Heq in H0.
      simpl in H0. apply H. assumption.
Qed.
*)
