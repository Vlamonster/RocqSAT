From Equations Require Import Equations.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
From Stdlib Require Import List Relations Lia.
Import ListNotations.

Open Scope bool_scope.

(* Atoms are propositional symbols mapped to the naturals. *)
Definition Atom: Type := nat.

Definition eqb_atom := Nat.eqb.

(* Literals are either positive or negated variants of atoms. *)
Inductive Lit: Type :=
| Pos (p: Atom)
| Neg (p: Atom).

Lemma eqb_atom_refl: forall (p: Atom), eqb_atom p p = true.
Proof. apply Nat.eqb_refl. Qed.

Lemma eqb_atom_sym: forall (p1 p2: Atom), eqb_atom p1 p2 = eqb_atom p2 p1.
Proof. apply Nat.eqb_sym. Qed.

Lemma eqb_atom_eq: forall (p1 p2: Atom), eqb_atom p1 p2 = true <-> p1 = p2.
Proof. apply Nat.eqb_eq. Qed.

Equations eqb_lit (l1 l2: Lit): bool :=
eqb_lit (Pos p1) (Pos p2) := eqb_atom p1 p2;
eqb_lit (Neg p1) (Neg p2) := eqb_atom p1 p2;
eqb_lit _ _ => false.

Notation "l1 =? l2" := (eqb_lit l1 l2) (at level 70).

Lemma eqb_lit_refl: forall (l: Lit), l =? l = true.
Proof. destruct l; simp eqb_lit; apply eqb_atom_refl. Qed.

Lemma eqb_lit_sym: forall (l1 l2: Lit), (l1 =? l2) = (l2 =? l1).
Proof. destruct l1, l2; simp eqb_lit; try reflexivity; try now apply eqb_atom_sym. Qed.

Lemma eqb_lit_eq: forall (l1 l2: Lit), l1 =? l2 = true <-> l1 = l2.
Proof. destruct l1, l2; split; try simp eqb_lit; try rewrite eqb_atom_eq; try congruence. Qed.

Lemma eqb_lit_neq: forall (l1 l2: Lit), l1 =? l2 = false <-> l1 <> l2.
Proof.
  split.
  - intros Hneqb Heq. subst. rewrite eqb_lit_refl in Hneqb. discriminate.
  - intros Hneq. destruct (l1 =? l2) eqn:Heqb.
    + apply eqb_lit_eq in Heqb. congruence.
    + reflexivity.
Qed.

(* A clause is a disjunction of literals. *)
Definition Clause: Type := list Lit.

(* A formula is a conjunction of clauses. *)
Definition CNF: Type := list Clause.

Equations neg (l: Lit): Lit :=
neg (Pos p) := Neg p;
neg (Neg p) := Pos p.

Lemma neg_neq: forall (l: Lit), l <> neg l.
Proof. intros. apply eqb_lit_neq. now funelim (l =? neg l). Qed.

Lemma neg_neqb: forall (l: Lit), l =? neg l = false.
Proof. intros. now funelim (l =? neg l). Qed.

Lemma neg_involutive: forall (l: Lit), neg (neg l) = l.
Proof. intros. now funelim (neg l). Qed.

Lemma eqb_lit_neg_compat: forall (l1 l2: Lit), (l1 =? l2) = (neg l1 =? neg l2).
Proof. now destruct l1, l2. Qed.

Lemma eq_lit_neg_compat: forall (l1 l2: Lit), l1 = l2 <-> neg l1 = neg l2.
Proof. intros. repeat rewrite <- eqb_lit_eq. now rewrite eqb_lit_neg_compat. Qed.

Definition Unit (C: Clause): Prop := exists (l: Lit), C = [l].

(* A partial assignment for annoted literals. See `l_eval` for evaluation. *)
Definition PA (A: Type): Type := list (Lit * A).

(* The first instance of `l` or `neg l` determines the value. *)
Equations l_eval {A: Type} (m: PA A) (l: Lit): option bool :=
l_eval [] _ := None;
l_eval ((l', _) :: m) l with l =? l', l =? neg l' :=
  | true, _    := Some true
  | _   , true := Some false
  | _   , _    := l_eval m l.

Equations l_ann {A: Type} (m: PA A) (l: Lit): option A :=
l_ann [] _ := None;
l_ann ((l', a) :: m) l with l =? l', l =? neg l' :=
  | true, _    := Some a
  | _   , true := Some a
  | _   , _    := l_ann m l.

Equations l_remove (c: Clause) (l: Lit): Clause :=
l_remove c l := filter (fun l' => negb (l =? l')) c.

Equations c_eval {A: Type} (m: PA A) (c: Clause): option bool :=
c_eval m [] := Some false;
c_eval m (l :: c) with l_eval m l, c_eval m c :=
  | Some true , _          := Some true
  | _         , Some true  := Some true
  | Some false, Some false := Some false
  | _         , _          := None.

Equations f_eval {A: Type} (m: PA A) (f: CNF): option bool :=
f_eval m [] := Some true;
f_eval m (c :: f) with c_eval m c, f_eval m f :=
  | Some true , r          := r
  | Some false, _          := Some false
  | _         , Some false := Some false
  | None      , _          := None.

Module EvalExamples.
Compute l_eval [(Pos 1, tt)] (Pos 1).
Compute l_eval [(Pos 1, tt)] (Neg 1).
Compute c_eval [] [Pos 1; Pos 2].
Compute c_eval [(Pos 1, tt)] [Pos 1; Pos 2].
Compute c_eval [(Neg 1, tt)] [Pos 1; Pos 2].
Compute c_eval [(Pos 2, tt)] [Pos 1; Pos 2].
End EvalExamples.

Definition Def {A: Type} (m: PA A) (l: Lit): Prop := exists (v: bool), l_eval m l = Some v.
Definition Undef {A: Type} (m: PA A) (l: Lit): Prop := l_eval m l = None.

Lemma def_undef: forall {A: Type} (m: PA A) (l: Lit), Def m l <-> ~ Undef m l.
Proof. 
  unfold Def, Undef. intros. destruct (l_eval m l).
  - intuition.
    + discriminate.
    + exists b. reflexivity.
  - intuition. destruct H. discriminate.
Qed.

Definition Total {A: Type} (m: PA A): Prop := forall (l: Lit), Def m l.

Definition Model {A: Type} (m: PA A) (f: CNF): Prop := f_eval m f = Some true.

Definition Sat (f: CNF): Prop := exists (A: Type) (m: PA A), Model m f.
Definition Unsat (f: CNF): Prop := ~ Sat f.

Definition Entails (A: Type) (f f': CNF): Prop := forall (m: PA A), Model m f -> Model m f'.
Definition Equivalent (A: Type) (f f': CNF): Prop := Entails A f f' /\ Entails A f' f.

(* Annotates whether the literal was decided or propagated. *)
Definition Ann: Type := bool.

Notation "m ++a n" := (n ++ m) (at level 65, left associativity).
Notation "m ++d l" := ((l, true) :: m) (at level 65, left associativity).
Notation "m ++p l" := ((l, false) :: m) (at level 65, left associativity).

Inductive State: Type :=
| fail
| state (m: PA Ann) (f: CNF).

Definition NoDecisions (m: PA Ann): Prop := ~ exists (l: Lit), l_ann m l = Some true.

Definition Conflicting (m: PA Ann) (c: Clause): Prop := c_eval m c = Some false.

Inductive Trans: relation State :=
(* Fail if all literals are assigned and there is a conflict. *)
| t_fail (m: PA Ann) (f: CNF) (c: Clause):
  In c f ->
  Conflicting m c ->
  NoDecisions m ->
  Trans (state m f) fail
(* If a clause is false except for one unassigned literal, assign it to satisfy the clause. *)
| t_unit (m: PA Ann) (f: CNF) (c: Clause) (l: Lit):
  In l c ->
  In c f ->
  Conflicting m (l_remove c l) ->
  Undef m l ->
  Trans (state m f) (state (m ++p l) f)
(* Arbitrarily set an unassigned literal in the formula to true. *)
| t_decide (m: PA Ann) (f: CNF) (c: Clause) (l: Lit):
  In l c \/ In (neg l) c ->
  In c f ->
  Undef m l ->
  Trans (state m f) (state (m ++d l) f)
(* Backtrack by flipping the most recent decision literal. *)
| t_backtrack (m n: PA Ann) (f: CNF) (c: Clause) (l: Lit):
  In c f ->
  Conflicting (m ++d l ++a n) c ->
  NoDecisions n ->
  Trans (state (m ++d l ++a n) f) (state (m ++p neg l) f).

Infix "==>" := Trans (at level 70).

Definition TransRTC: relation State := clos_refl_trans State Trans.
Infix "==>*" := TransRTC (at level 70).

Definition Final (s: State): Prop := ~ exists (s': State), s ==> s'.

Module TransExamples.

Example dead_end:
    state [(Pos 1, false)] [[Pos 1];[Neg 1]] ==>
    fail.
Proof.
  apply (t_fail _ _ [Neg 1]).
  - right. left. reflexivity.
  - unfold Conflicting. autorewrite with c_eval. reflexivity.
  - unfold NoDecisions. unfold not. intros. destruct H. autorewrite with neg l_ann in H.
    destruct (x =? Pos 1), (x =? Neg 1); simpl in H; discriminate.
Qed.

Example unit_prop: 
  (state [] [[Pos 1];[Neg 1]]) ==>
  (state [(Pos 1, false)] [[Pos 1];[Neg 1]]).
Proof.
  apply (t_unit _ _ [Pos 1] _).
  - left. reflexivity.
  - left. reflexivity.
  - unfold Conflicting. autorewrite with c_eval. reflexivity.
  - unfold Undef. autorewrite with l_eval. reflexivity.
Qed.

Example decide:
  (state [] [[Pos 1];[Neg 1]]) ==>
  (state [(Pos 1, true)] [[Pos 1];[Neg 1]]).
Proof.
  apply (t_decide _ _ [Pos 1] _).
  - left. left. reflexivity.
  - left. reflexivity.
  - unfold Undef. autorewrite with l_eval. reflexivity.
Qed.

Example unit_prop__dead_end:
  (state [] [[Pos 1];[Neg 1]]) ==>*
  fail.
Proof.
  apply (rt_trans _ _ _ (state [(Pos 1, false)] [[Pos 1];[Neg 1]]) _).
  - apply rt_step. apply unit_prop.
  - apply rt_step. apply dead_end.
Qed.

Example backtrack:
  (state [(Pos 1, true)] [[Pos 1];[Neg 1]]) ==>
  (state [(Neg 1, false)] [[Pos 1];[Neg 1]]).
Proof.
  apply (t_backtrack [] [] _ [Neg 1] (Pos 1)).
  - right. left. reflexivity.
  - unfold Conflicting. simp c_eval. reflexivity.
  - unfold NoDecisions. unfold not. intros. destruct H. simp l_ann in H. discriminate.
Qed.

End TransExamples.

Equations split_last_decision (m: PA Ann): option (PA Ann * Lit) :=
split_last_decision [] := None;
split_last_decision (m ++d l) := Some (m, l);
split_last_decision (m ++p l) := split_last_decision m.

Equations option_bind {A B: Type} (f: A -> option B) (o: option A): option B :=
option_bind _ None     := None;
option_bind f (Some a) := f a.

Equations is_conflict (m: PA Ann) (c: Clause): bool :=
is_conflict m c with c_eval m c :=
  | Some false := true
  | _          := false.

Equations is_undefined_c (m: PA Ann) (c: Clause): bool :=
is_undefined_c m c with c_eval m c := 
  | None := true
  | _    := false.

Equations is_undefined_l (m: PA Ann) (l: Lit): bool :=
is_undefined_l m l with l_eval m l := 
  | None := true
  | _    := false.

Equations find_conflict (m: PA Ann) (f: CNF): option Clause :=
find_conflict m f := find (is_conflict m) f.

Equations find_unit_l (m: PA Ann) (c: Clause): option Lit :=
find_unit_l m c := find (fun (l: Lit) => is_conflict m (l_remove c l)) c.

Equations find_unit (m: PA Ann) (f: CNF): option (Clause * Lit) :=
find_unit m [] := None;
find_unit m (c :: f) with c_eval m c, find_unit_l m c :=
  | None, Some l := Some (c, l)
  | _   , _      := find_unit m f.

Equations find_undef_l (m: PA Ann) (c: Clause): option Lit :=
find_undef_l m c := find (is_undefined_l m) c.

Equations find_decision (m: PA Ann) (f: CNF): option Lit :=
find_decision m [] := None;
find_decision m (c :: f) with find_undef_l m c, find_decision m f :=
  | Some l, _ := Some l
  | _     , r := r.

Equations next_state (s: State): option State :=
next_state fail := None;
next_state (state m f) :=
  let split := split_last_decision m in
  match find_conflict m f, split with
  (* t_fail *)
  | Some c, None => Some fail
  (* t_backtrack *)
  | Some c, Some (m', l) => Some (state (m' ++p neg l) f)
  | _     , _    =>
  (* t_unit *)
  match find_unit m f with
  | Some (c, l) => Some (state (m ++p l) f)
  | None        =>
  (* t_decide *)
  match find_decision m f with
  | Some l => Some (state (m ++d l) f)
  | None   => None
  end end end.

Compute (next_state (state [] [[Pos 1];[Neg 1]])).
Compute (option_bind next_state (next_state (state [] [[Pos 1];[Neg 1]]))).

Compute (next_state (state ([] ++d Pos 1) [[Pos 1];[Neg 1]])).
Compute (option_bind next_state (next_state (state ([] ++d Pos 1) [[Pos 1];[Neg 1]]))).

Lemma split_decomp: forall (m m': PA Ann) (l': Lit),
  split_last_decision m = Some (m', l') -> exists (n': PA Ann), m = m' ++d l' ++a n' /\ NoDecisions n'.
Proof.
  unfold NoDecisions. unfold not. intros. funelim (split_last_decision m).
  - discriminate.
  - rewrite <- Heqcall in H. injection H as H. subst. exists []. split.
    + reflexivity.
    + intros. destruct H. discriminate.
  - rewrite <- Heqcall in H0. destruct (H m' l' H0). destruct H1. rewrite H1. exists (x ++p l). split.
    + reflexivity.
    + intros. apply H2. destruct H3. exists x0. simp l_ann in H3. destruct (x0 =? neg l), (x0 =? l).
      * simpl in H3. discriminate.
      * simpl in H3. discriminate.
      * simpl in H3. discriminate.
      * simpl in H3. assumption.
Qed. 

Lemma find_conflict_c_in_f: forall (m: PA Ann) (f: CNF) (c: Clause), find_conflict m f = Some c -> In c f.
Proof. intros. simp find_conflict in H. apply find_some in H as [H _]. assumption. Qed.

Lemma find_conflict_conflicting: forall (m: PA Ann) (f: CNF) (c: Clause), find_conflict m f = Some c -> Conflicting m c.
Proof. 
  unfold Conflicting. intros. simp find_conflict in H. apply find_some in H as [_ H]. funelim (is_conflict m c).
  - congruence.
  - assumption.
  - congruence.
Qed.

Lemma l_ann_prop_eq: forall (m: PA Ann) (l: Lit), l_ann (m ++p l) l = Some false. 
Proof. intros. simp l_ann. rewrite eqb_lit_refl. simpl. reflexivity. Qed.

Lemma l_ann_prop_eq_neg: forall (m: PA Ann) (l: Lit), l_ann (m ++p l) (neg l) = Some false. 
Proof. 
  intros. simp l_ann. rewrite eqb_lit_refl. pose proof (neg_neq l). apply eqb_lit_neq in H.
  rewrite eqb_lit_sym in H. rewrite H. simpl. reflexivity.
Qed.

Lemma l_ann_prop_neq: forall (m: PA Ann) (l l': Lit), l' <> l /\ l' <> neg l -> l_ann (m ++p l) l' = l_ann m l'. 
Proof. 
  intros. destruct H. simp l_ann. rewrite <- eqb_lit_neq in H, H0. rewrite H, H0. simpl. reflexivity.
Qed.

Lemma no_split__no_decision: forall (m: PA Ann), split_last_decision m = None -> NoDecisions m.
Proof. 
  unfold NoDecisions. unfold not. intros. funelim (split_last_decision m).
  - destruct H0. discriminate.
  - discriminate.
  - destruct H1. apply (H m).
    + assumption.
    + destruct (x =? l) eqn:G1, (x =? neg l) eqn:G2.
      * apply eqb_lit_eq in G1. subst. rewrite l_ann_prop_eq in H1. discriminate.
      * apply eqb_lit_eq in G1. subst. rewrite l_ann_prop_eq in H1. discriminate.
      * apply eqb_lit_eq in G2. subst. rewrite l_ann_prop_eq_neg in H1. discriminate.
      * exists x. rewrite eqb_lit_neq in G1, G2. rewrite <- (l_ann_prop_neq m _ _ (conj G1 G2)). assumption.
    + reflexivity.
    + reflexivity.
Qed.

Lemma no_decision__no_split: forall (m: PA Ann), NoDecisions m -> split_last_decision m = None.
Proof. 
  unfold NoDecisions. unfold not. intros. funelim (split_last_decision m).
  - reflexivity.
  - exfalso. apply H. exists l. simp l_ann. rewrite eqb_lit_refl. reflexivity.
  - apply H. intros. destruct H1. destruct (x =? l) eqn:G1, (x =? neg l) eqn:G2.
    + admit.
    + admit.
    + admit.
    + apply H0. exists x. simp l_ann. rewrite G1, G2. simpl. assumption.
Admitted.

Lemma find_undef_l_in_c: forall (m: PA Ann) (c: Clause) (l: Lit), find_undef_l m c = Some l -> In l c.
Proof.
  intros. funelim (find_undef_l m c). rewrite H in Heqcall. 
  apply find_some in Heqcall. destruct Heqcall. assumption.
Qed.

Lemma find_undef_l_undef: forall (m: PA Ann) (c: Clause) (l: Lit), find_undef_l m c = Some l -> Undef m l.
Proof. 
  unfold Undef. intros. funelim (find_undef_l m c). rewrite H in Heqcall. 
  apply find_some in Heqcall. destruct Heqcall. funelim (is_undefined_l m l).
  - congruence.
  - assumption.
Qed.

Lemma find_decision_decomp: forall (m: PA Ann) (f: CNF) (l: Lit), 
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

Lemma find_unit_l_l_in_c: forall (m: PA Ann) (c: Clause) (l: Lit),
  find_unit_l m c = Some l -> In l c.
Proof.
  intros. funelim (find_unit_l m c). rewrite H in Heqcall. 
  apply find_some in Heqcall. destruct Heqcall. assumption.
Qed.

Lemma find_unit_l_in_c: forall (m: PA Ann) (f: CNF) (c: Clause) (l: Lit),
  find_unit m f = Some (c, l) -> In l c.
Proof. 
  intros. funelim (find_unit m f).
  - congruence.
  - apply H. rewrite <- H0. assumption.
  - rewrite H in Heqcall. injection Heqcall as Heqcall. subst. 
    apply (find_unit_l_l_in_c m c0 l0). assumption.
  - apply H. congruence.
Qed.

Lemma find_unit_c_in_f: forall (m: PA Ann) (f: CNF) (c: Clause) (l: Lit),
  find_unit m f = Some (c, l) -> In c f.
Proof. 
  intros. funelim (find_unit m f).
  - congruence.
  - right. apply (H c0 l0). congruence.
  - rewrite H in Heqcall. injection Heqcall as Heqcall. subst. left. reflexivity.
  - right. apply (H c0 l). congruence.
Qed.

Lemma find_unit_conflicting: forall (m: PA Ann) (f: CNF) (c: Clause) (l: Lit),
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

Lemma c_eval_none__l_eval_none: forall (m: PA Ann) (c: Clause), 
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

Lemma c_eval_false__l_eval_false: forall (m: PA Ann) (c: Clause),
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

Lemma undef_remove_false__undef: forall (m: PA Ann) (c: Clause) (l: Lit),
  c_eval m c = None -> c_eval m (l_remove c l) = Some false -> Undef m l.
Proof.
  unfold Undef. intros. 
  pose proof (c_eval_none__l_eval_none m c H).
  pose proof (c_eval_false__l_eval_false m (l_remove c l) H0).
  destruct H1. destruct H1. destruct (x =? l) eqn:G.
  - apply eqb_lit_eq in G. subst. assumption.
  - pose proof (H2 x). assert (In x (l_remove c l)).
    + simp l_remove. rewrite filter_In. split.
      * assumption.
      * rewrite eqb_lit_sym. rewrite G. reflexivity.
    + apply H4 in H5. congruence. 
Qed.

Lemma find_unit_undef: forall (m: PA Ann) (f: CNF) (c: Clause) (l: Lit),
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

Lemma app_cancel: forall (m n: PA Ann), m ++a n = m -> n = [].
Proof.
  induction m.
  - intros. rewrite app_nil_r in H. assumption.
  - intros. apply IHm. apply (app_inv_tail (a::m) _ []) in H. rewrite H. simpl. reflexivity.
Qed.

Lemma next_state_sound: forall (s s': State), next_state s = Some s' -> s ==> s'.
Proof.
  intros. funelim (next_state s); rewrite H in Heqcall; clear H; symmetry in Heqcall.
  - discriminate.
  - destruct (find_conflict m f) as [c_conflict|] eqn:find_conflict.
    + destruct (split_last_decision m) as [(m_split, l_split)|] eqn:split_last_decision.
      (* t_backtrack *)
      * injection Heqcall as Heqcall. rewrite Heqcall. 
        pose proof (split_decomp _ _ _ split_last_decision) as decomp. 
        destruct decomp as [n_split [decomp no_dec]]. rewrite decomp.
        apply (t_backtrack m_split n_split f c_conflict l_split).
        -- apply (find_conflict_c_in_f m f c_conflict). assumption.
        -- rewrite <- decomp. apply (find_conflict_conflicting m f c_conflict). assumption.
        -- assumption.
      (* t_fail *)
      * injection Heqcall as Heqcall. rewrite Heqcall. apply (t_fail m f c_conflict).
        -- apply (find_conflict_c_in_f m f c_conflict). assumption.
        -- apply (find_conflict_conflicting m f c_conflict). assumption.
        -- apply (no_split__no_decision m). assumption.
    + destruct (find_unit m f) as [(c_unit, l_unit)|] eqn:find_unit.
      (* t_unit *)
      * injection Heqcall as Heqcall. rewrite Heqcall. apply (t_unit m f c_unit l_unit).
        -- apply (find_unit_l_in_c m f c_unit l_unit). assumption.
        -- apply (find_unit_c_in_f m f c_unit l_unit). assumption.
        -- apply (find_unit_conflicting m f c_unit l_unit). assumption.
        -- apply (find_unit_undef m f c_unit l_unit). assumption.
      * destruct (find_decision m f) as [l_decide|] eqn:find_decision.
        (* t_decide *)
        -- injection Heqcall as Heqcall. rewrite Heqcall.
           destruct (find_decision_decomp m f l_decide find_decision) as [c_decide [Hc Hc_in_f]].
           apply (t_decide m f c_decide l_decide).
          ++ left. apply (find_undef_l_in_c m c_decide l_decide). assumption.
          ++ assumption.
          ++ apply (find_undef_l_undef m c_decide l_decide). assumption.
        -- discriminate.
Qed.

Lemma find_conflict_exists: forall (m: PA Ann) (f: CNF) (c: Clause),
  In c f -> Conflicting m c -> exists (c': Clause), find_conflict m f = Some c'.
Proof.
  unfold Conflicting. intros m f c Hin Hc. destruct (find_conflict m f) as [c'|] eqn:Hfind.
  - now exists c'.
  - simp find_conflict in Hfind. pose proof (find_none (is_conflict m) f Hfind c Hin) as contra.
    simp is_conflict in contra. rewrite Hc in contra. simpl in contra. discriminate.
Qed.

Lemma find_undef_l_exists : forall (m: PA Ann) (c: Clause) (l: Lit),
  In l c -> Undef m l -> exists (l': Lit), find_undef_l m c = Some l'.
Proof.
  unfold Undef. intros. destruct (find_undef_l m c) eqn:G.
  - now exists l0.
  - simp find_undef_l in G. apply (find_none (is_undefined_l m) c G l) in H.
    simp is_undefined_l in H. rewrite H0 in H. discriminate.
Qed.

Lemma find_decision_exists: forall (m: PA Ann) (f: CNF) (c: Clause) (l: Lit),
  In l c -> In c f -> Undef m l -> exists (l': Lit), find_decision m f = Some l'.
Proof. 
  intros. funelim (find_decision m f).
  - contradiction.
  - now exists l.
  - apply (Hind c0 l); auto. inversion H0; auto. subst.
    destruct (find_undef_l_exists m c0 l H H1). congruence.
Qed.

Lemma undef__neg_undef: forall (m: PA Ann) (l: Lit), Undef m l <-> Undef m (neg l).
Proof.
  unfold Undef. intros. funelim (l_eval m l).
  - intuition.
  - intuition.
    + discriminate.
    + apply eqb_lit_eq in Heq. subst. simp l_eval in H. rewrite eqb_lit_refl in H. 
      rewrite eqb_lit_sym in H. rewrite neg_neqb in H. discriminate.
  - intuition.
    + discriminate.
    + apply eqb_lit_eq in Heq. subst. simp neg in H. rewrite neg_involutive in H.
      simp l_eval in H. rewrite eqb_lit_refl in H. rewrite neg_neqb in H. discriminate.
  - intuition.
    + simp l_eval. rewrite <- eqb_lit_neg_compat. rewrite Heq0. rewrite eqb_lit_neg_compat in Heq.
      rewrite neg_involutive in Heq. rewrite Heq. simpl. assumption.
    + autorewrite with l_eval in H. rewrite <- eqb_lit_neg_compat in H. rewrite Heq0 in H.
      rewrite eqb_lit_neg_compat in Heq. rewrite neg_involutive in Heq. rewrite Heq in H. simpl in H. 
      apply H1. apply H.
Qed.

(* The rhs is weaker because there could be multiple { s': State | s ==> s' }. *)
Lemma next_state_exists: forall (s s': State), s ==> s' -> exists (s'': State), next_state s = Some s''.
Proof.
  intros. inversion H as 
    [
      m f c_conflict Hc_in_f Hconflict Hno_dec |
      m f c_unit l_unit Hl_in_c Hc_in_f Hconflict Hundef |
      m f c_decide l_decide Hx_in_c Hc_in_f Hundef |
      m_split n_split f c_conflict l_split Hc_in_f Hconflict Hno_dec
    ]; subst s s'.
  (* t_fail *)
  - funelim (next_state (state m f)).
    + discriminate.
    + injection eqargs as eqargs. symmetry in eqargs, H0. subst. 
      destruct (find_conflict m f) as [c_conflict'|] eqn:Hfind_conflict.
      * destruct (split_last_decision m) as [(m_split, l_split)|] eqn:Hsplit.
        -- now exists (state (m_split ++p neg l_split) f).
        -- now exists fail.
      * destruct (find_conflict_exists m f c_conflict Hc_in_f Hconflict). congruence.
  (* t_unit *)
  - funelim (next_state (state m f)).
    + discriminate.
    + injection eqargs as eqargs. symmetry in eqargs, H0. subst.
      destruct (find_conflict m f) as [c_conflict'|] eqn:Hfind_conflict.
      * destruct (split_last_decision m) as [(m_split, l_split)|] eqn:Hsplit.
        -- now exists (state (m_split ++p neg l_split) f).
        -- now exists fail.
      * destruct (find_unit m f) as [(c_unit', l_unit')|] eqn:Hfind_unit.
        -- now exists (state (m ++p l_unit') f).
        -- destruct (find_decision m f) as [l_decide|] eqn:Hfind_dec.
          ++ now exists (state (m ++d l_decide) f).
          ++ destruct (find_decision_exists m f c_unit l_unit Hl_in_c Hc_in_f Hundef). congruence.
  (* t_decide *)
  - funelim (next_state (state m f)).
    + discriminate.
    + injection eqargs as eqargs. symmetry in eqargs, H0. subst.
      destruct (find_conflict m f) as [c_conflict'|] eqn:Hfind_conflict.
      * destruct (split_last_decision m) as [(m_split, l_split)|] eqn:Hsplit.
        -- now exists (state (m_split ++p neg l_split) f).
        -- now exists fail.
      * destruct (find_unit m f) as [(c_unit', l_unit')|] eqn:Hfind_unit.
        -- now exists (state (m ++p l_unit') f).
        -- destruct (find_decision m f) as [l_decide'|] eqn:Hfind_dec.
          ++ now exists (state (m ++d l_decide') f).
          ++ destruct Hx_in_c as [Hl_in_c|Hnegl_in_c].
            ** destruct (find_decision_exists m f c_decide l_decide Hl_in_c Hc_in_f Hundef). congruence.
            ** apply undef__neg_undef in Hundef.
               destruct (find_decision_exists m f c_decide (neg l_decide) Hnegl_in_c Hc_in_f Hundef). congruence.
  (* t_backtrack *)
  - funelim (next_state (state (m_split ++d l_split ++a n_split) f)).
    + discriminate.
    + injection eqargs as eqargs. symmetry in eqargs, H0. subst.
      destruct (find_conflict (m_split ++d l_split ++a n_split) f) as [c_conflict'|] eqn:Hfind_conflict.
      * destruct (split_last_decision (m_split ++d l_split ++a n_split)) as [(m_split', l_split')|] eqn:Hsplit.
        -- now exists (state (m_split' ++p neg l_split') f).
        -- now exists fail.
      * destruct (find_unit (m_split ++d l_split ++a n_split) f) as [(c_unit', l_unit')|] eqn:Hfind_unit.
        -- now exists (state (m_split ++d l_split ++a n_split ++p l_unit') f).
        -- destruct (find_decision (m_split ++d l_split ++a n_split) f) as [l_decide'|] eqn:Hfind_dec.
          ++ now exists (state (m_split ++d l_split ++a n_split ++d l_decide') f).
          ++ destruct (find_conflict_exists (m_split ++d l_split ++a n_split) f c_conflict Hc_in_f Hconflict). congruence.
Qed.

Lemma next_state_final_refl: forall (s: State), next_state s = None <-> Final s.
Proof.
  unfold Final. unfold not. intros. split.
  - intros. destruct H0. apply next_state_exists in H0. destruct H0. congruence.
  - intros. destruct (next_state s) eqn:G.
    + apply next_state_sound in G. exfalso. apply H. exists s0. assumption.
    + reflexivity.
Qed.

(* Temporarily has `n` for testing, until termination in proven. *)
Equations solve_n (n: nat) (s: State): State :=
solve_n 0     _ := s;
solve_n (S n) s with next_state s :=
  | Some s' := solve_n n s'
  | None := s.

Equations max_lit_c (c: Clause): nat :=
max_lit_c []           := 0;
max_lit_c (Pos p :: c) := max p (max_lit_c c);
max_lit_c (Neg p :: c) := max p (max_lit_c c).

Equations max_lit_f (f: CNF): nat :=
max_lit_f []       := 0;
max_lit_f (c :: f) := max (max_lit_c c) (max_lit_f f).

Equations score_aux (m: PA Ann) (n x: nat): list nat :=
score_aux []        n x := [n - x];
score_aux (m ++p l) n x := score_aux m n (S x);
score_aux (m ++d l) n x := n - x :: score_aux m n 0.

Equations score (m: PA Ann) (f: CNF): list nat :=
score m f := rev (score_aux m (max_lit_f f) 0).

Equations score_total (m: PA Ann) (f: CNF): nat :=
score_total m f := (max_lit_f f) - length m.

Inductive PrefixLt: relation (list nat) :=
| p_head (m m': list nat) (n n': nat):
  n < n' ->
  PrefixLt (n :: m) (n' :: m')
| p_tail (m m': list nat) (n n': nat):
  n = n' ->
  PrefixLt m m' ->
  PrefixLt (n :: m) (n' :: m').

Inductive TotalLt: relation (list nat * nat) :=
| t_total (l l': nat):
  l < l' ->
  TotalLt ([], l) ([], l')
| t_tail (m m': list nat) (n n' l l': nat):
  n = n' ->
  TotalLt (m, l) (m', l') ->
  TotalLt (n :: m, l) (n' :: m', l').

Inductive StateLt': relation State :=
| s_fail (m: PA Ann) (f: CNF): 
  StateLt' fail (state m f)
| s_prefix (m m': PA Ann) (f: CNF):
  PrefixLt (score m f) (score m' f) ->
  StateLt' (state m f) (state m' f)
| s_total (m m': PA Ann) (f: CNF):
  TotalLt (score m f, score_total m f) (score m' f, score_total m' f) ->
  StateLt' (state m f) (state m' f).

Equations l_in_c (l: Lit) (f: Clause): bool :=
l_in_c l c := existsb (eqb_lit l) c || existsb (eqb_lit (neg l)) c.

Equations l_in_f (l: Lit) (f: CNF): bool :=
l_in_f l f := existsb (l_in_c l) f.

Equations neqb_of (eq: Lit * Ann -> Lit * Ann -> bool) (l l': Lit * Ann): bool :=
neqb_of eq a b := negb (eq a b).

Equations dedupe_by (eq: Lit * Ann -> Lit * Ann -> bool) (m: list (Lit * Ann)): 
  list (Lit * Ann) by wf (length m) lt :=
dedupe_by eq []       := [];
dedupe_by eq (l :: m) := l :: dedupe_by eq (filter (neqb_of eq l) m).
Next Obligation.
  eapply Nat.le_lt_trans.
  - apply filter_length_le.
  - auto with arith.
Qed.

Equations eqb_by_atom (la la': Lit * Ann): bool :=
eqb_by_atom (l, _) (l', _) := (l =? l') || (l =? neg l'). 

Equations is_bounded (f: CNF) (la: Lit * Ann): bool :=
is_bounded f (l, _) := l_in_f l f.

Equations clean (s: State): State :=
clean fail        := fail;
clean (state m f) := 
  let bounded := filter (is_bounded f) m in
  let deduped := dedupe_by eqb_by_atom bounded in
  state deduped f.

Inductive StateLt: relation State :=
| s_clean (s s': State):
  StateLt' (clean s) (clean s') ->
  StateLt s s'.

Infix ">>*" := (fun (s s': State) => StateLt' s' s) (at level 70).
Infix ">>" := (fun (s s': State) => StateLt s' s) (at level 70).

Equations prefix_lt (m m': list nat): bool :=
prefix_lt []       _          := false;
prefix_lt _        []         := false;
prefix_lt (n :: m) (n' :: m') := (n <? n') || (n =? n')%nat && (prefix_lt m m').

Lemma prefix_lt_refl: forall (m m': list nat), prefix_lt m m' = true <-> PrefixLt m m'.
Proof.
  intros. funelim (prefix_lt m m').
  - split.
    + intros. discriminate.
    + intros. inversion H.
  - split.
    + intros. discriminate.
    + intros. inversion H.
  - split.
    + intros. destruct (n <? n') eqn:G.
      * apply p_head. apply Nat.ltb_lt. assumption.
      * simpl in H0. rewrite Bool.andb_true_iff in H0. destruct H0.
        rewrite Nat.eqb_eq in H0. subst n'. apply p_tail.
        -- reflexivity.
        -- now apply H.
    + intros. inversion H0; subst.
      * apply Nat.ltb_lt in H2. now rewrite H2.
      * apply H in H6. rewrite H6. rewrite Nat.eqb_refl. apply orb_true_r.
Qed.

Equations total_lt (m m': list nat) (l l': nat): bool :=
total_lt []       []         l l' := l <? l';
total_lt []       _          _ _  := false;
total_lt _        []         _ _  := false;
total_lt (n :: m) (n' :: m') l l' := (n =? n')%nat && (total_lt m m' l l').

Lemma total_lt_refl: forall (m m': list nat) (l l': nat), 
  total_lt m m' l l' = true <-> TotalLt (m, l) (m', l').
Proof.
  intros. funelim (total_lt m m' l l').
  - split.
    + intros. apply t_total. now apply Nat.ltb_lt.
    + intros. inversion H. subst. now apply Nat.ltb_lt.
  - split.
    + intros. discriminate.
    + intros. inversion H.
  - split.
    + intros. discriminate.
    + intros. inversion H.
  - split.
    + intros. apply Bool.andb_true_iff in H0. destruct H0. rewrite Nat.eqb_eq in H0.
      subst n'. apply t_tail.
      * reflexivity.
      * now apply H.
    + intros. inversion H0; subst. apply H in H8. rewrite H8. now rewrite Nat.eqb_refl.
Qed.

Equations state_lt' (s s': State): bool :=
state_lt' fail        _             := true;
state_lt' _           fail          := false;
state_lt' (state m f) (state m' f') :=
  prefix_lt (score m f) (score m' f') ||
  total_lt (score m f) (score m' f') (score_total m f) (score_total m' f').

Lemma state_lt'_refl: forall (m m': PA Ann) (f: CNF), 
  state_lt' (state m f) (state m' f) = true <-> state m' f >>* state m f.
Proof.
  intros. split.
  - intros. funelim (state_lt' (state m f) (state m' f)).
    + discriminate.
    + discriminate.
    + injection H0 as H0. subst m0 f0. injection H1 as H1. subst m'0 f'.
      rewrite H in Heqcall. apply orb_true_iff in Heqcall. destruct Heqcall.
      * apply s_prefix. now apply prefix_lt_refl.
      * apply s_total. now apply total_lt_refl.
  - intros. inversion H; subst.
    + apply prefix_lt_refl in H1. simp state_lt'. rewrite H1. reflexivity.
    + apply total_lt_refl in H1. simp state_lt'. rewrite H1. apply orb_true_r.
Qed.

Equations state_lt (s s': State): bool :=
state_lt s s' := state_lt' (clean s) (clean s').

Lemma clean_same_formula: forall (m m': PA Ann) (f f': CNF),
  clean (state m f) = state m' f' -> f = f'.
Proof. intros. simp clean in H. simpl in H. injection H as _ <-. reflexivity. Qed.

Lemma state_lt_refl: forall (m m': PA Ann) (f: CNF),
  state_lt (state m f) (state m' f) = true <-> state m' f >> state m f.
Proof.
  intros. split.
  - intros. funelim (state_lt (state m f) (state m' f)). rewrite H in Heqcall.
    constructor. simp clean in *. simpl in *. now apply state_lt'_refl.
  - intros. inversion H; subst. simp state_lt. simp clean in *. simpl in *. now apply state_lt'_refl.
Qed.

Lemma next_state_options: forall (m: PA Ann) (f: CNF),
  next_state (state m f) = None \/
  next_state (state m f) = Some fail \/ 
  exists m': PA Ann, next_state (state m f) = Some (state m' f).
Proof.
  intros. funelim (next_state (state m f)).
  - left. reflexivity.
  - injection eqargs as eqargs. subst m0 f0. rewrite Heqcall. destruct (find_conflict m f).
    + destruct (split_last_decision m).
      * destruct p. right. right. now exists (p ++p neg l).
      * right. now left.
    + destruct (find_unit m f).
      * destruct p. right. right. now exists (m ++p l).
      * destruct (find_decision m f).
        -- right. right. now exists (m ++d l).
        -- now left.
Qed.

Module TransLtExamples.

Example prefix_lt_head: PrefixLt [1] [2].
Proof. apply p_head. auto. Qed.

Example prefix_lt_head_refl: PrefixLt [1] [2].
Proof. now apply prefix_lt_refl. Qed.

Example prefix_lt_tail: PrefixLt [1;1] [1;2].
Proof. apply p_tail. auto. apply p_head. auto. Qed.

Example prefix_lt_tail_refl: PrefixLt [1;1] [1;2].
Proof. now apply prefix_lt_refl. Qed.

Example total_lt_total: TotalLt ([], 1) ([], 2).
Proof. apply t_total. auto. Qed.

Example total_lt_total_prefix: TotalLt ([], 1) ([], 2).
Proof. now apply total_lt_refl. Qed.

Example total_lt_tail: TotalLt ([1], 1) ([1], 2).
Proof. apply t_tail. auto. apply t_total. auto. Qed.

Example total_lt_tail_refl: TotalLt ([1], 1) ([1], 2).
Proof. now apply total_lt_refl. Qed.

Example clean_dedupes: 
  clean (state ([] ++p Pos 2 ++p Pos 1 ++p Neg 1 ++d Pos 2) [[Pos 1];[Pos 2]]) = 
  state ([] ++p Neg 1 ++d Pos 2) [[Pos 1];[Pos 2]].
Proof. reflexivity. Qed.

Example clean_bounds: 
  clean (state ([] ++p Pos 3 ++p Pos 5 ++p Neg 1 ++d Pos 2) [[Pos 1];[Pos 2]]) = 
  state ([] ++p Neg 1 ++d Pos 2) [[Pos 1];[Pos 2]].
Proof. reflexivity. Qed.

End TransLtExamples.

Lemma l_in_c__c_in_f__l_in_f: forall (f: CNF) (c: Clause) (l: Lit),
  In l c -> In c f -> l_in_f l f = true.
Proof. 
  intros. simp l_in_f. rewrite existsb_exists. exists c. split.
  - assumption.
  - simp l_in_c. rewrite orb_true_iff. left. rewrite existsb_exists. exists l. split.
    + assumption.
    + apply eqb_lit_refl.
Qed.

Lemma undef__no_dupes: forall (m: PA Ann) (l: Lit) (b: bool), 
  Undef m l -> forallb (neqb_of eqb_by_atom (l, b)) m = true.
Proof.
  unfold Undef. induction m.
  - intros. simpl. reflexivity.
  - intros. simpl. simp neqb_of. apply andb_true_iff. split.
    + destruct a. simp eqb_by_atom. destruct (l =? l0) eqn:G1, (l =? neg l0) eqn:G2.
      * simp l_eval in H. rewrite G1, G2 in H. simpl in H. discriminate.
      * simp l_eval in H. rewrite G1, G2 in H. simpl in H. discriminate.
      * simp l_eval in H. rewrite G1, G2 in H. simpl in H. discriminate.
      * simpl. reflexivity.
    + apply IHm. destruct a. destruct (l =? l0) eqn:G1, (l =? neg l0) eqn:G2.
      * simp l_eval in H. rewrite G1, G2 in H. simpl in H. discriminate.
      * simp l_eval in H. rewrite G1, G2 in H. simpl in H. discriminate.
      * simp l_eval in H. rewrite G1, G2 in H. simpl in H. discriminate.
      * simp l_eval in H. rewrite G1, G2 in H. simpl in H. assumption.
Qed.

Lemma dedupe_prop: forall (m: PA Ann) (l: Lit), 
  Undef m l -> dedupe_by eqb_by_atom (m ++p l) = dedupe_by eqb_by_atom m ++p l.
Proof.
  intros. funelim (dedupe_by eqb_by_atom m).
  - reflexivity.
  - simp dedupe_by. apply (undef__no_dupes (l :: m) l0 false) in H0. 
    apply forallb_filter_id in H0. rewrite H0. now simp dedupe_by.
Qed.

Lemma dedupe_dec: forall (m: PA Ann) (l: Lit), 
  Undef m l -> dedupe_by eqb_by_atom (m ++d l) = dedupe_by eqb_by_atom m ++d l.
Proof.
  intros. funelim (dedupe_by eqb_by_atom m).
  - reflexivity.
  - simp dedupe_by. apply (undef__no_dupes (l :: m) l0 true) in H0. 
    apply forallb_filter_id in H0. rewrite H0. now simp dedupe_by.
Qed.

Lemma l_eval_some_in: forall (m: PA Ann) (l: Lit) (b: bool), 
  l_eval m l = Some b -> exists (b': bool), In (l, b') m \/ In (neg l, b') m.
Proof. 
  intros. funelim (l_eval m l).
  - congruence.
  - rewrite eqb_lit_eq in Heq. subst l'. exists a. left. now left.
  - rewrite eqb_lit_eq in Heq. subst. exists a. right. rewrite neg_involutive. now left.
  - rewrite H0 in Heqcall. apply H in Heqcall; auto. destruct Heqcall. destruct H1.
    + exists x. left. now right.
    + exists x. right. now right.
Qed.

Lemma in_l_eval_some: forall (m: PA Ann) (l: Lit) (b: bool), 
  In (l, b) m -> exists (b': bool), l_eval m l = Some b'.
Proof.
  intros. funelim (l_eval m l).
  - contradiction.
  - now exists true.
  - now exists false.
  - apply (H b). inversion H0.
    + injection H1 as <- <-. rewrite eqb_lit_refl in Heq0. discriminate.
    + assumption. 
Qed.

Lemma l_eval_some_neg: forall (m: PA Ann) (l: Lit) (b: bool),
  l_eval m l = Some b <-> l_eval m (neg l) = Some (negb b).
Proof.
  intros. funelim (l_eval m l).
  - split.
    + intros. discriminate.
    + intros. discriminate.
  - split.
    + intros. injection H as <-. rewrite eqb_lit_eq in Heq. subst l'.
      simp l_eval. rewrite eqb_lit_refl. rewrite eqb_lit_sym. rewrite neg_neqb. simpl. reflexivity.
    + intros. rewrite eqb_lit_eq in Heq. subst l'. simp l_eval in H.
      rewrite eqb_lit_refl in H. rewrite eqb_lit_sym in H. rewrite neg_neqb in H. simpl in H.
      injection H as H. destruct b; easy.
  - split.
    + intros. rewrite eqb_lit_eq in Heq. subst. rewrite neg_involutive.
      simp l_eval. rewrite eqb_lit_refl. rewrite neg_neqb. simpl. f_equal.
      injection H as <-. reflexivity.
    + intros. f_equal. rewrite eqb_lit_eq in Heq. subst. rewrite neg_involutive in H.
      simp l_eval in H. rewrite neg_neqb in H. rewrite eqb_lit_refl in H. simpl in H.
      injection H as H. destruct b; auto.
  - split.
    + intros. simp l_eval. rewrite <- eqb_lit_neg_compat. rewrite Heq0. 
      rewrite eqb_lit_neg_compat. rewrite neg_involutive. rewrite Heq. simpl.
      apply H. assumption.
    + intros. simp l_eval in H0. rewrite <- eqb_lit_neg_compat in H0. rewrite Heq0 in H0.
      rewrite eqb_lit_neg_compat in H0. rewrite neg_involutive in H0. rewrite Heq in H0.
      simpl in H0. apply H. assumption.
Qed.

Lemma undef__filter_undef: forall (m: PA Ann) (l: Lit) (test: Lit * Ann -> bool),
  Undef m l -> Undef (filter test m) l.
Proof.
  unfold Undef. intros. pose proof (incl_filter test m). unfold incl in H0.
  destruct (l_eval (filter test m) l) eqn:G.
  - apply l_eval_some_in in G. destruct G as [b' [G|G]].
    + apply H0 in G. apply in_l_eval_some in G. destruct G. congruence.
    + apply H0 in G. apply in_l_eval_some in G. destruct G. apply l_eval_some_neg in H1.
      rewrite neg_involutive in H1. congruence.
  - reflexivity.
Qed.

Lemma trans__state_lt: forall (s s': State), s ==> s' -> s >> s'.
  intros. inversion H as 
    [
      m f c_conflict Hc_in_f Hconflict Hno_dec |
      m f c_unit l_unit Hl_in_c Hc_in_f Hconflict Hundef |
      m f c_decide l_decide Hx_in_c Hc_in_f Hundef |
      m_split n_split f c_conflict l_split Hc_in_f Hconflict Hno_dec
    ]; subst s s'; constructor.
  - admit.
  - simp clean. simpl. simp is_bounded. apply s_prefix. apply prefix_lt_refl.
    rewrite (l_in_c__c_in_f__l_in_f f c_unit l_unit Hl_in_c Hc_in_f).
    pose proof (dedupe_prop (filter (is_bounded f) m) l_unit (undef__filter_undef m l_unit (is_bounded f) Hundef)).
    simp dedupe_by in *. rewrite H0. clear H0.
    admit.
  - admit.
  - admit.
Admitted.

Lemma next_state__state_lt: forall (s s': State), next_state s = Some s' -> s >> s'.
Proof. intros. apply trans__state_lt. apply next_state_sound. assumption. Qed.

Lemma wf_state_lt: well_founded StateLt.
Proof. unfold well_founded. Admitted.

Theorem fail_final: Final fail.
Proof. unfold Final. unfold not. intros. inversion H. inversion H0. Qed.

Theorem final_exists: forall (f: CNF),
  (state [] f ==>* fail /\ Final fail) \/
  (exists (m: PA Ann), state [] f ==>* state m f /\ Final (state m f)).
Admitted.

Theorem final_sat_refl: forall (f: CNF) (m: PA Ann),
  state [] f ==>* state m f /\ Final (state m f) <-> Sat f.
Admitted.

Theorem final_unsat_refl: forall (f: CNF),
  state [] f ==>* fail /\ Final fail <-> Unsat f.
Admitted.

Theorem sat_decidable: forall (f: CNF), Sat f \/ Unsat f.
Proof.
  intros. destruct (final_exists f).
  - right. apply final_unsat_refl. assumption.
  - left. destruct H. apply (final_sat_refl f x). assumption.
Qed.
