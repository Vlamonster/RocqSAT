From Equations Require Import Equations.
From Stdlib Require Import List Nat Relations.
Import ListNotations.

(* Atoms are propositional symbols mapped to the naturals. *)
Definition Atom: Type := nat.

Definition eqb_atom := eqb.

(* Literals are either positive or negated variants of atoms. *)
Inductive Lit: Type :=
| Pos (p: Atom)
| Neg (p: Atom).

Lemma eqb_atom_refl: forall (p: Atom), eqb_atom p p = true.
Proof. apply PeanoNat.Nat.eqb_refl. Qed.

Lemma eqb_atom_sym: forall (p1 p2: Atom), eqb_atom p1 p2 = eqb_atom p2 p1.
Proof. apply PeanoNat.Nat.eqb_sym. Qed.

Lemma eqb_atom_eq: forall (p1 p2: Atom), eqb_atom p1 p2 = true <-> p1 = p2.
Proof. apply PeanoNat.Nat.eqb_eq. Qed.

Equations eqb_lit (l1 l2: Lit): bool :=
eqb_lit (Pos p1) (Pos p2) := eqb_atom p1 p2;
eqb_lit (Neg p1) (Neg p2) := eqb_atom p1 p2;
eqb_lit _ _ => false.

Notation "l1 =? l2" := (eqb_lit l1 l2) (at level 70).

Lemma eqb_lit_refl: forall (l: Lit), l =? l = true.
Proof. intros. destruct l; simp eqb_lit; apply eqb_atom_refl. Qed.

Lemma eqb_lit_sym: forall (l1 l2: Lit), (l1 =? l2) = (l2 =? l1).
Proof. 
  intros. destruct l1, l2; simp eqb_lit.
  - apply eqb_atom_sym.
  - reflexivity.
  - reflexivity.
  - apply eqb_atom_sym.
Qed.

Lemma eqb_lit_eq: forall (l1 l2: Lit), l1 =? l2 = true <-> l1 = l2.
Proof.
  destruct l1, l2.
  - split.
    + intros. simp eqb_lit in H. apply eqb_atom_eq in H. subst. reflexivity.
    + intros. rewrite H. apply eqb_lit_refl.
  - split.
    + intros. simp eqb_lit in H. discriminate.
    + intros. discriminate.
  - split.
    + intros. simp eqb_lit in H. discriminate.
    + intros. discriminate.
  - split.
    + intros. simp eqb_lit in H. apply eqb_atom_eq in H. subst. reflexivity.
    + intros. injection H as H. subst. apply eqb_lit_refl.
Qed.

Lemma eqb_lit_neq: forall (l1 l2: Lit), l1 =? l2 = false <-> l1 <> l2.
Proof.
  intros l1 l2. split.
  - intros Hneq Heq. rewrite Heq in Hneq. rewrite eqb_lit_refl in Hneq. discriminate.
  - intros Hneq. destruct (l1 =? l2) eqn:Heq.
    + apply eqb_lit_eq in Heq. exfalso. apply Hneq. apply Heq.
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
Proof. 
  intros. apply eqb_lit_neq. funelim (eqb_lit l (neg l)).
  - rewrite Heqcall. simp neg eqb_lit. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite Heqcall. simp neg eqb_lit. reflexivity.
Qed.

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

Equations find_undef_c (m: PA Ann) (f: CNF): option Clause :=
find_undef_c m f := find (is_undefined_c m) f.

Equations find_undef_l (m: PA Ann) (c: Clause): option Lit :=
find_undef_l m c := find (is_undefined_l m) c.

Equations find_decision (m: PA Ann) (f: CNF): option Lit :=
find_decision m f := option_bind (find_undef_l m) (find_undef_c m f).

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
  split_last_decision m = Some (m', l') -> exists (n': PA Ann), m = m' ++d l' ++a n'.
Proof.
  intros. funelim (split_last_decision m).
  - discriminate.
  - rewrite <- Heqcall in H. injection H as H. subst. exists []. reflexivity.
  - rewrite <- Heqcall in H0. destruct (H m' l' H0). rewrite H1. exists (x ++p l). reflexivity.
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
    + exists x. destruct (x =? l) eqn:G1, (x =? neg l) eqn:G2.
      * apply eqb_lit_eq in G1. subst. rewrite l_ann_prop_eq in H1. discriminate.
      * apply eqb_lit_eq in G1. subst. rewrite l_ann_prop_eq in H1. discriminate.
      * apply eqb_lit_eq in G2. subst. rewrite l_ann_prop_eq_neg in H1. discriminate.
      * rewrite eqb_lit_neq in G1, G2. rewrite <- (l_ann_prop_neq m _ _ (conj G1 G2)). assumption.
    + reflexivity.
    + reflexivity.
Qed.

Lemma find_undef_l_in_c: forall (m: PA Ann) (c: Clause) (l: Lit), find_undef_l m c = Some l -> In l c.
Proof.
  intros. funelim (find_undef_l m c). rewrite H in Heqcall. 
  apply find_some in Heqcall. destruct Heqcall. assumption.
Qed.

Lemma find_undef_c_in_f: forall (m: PA Ann) (f: CNF) (c: Clause), find_undef_c m f = Some c -> In c f.
Proof. 
  intros. funelim (find_undef_c m f). rewrite H in Heqcall.
  apply find_some in Heqcall. destruct Heqcall. assumption.
Qed.

Lemma find_undef_l_undef: forall (m: PA Ann) (c: Clause) (l: Lit), find_undef_l m c = Some l -> Undef m l.
Proof. 
  unfold Undef. intros. funelim (find_undef_l m c). rewrite H in Heqcall. 
  apply find_some in Heqcall. destruct Heqcall. funelim (is_undefined_l m l).
  - congruence.
  - assumption.
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

Lemma undef_remove_false__undef: forall (m: PA Ann) (c: Clause) (l: Lit),
  c_eval m c = None -> c_eval m (l_remove c l) = Some false -> Undef m l.
Proof. Admitted.

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
        destruct decomp as [n_split decomp]. rewrite decomp.
        apply (t_backtrack m_split n_split f c_conflict l_split).
        -- apply (find_conflict_c_in_f m f c_conflict). assumption.
        -- rewrite <- decomp. apply (find_conflict_conflicting m f c_conflict). assumption.
        -- admit.
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
      * destruct (find_decision m f) as [l_decision|] eqn:find_decision.
        (* t_decide *)
        -- injection Heqcall as Heqcall. rewrite Heqcall. autorewrite with find_decision in find_decision.
           destruct (find_undef_c m f) as [c_decision|] eqn:find_undef_c.
          ++ simp option_bind in find_decision. apply (t_decide m f c_decision l_decision).
            ** left. apply (find_undef_l_in_c m c_decision l_decision). assumption.
            ** apply (find_undef_c_in_f m f c_decision). assumption.
            ** apply (find_undef_l_undef m c_decision l_decision). assumption.
          ++ simp option_bind in find_decision. discriminate.
        -- discriminate.
Qed.

(* The rhs is weaker because there could be multiple { s': State | s ==> s' }. *)
Lemma next_state_exists: forall (s s': State), s ==> s' -> exists (s'': State), next_state s = Some s''.
Admitted.

Lemma next_state_final_refl: forall (s: State), next_state s = None <-> Final s.
Admitted.

(* Temporarily has `n` for testing, until termination in proven. *)
Equations solve (n: nat) (s: State): State :=
solve 0     _ := s;
solve (S n) s with next_state s :=
  | Some s' := solve n s'
  | None := s.

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
