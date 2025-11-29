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

Equations eqb_lit (l1 l2: Lit): bool :=
eqb_lit (Pos p1) (Pos p2) := eqb_atom p1 p2;
eqb_lit (Neg p1) (Neg p2) := eqb_atom p1 p2;
eqb_lit _ _ => false.

Notation "l1 =? l2" := (eqb_lit l1 l2) (at level 70).

(* A clause is a disjunction of literals. *)
Definition Clause: Type := list Lit.

(* A formula is a conjunction of clauses. *)
Definition CNF: Type := list Clause.

Equations neg (l: Lit): Lit :=
neg (Pos p) := Neg p;
neg (Neg p) := Pos p.

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
l_remove [] _  := [];
l_remove (l' :: c) l  with l =? l' :=
  | true := c
  | false := l' :: l_remove c l.

Equations c_eval {A: Type} (m: PA A) (c: Clause): option bool :=
c_eval m [] := Some false;
c_eval m (l :: c) with l_eval m l, c_eval m c :=
  | Some true , _          := Some true
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
  - unfold In. right. left. reflexivity.
  - unfold Conflicting. autorewrite with c_eval. reflexivity.
  - unfold NoDecisions. unfold not. intros. destruct H. autorewrite with neg l_ann in H.
    destruct (x =? Pos 1), (x =? Neg 1); simpl in H; discriminate.
Qed.

Example unit_prop: 
  (state [] [[Pos 1];[Neg 1]]) ==>
  (state [(Pos 1, false)] [[Pos 1];[Neg 1]]).
Proof.
  apply (t_unit _ _ [Pos 1] _).
  - unfold In. left. reflexivity.
  - unfold In. left. reflexivity.
  - unfold Conflicting. autorewrite with c_eval. reflexivity.
  - unfold Undef. autorewrite with l_eval. reflexivity.
Qed.

Example decide:
  (state [] [[Pos 1];[Neg 1]]) ==>
  (state [(Pos 1, true)] [[Pos 1];[Neg 1]]).
Proof.
  apply (t_decide _ _ [Pos 1] _).
  - unfold In. left. left. reflexivity.
  - unfold In. left. reflexivity.
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
  - unfold In. right. left. reflexivity.
  - unfold Conflicting. simp c_eval. reflexivity.
  - unfold NoDecisions. unfold not. intros. destruct H. simp l_ann in H. discriminate.
Qed.

End TransExamples.

(* Splits formula into m ++d l ++a n. Propagations are stored in reverse order until return. *)
Equations split_last_decision_aux (m n: PA Ann): option (PA Ann * Lit * PA Ann) :=
split_last_decision_aux []        _ := None;
split_last_decision_aux (m ++d l) n := Some (m, l, rev n);
split_last_decision_aux (m ++p l) n := split_last_decision_aux m (n ++p l).

Equations split_last_decision (m: PA Ann): option (PA Ann * Lit * PA Ann) :=
split_last_decision m := split_last_decision_aux m [].

Equations last_decision (m: PA Ann): option Lit :=
last_decision m with split_last_decision m :=
  | Some (_, l, _) := Some l
  | _              := None.

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
  (* t_fail *)
  match find_conflict m f, last_decision m with
  | Some c, None => Some fail
  | _     , _    =>
  (* t_unit *)
  match find_unit m f with
  | Some (c, l) => Some (state (m ++p l) f)
  | None        =>
  (* t_decide *)
  match find_decision m f with
  | Some l => Some (state (m ++d l) f)
  | None   =>
  (* t_backtrack *)
  match find_conflict m f, split_last_decision m with
  | Some c, Some (m', l, n) => Some (state (m' ++p neg l) f)
  | _     , _               => None
  end end end end.

Compute (next_state (state [] [[Pos 1];[Neg 1]])).
Compute (option_bind next_state (next_state (state [] [[Pos 1];[Neg 1]]))).

Compute (next_state (state ([] ++d Pos 1) [[Pos 1];[Neg 1]])).
Compute (option_bind next_state (next_state (state ([] ++d Pos 1) [[Pos 1];[Neg 1]]))).

Lemma next_state_sound: forall (s s': State), next_state s = Some s' -> s ==> s'.
Admitted.

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
