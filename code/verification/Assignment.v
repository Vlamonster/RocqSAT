From Stdlib Require Import List.
Import ListNotations.

From RocqSAT Require Import Lit.

(* An annotation on a literal (Lit * Ann) describing how its value was assigned. *)
Inductive Ann: Type :=
| dec
| prop.

(* A partial assignment: a trail of annotated literals, extended on the right. Evaluation is defined in Evaluation.v. *)
Inductive PA: Type :=
| empty
| add (m: PA) (l: Lit) (a: Ann).

(* m followed by n. *)
Fixpoint extend (m n: PA): PA :=
match n with
| empty     => m
| add n l a => add (extend m n) l a
end.

(* The annotated literals of m, most recent first. *)
Fixpoint to_list (m: PA): list (Lit * Ann) :=
match m with
| empty     => []
| add m l a => (l, a) :: to_list m
end.

Coercion to_list: PA >-> list.

(* Conversely, the trail of a list of annotated literals, most recent first. *)
Fixpoint of_list (m: list (Lit * Ann)): PA :=
match m with
| []          => empty
| (l, a) :: m => add (of_list m) l a
end.

Lemma to_list_of_list: forall (m: list (Lit * Ann)), to_list (of_list m) = m.
Proof.
  induction m as [|[l a] m IH].
  - reflexivity.
  - simpl. now rewrite IH.
Qed.

Lemma of_list_to_list: forall (m: PA), of_list (to_list m) = m.
Proof.
  induction m as [|m IH l a].
  - reflexivity.
  - simpl. now rewrite IH.
Qed.

(* A literal on its own is the trail in which it is propagated. *)
Definition single (l: Lit): PA := add empty l prop.

Coercion single: Lit >-> PA.

(* Trails are written left to right between ⟨ ⟩: ⟨m, l⟩ propagates l and ⟨m; l⟩ decides l after m.
   On the empty trail ⟨⟩ this is written ⟨, l1, l2; l3⟩, which propagates l1 and l2 and then decides l3. *)
Declare Custom Entry trail.
Notation "⟨ m ⟩" := m (m custom trail at level 2).
Notation "⟨ ⟩" := empty.
Notation "∅" := empty (in custom trail at level 0).
Notation "m , l" := (add m l prop) (in custom trail at level 1, left associativity, l constr at level 0).
Notation "m ; l" := (add m l dec) (in custom trail at level 1, left associativity, l constr at level 0).
Notation "; l" := (add empty l dec) (in custom trail at level 1, l constr at level 0).
Notation ", l" := (add empty l prop) (in custom trail at level 1, l constr at level 0).
Notation "m ++ n" := (extend m n) (in custom trail at level 2, left associativity, n custom trail at level 1).
Notation "x" := x (in custom trail at level 0, x ident).
Notation "( x )" := x (in custom trail at level 0, x constr).

Lemma extend_empty_l: forall (m: PA), ⟨∅ ++ m⟩ = m.
Proof.
  induction m as [|m IH l a].
  - reflexivity.
  - simpl. now rewrite IH.
Qed.

Lemma to_list_extend: forall (m n: PA), to_list ⟨m ++ n⟩ = to_list n ++ to_list m.
Proof.
  intros m n. induction n as [|n IH l a].
  - reflexivity.
  - simpl. now rewrite IH.
Qed.

(* An assignment without decision literals. *)
Definition NoDecisions (m: PA): Prop := ~ exists (l: Lit), In (l, dec) m.

(* Splits off the most recent decision literal, if any. *)
Fixpoint split_last_decision (m: PA): option (PA * Lit) :=
match m with
| ⟨⟩    => None
| ⟨m, l⟩ => split_last_decision m
| ⟨m; l⟩ => Some (m, l)
end.

Lemma split_last_decision_some_iff: forall (m m': PA) (l': Lit),
  split_last_decision m = Some (m', l') <-> exists (n': PA), m = ⟨m'; l' ++ n'⟩ /\ NoDecisions n'.
Proof.
  intros m m' l'. split.
  - induction m as [|m IH l [|]]; simpl.
    + discriminate.
    + intros Hsplit. injection Hsplit as <- <-. exists ⟨⟩. split.
      * reflexivity.
      * intros [l'' []].
    + intros Hsplit. apply IH in Hsplit as [n' [Heq Hno_dec]]. exists ⟨n', l⟩. split.
      * now rewrite Heq.
      * intros [l'' [Heq'|Hin]].
        -- discriminate.
        -- apply Hno_dec. now exists l''.
  - intros [n' [-> Hno_dec]]. induction n' as [|n' IH l [|]]; simpl.
    + reflexivity.
    + exfalso. apply Hno_dec. exists l. now left.
    + apply IH. intros [l'' Hin]. apply Hno_dec. exists l''. now right.
Qed.

Lemma split_last_decision_none_iff: forall (m: PA), split_last_decision m = None <-> NoDecisions m.
Proof.
  induction m as [|m IH l [|]]; simpl.
  - split.
    + intros _ [l []].
    + reflexivity.
  - split.
    + discriminate.
    + intros Hno_dec. exfalso. apply Hno_dec. exists l. now left.
  - rewrite IH. split.
    + intros Hno_dec [l' [Heq|Hin]].
      * discriminate.
      * apply Hno_dec. now exists l'.
    + intros Hno_dec [l' Hin]. apply Hno_dec. exists l'. now right.
Qed.
