From Stdlib Require Import List.
Import ListNotations.

From RocqSAT Require Import Atom.
From RocqSAT Require Import Lit.
From RocqSAT.utils Require Export Member.

(* Trails are written between ⟨ ⟩, see the notations below. *)
Declare Custom Entry trail.

Module PA.
  Module Definitions.
    (* A partial assignment: a trail of propagated and decided literals, extended on the right. Evaluation is defined in Evaluation.v. *)
    Inductive PA: Type :=
    | empty
    | propagate (m: PA) (l: Lit)
    | decide (m: PA) (l: Lit).

    (* Trails are written left to right between ⟨ ⟩: ⟨m, l⟩ propagates l and ⟨m; l⟩ decides l after m.
       On the empty trail ⟨⟩ this is written ⟨, l1, l2; l3⟩, which propagates l1 and l2 and then decides l3. *)
    Notation "⟨ m ⟩" := m (m custom trail at level 2).
    Notation "⟨ ⟩" := empty.
    Notation "∅" := empty (in custom trail at level 0).
    Notation "x" := x (in custom trail at level 0, x ident).
    Notation "( x )" := x (in custom trail at level 0, x constr).
    Notation "m , l" := (propagate m l) (in custom trail at level 1, left associativity, l constr at level 0).
    Notation "m ; l" := (decide m l) (in custom trail at level 1, left associativity, l constr at level 0).
    Notation ", l" := (propagate empty l) (in custom trail at level 1, l constr at level 0).
    Notation "; l" := (decide empty l) (in custom trail at level 1, l constr at level 0).

    (* The atoms of the literals of m, most recent first. *)
    Fixpoint atoms (m: PA): list Atom :=
    match m with
    | ⟨⟩     => []
    | ⟨m, l⟩ => extract l :: atoms m
    | ⟨m; l⟩ => extract l :: atoms m
    end.

    (* m has no decisions, or no propagations. *)
    Fixpoint NoDecisions (m: PA): Prop :=
    match m with
    | ⟨⟩     => True
    | ⟨m, _⟩ => NoDecisions m
    | ⟨m; _⟩ => False
    end.

    Fixpoint NoPropagations (m: PA): Prop :=
    match m with
    | ⟨⟩     => True
    | ⟨m, _⟩ => False
    | ⟨m; _⟩ => NoPropagations m
    end.

    (* Splits off the most recent decision literal, if any. *)
    Fixpoint split_last_decision (m: PA): option (PA * Lit) :=
    match m with
    | ⟨⟩     => None
    | ⟨m, l⟩ => split_last_decision m
    | ⟨m; l⟩ => Some (m, l)
    end.
  End Definitions.

  Include Definitions.

  (* The counterparts of the list operations of the same name; used qualified, or through the notations below. *)

  (* m followed by n. *)
  Fixpoint app (m n: PA): PA :=
  match n with
  | ⟨⟩     => m
  | ⟨n, l⟩ => ⟨(app m n), l⟩
  | ⟨n; l⟩ => ⟨(app m n); l⟩
  end.

  (* l is assigned in m, by a propagation or a decision. *)
  Fixpoint In (l: Lit) (m: PA): Prop :=
  match m with
  | ⟨⟩      => False
  | ⟨m, l'⟩ => l' = l \/ In l m
  | ⟨m; l'⟩ => l' = l \/ In l m
  end.

  (* The number of literals of m. *)
  Fixpoint length (m: PA): nat :=
  match m with
  | ⟨⟩     => 0
  | ⟨m, _⟩ => S (length m)
  | ⟨m; _⟩ => S (length m)
  end.

  Module Notations.
    Notation "m ++ n" := (app m n) (in custom trail at level 2, left associativity, n custom trail at level 1).

    #[export]
    Instance MemberPA: Member Lit PA := In.
  End Notations.

  Import Notations.

  Module Lemmas.
    Lemma app_empty_l: forall (m: PA), ⟨∅ ++ m⟩ = m.
    Proof.
      induction m as [|m IH l|m IH l].
      - reflexivity.
      - simpl. now rewrite IH.
      - simpl. now rewrite IH.
    Qed.

    Lemma in_app_iff: forall (m n: PA) (l: Lit), l ∈ ⟨m ++ n⟩ <-> l ∈ n \/ l ∈ m.
    Proof.
      intros m n l. induction n as [|n IH l'|n IH l']; cbn.
      - split.
        + now right.
        + now intros [[]|Hin].
      - rewrite IH. tauto.
      - rewrite IH. tauto.
    Qed.

    Lemma length_atoms: forall (m: PA), List.length (atoms m) = length m.
    Proof.
      induction m as [|m IH l|m IH l].
      - reflexivity.
      - simpl. now rewrite IH.
      - simpl. now rewrite IH.
    Qed.

    Lemma in_atoms: forall (m: PA) (p: Atom), List.In p (atoms m) <-> exists (l: Lit), l ∈ m /\ extract l = p.
    Proof.
      intros m p. induction m as [|m IH l|m IH l]; simpl.
      - split.
        + intros [].
        + intros [l [[] _]].
      - rewrite IH. split.
        + intros [Heq|[l' [Hin Heq]]].
          * exists l. split.
            -- now left.
            -- assumption.
          * exists l'. split.
            -- now right.
            -- assumption.
        + intros [l' [[<-|Hin] Heq]].
          * now left.
          * right. now exists l'.
      - rewrite IH. split.
        + intros [Heq|[l' [Hin Heq]]].
          * exists l. split.
            -- now left.
            -- assumption.
          * exists l'. split.
            -- now right.
            -- assumption.
        + intros [l' [[<-|Hin] Heq]].
          * now left.
          * right. now exists l'.
    Qed.

    Lemma split_last_decision_some_iff: forall (m m': PA) (l': Lit),
      split_last_decision m = Some (m', l') <-> exists (n': PA), m = ⟨m'; l' ++ n'⟩ /\ NoDecisions n'.
    Proof.
      intros m m' l'. split.
      - induction m as [|m IH l|m IH l]; simpl.
        + discriminate.
        + intros Hsplit. apply IH in Hsplit as [n' [Heq Hno_dec]]. exists ⟨n', l⟩. split.
          * now rewrite Heq.
          * assumption.
        + intros Hsplit. injection Hsplit as <- <-. now exists ⟨⟩.
      - intros [n' [-> Hno_dec]]. induction n' as [|n' IH l|n' IH l]; simpl.
        + reflexivity.
        + now apply IH.
        + contradiction.
    Qed.

    Lemma split_last_decision_none_iff: forall (m: PA), split_last_decision m = None <-> NoDecisions m.
    Proof.
      induction m as [|m IH l|m IH l]; simpl.
      - now split.
      - assumption.
      - split.
        + discriminate.
        + contradiction.
    Qed.
  End Lemmas.

  Include Lemmas.
End PA.

Export PA.Definitions PA.Notations.
