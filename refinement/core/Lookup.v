From Stdlib Require Import Arith.

From RocqSAT Require Import Lit.
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

(* The values of m: replaying the trail, so that the most recent assignment of each atom wins. *)
Fixpoint values (m: PA): Values :=
match m with
| ⟨⟩     => tmake None
| ⟨m, l⟩ => set_value (values m) l
| ⟨m; l⟩ => set_value (values m) l
end.

Section Literals.
  (* The value of l according to v. *)
  Definition lookup (v: Values) (l: Lit): option bool :=
  match tget v (extract l) with
  | Some b => Some (if is_pos l then b else negb b)
  | None   => None
  end.

  (* Boolean tests for the three possible values of a literal. *)
  Definition lookup_true (v: Values) (l: Lit): bool :=
  match lookup v l with
  | Some true => true
  | _         => false
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

  (* After adding the value of l, l is true. *)
  Lemma lookup_add_self: forall (v: Values) (l: Lit), lookup (set_value v l) l = Some true.
  Proof. intros v l. rewrite lookup_add. unfold l_eval_step. now rewrite Lit.eqb_refl. Qed.

  (* Every literal other than l and ¬l keeps its value. *)
  Lemma lookup_add_other: forall (v: Values) (l l': Lit),
    l' <> l -> l' <> ¬l -> lookup (set_value v l) l' = lookup v l'.
  Proof.
    intros v l l' Hneq Hneq_neg. rewrite lookup_add. unfold l_eval_step. destruct (l' =? l) eqn:G1.
    - now apply Lit.eqb_eq in G1.
    - destruct (l' =? ¬l) eqn:G2.
      + now apply Lit.eqb_eq in G2.
      + reflexivity.
  Qed.

  (* The value of ¬l is the negation of the value of l. *)
  Lemma lookup_neg: forall (v: Values) (l: Lit), lookup v (¬l) = option_map negb (lookup v l).
  Proof. intros v [p|p]; unfold lookup; simpl; destruct (tget v p) as [[|]|]; reflexivity. Qed.

  (* Every value of v' is a value of v: v' are the values of an earlier trail. *)
  Definition Incl (v' v: Values): Prop := forall (l: Lit) (b: bool), lookup v' l = Some b -> lookup v l = Some b.

  (* Incl is reflexive and transitive. *)
  Lemma incl_refl: forall (v: Values), Incl v v.
  Proof. now intros v l b Hl. Qed.

  Lemma incl_trans: forall (v1 v2 v3: Values), Incl v1 v2 -> Incl v2 v3 -> Incl v1 v3.
  Proof. intros v1 v2 v3 H12 H23 l b Hl. now apply H23, H12. Qed.

  (* Assigning an unassigned literal only adds values. *)
  Lemma incl_set_value: forall (v' v: Values) (l: Lit), Incl v' v -> lookup v l = None -> Incl v' (set_value v l).
  Proof.
    intros v' v l Hincl Hl l' b Hl'. apply Hincl in Hl'. rewrite lookup_add_other.
    - assumption.
    - intros ->. congruence.
    - intros ->. rewrite lookup_neg, Hl in Hl'. discriminate.
  Qed.

  (* v with the value of the atom of l removed. *)
  Definition unset_value (v: Values) (l: Lit): Values := tset v (extract l) None.

  (* Unsetting the atom of l makes l and ¬l unassigned and keeps the others. *)
  Lemma lookup_unset: forall (v: Values) (l l': Lit),
    lookup (unset_value v l) l' = if Nat.eq_dec (extract l) (extract l') then None else lookup v l'.
  Proof.
    intros v l l'. unfold lookup, unset_value. rewrite tget_tset.
    now destruct (Nat.eq_dec (extract l) (extract l')).
  Qed.

  (* v holds exactly the values of the trail m. *)
  Definition ValuesOf (v: Values) (m: PA): Prop := forall (l: Lit), lookup v l = l_eval m l.

  (* Every literal of m was unassigned when it was added, so no atom is assigned twice. *)
  Fixpoint Fresh (m: PA): Prop :=
  match m with
  | ⟨⟩     => True
  | ⟨m, l⟩ => Fresh m /\ l_eval m l = None
  | ⟨m; l⟩ => Fresh m /\ l_eval m l = None
  end.

  (* Unsetting the newest literal l of ⟨m, l⟩, unassigned in m, gives the values of m. *)
  Lemma values_of_unset: forall (v: Values) (m: PA) (l: Lit),
    ValuesOf v ⟨m, l⟩ -> l_eval m l = None -> ValuesOf (unset_value v l) m.
  Proof.
    intros v m l Hv Hl y. rewrite lookup_unset.
    destruct (Nat.eq_dec (extract l) (extract y)) as [Heq|Hneq].
    - symmetry in Heq. apply Neg.extract_eq in Heq as [-> | ->].
      + now symmetry.
      + symmetry. now apply l_eval_neg_none_iff in Hl.
    - rewrite Hv. simpl. unfold l_eval_step. destruct (y =? l) eqn:Hyl.
      + apply Lit.eqb_eq in Hyl as ->. contradiction.
      + destruct (y =? ¬l) eqn:Hynegl.
        * apply Lit.eqb_eq in Hynegl as ->. exfalso. apply Hneq. apply Neg.extract_eq. right. now rewrite Neg.involutive.
        * reflexivity.
  Qed.

  (* v without the values of the last decision level of m, from its most recent literal down to the decision. *)
  Fixpoint unassign_level (v: Values) (m: PA): Values :=
  match m with
  | ⟨⟩     => v
  | ⟨m, l⟩ => unassign_level (unset_value v l) m
  | ⟨m; l⟩ => unset_value v l
  end.

  (* Unassigning the last decision level gives the values of the trail before its decision. *)
  Lemma unassign_level_spec: forall (v: Values) (m m': PA) (l: Lit),
    ValuesOf v m -> Fresh m -> split_last_decision m = Some (m', l) -> ValuesOf (unassign_level v m) m'.
  Proof.
    intros v m. revert v. induction m as [|m IH l0|m IH l0]; intros v m' l Hv Hfresh Hsplit; simpl in Hsplit |- *.
    - discriminate.
    - destruct Hfresh as [Hfresh Hl0]. apply (IH (unset_value v l0) m' l).
      + apply values_of_unset.
        * intros y. apply Hv.
        * assumption.
      + assumption.
      + assumption.
    - injection Hsplit as <- <-. destruct Hfresh as [_ Hl0]. apply values_of_unset.
      + intros y. apply Hv.
      + assumption.
  Qed.

  (* Looking up the values of m agrees with l_eval. *)
  Lemma lookup_values: forall (m: PA) (l: Lit), lookup (values m) l = l_eval m l.
  Proof.
    intros m l. induction m as [|m IH l'|m IH l'].
    - reflexivity.
    - simpl. now rewrite lookup_add, IH.
    - simpl. now rewrite lookup_add, IH.
  Qed.

  (* The older part of a fresh trail is fresh. *)
  Lemma fresh_app: forall (m n: PA), Fresh ⟨m ++ n⟩ -> Fresh m.
  Proof.
    intros m n. induction n as [|n IH x|n IH x]; simpl.
    - easy.
    - intros [Hfresh _]. now apply IH.
    - intros [Hfresh _]. now apply IH.
  Qed.

  (* The literals after the older part of a fresh trail were unassigned in it. *)
  Lemma fresh_app_undef: forall (m n: PA) (l: Lit), Fresh ⟨m ++ n⟩ -> l ∈ n -> l_eval m l = None.
  Proof.
    intros m n l. induction n as [|n IH x|n IH x]; simpl.
    - intros _ [].
    - intros [Hfresh Hx] [->|Hin].
      + destruct (l_eval n l) as [b|] eqn:Hn.
        * rewrite (l_eval_app_some m n l b Hn) in Hx. discriminate.
        * now rewrite l_eval_app_undef in Hx.
      + now apply IH.
    - intros [Hfresh Hx] [->|Hin].
      + destruct (l_eval n l) as [b|] eqn:Hn.
        * rewrite (l_eval_app_some m n l b Hn) in Hx. discriminate.
        * now rewrite l_eval_app_undef in Hx.
      + now apply IH.
  Qed.

  (* In a fresh trail, every assigned literal is true. *)
  Lemma fresh_in_true: forall (m: PA) (l: Lit), Fresh m -> l ∈ m -> l_eval m l = Some true.
  Proof.
    intros m l. induction m as [|m IH x|m IH x]; intros Hfresh Hin.
    - destruct Hin.
    - destruct Hfresh as [Hfresh Hx]. destruct Hin as [<-|Hin].
      + simpl. unfold l_eval_step. now rewrite Lit.eqb_refl.
      + apply l_eval_cons_undef.
        * assumption.
        * now apply IH.
    - destruct Hfresh as [Hfresh Hx]. destruct Hin as [<-|Hin].
      + simpl. unfold l_eval_step. now rewrite Lit.eqb_refl.
      + apply (l_eval_cons_undef m l x).
        * assumption.
        * now apply IH.
  Qed.

  (* v without the values of the literals of n and then d: the values before the decision d of ⟨mt; d ++ n⟩. *)
  Fixpoint unassign_segment (v: Values) (d: Lit) (n: PA): Values :=
  match n with
  | ⟨⟩     => unset_value v d
  | ⟨n, x⟩ => unassign_segment (unset_value v x) d n
  | ⟨n; x⟩ => unassign_segment (unset_value v x) d n
  end.

  (* Unassigning the segment gives the values of the trail before its decision. *)
  Lemma unassign_segment_spec: forall (v: Values) (mt n: PA) (d: Lit),
    ValuesOf v ⟨mt; d ++ n⟩ -> Fresh ⟨mt; d ++ n⟩ -> ValuesOf (unassign_segment v d n) mt.
  Proof.
    intros v mt n d. revert v. induction n as [|n IH x|n IH x]; intros v Hv Hfresh; simpl in Hfresh |- *.
    - destruct Hfresh as [_ Hd]. apply values_of_unset.
      + intros y. apply Hv.
      + assumption.
    - destruct Hfresh as [Hfresh Hx]. apply IH.
      + apply values_of_unset.
        * intros y. apply Hv.
        * assumption.
      + assumption.
    - destruct Hfresh as [Hfresh Hx]. apply IH.
      + apply values_of_unset.
        * intros y. apply Hv.
        * assumption.
      + assumption.
  Qed.
End Literals.

