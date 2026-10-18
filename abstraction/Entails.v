From Stdlib Require Import List.

From RocqSAT Require Import Lit.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import Model.

(* The entailment invariant on a trail: every propagated literal follows from f and the literals before it, except pure literals, which only have to preserve models. *)
Inductive Entails (f: CNF): PA -> Prop :=
(* The empty assignment. *)
| e_nil: 
  Entails f ⟨⟩
(* A decision is an assumption, so it needs no justification. *)
| e_decide (m: PA) (l: Lit):
  Entails f m -> Entails f ⟨m; l⟩
(* A propagated literal follows from the formula together with the assignment so far. *)
| e_propagate (m: PA) (l: Lit):
  CNF.union f (units m) ⊨ unit_cnf l ->
  Entails f m -> Entails f ⟨m, l⟩
(* A pure literal does not follow, but making it true keeps every model a model. *)
| e_pure (m: PA) (l: Lit):
  (forall (m': PA), Model m' (CNF.union f (units m)) -> Model ⟨m', l⟩ (CNF.union f (units m))) ->
  Entails f m -> Entails f ⟨m, l⟩.

(* The older part of an entailed assignment is entailed. *)
Lemma entails_prefix: forall (f: CNF) (m n: PA), Entails f ⟨m ++ n⟩ -> Entails f m.
Proof.
  intros f m n. induction n as [|n IH l|n IH l].
  - now intros.
  - intros Hentails. apply IH. now inversion Hentails.
  - intros Hentails. apply IH. now inversion Hentails.
Qed.

(* A model of f and m extends to a model of f and ⟨m ++ n⟩ if n contains no decisions. *)
Lemma entails_extend: forall (f: CNF) (m n m': PA),
  Entails f ⟨m ++ n⟩ ->
  NoDecisions n ->
  Model m' (CNF.union f (units m)) ->
  exists (m'': PA), Model m'' (CNF.union f (units ⟨m ++ n⟩)).
Proof.
  intros f m n m' Hentails Hno_dec Hm'. induction n as [|n IH l|n IH l].
  - now exists m'.
  - inversion Hentails as [| m0 l0 Hentails' | m0 l0 Himpl Hentails' | m0 l0 Hpure Hentails']; subst.
    + destruct IH as [m'' Hm''].
      * assumption.
      * assumption.
      * exists m''. pose proof (Himpl m'' Hm'') as Hl. apply model_unit_cnf_iff in Hl.
        apply model_union_iff in Hm'' as [Hf Hrest]. apply model_union_iff. split.
        -- assumption.
        -- rewrite model_units_iff in *. intros l' [<-|Hin].
          ++ assumption.
          ++ now apply Hrest.
    + destruct IH as [m'' Hm''].
      * assumption.
      * assumption.
      * exists ⟨m'', l⟩. apply Hpure in Hm''.
        apply model_union_iff in Hm'' as [Hf Hrest]. apply model_union_iff. split.
        -- assumption.
        -- rewrite model_units_iff in *. intros l' [<-|Hin].
          ++ simpl. unfold l_eval_step. now rewrite Lit.eqb_refl.
          ++ now apply Hrest.
  - contradiction.
Qed.

(* Entailment only depends on the models of the formula. *)
Lemma entails_equivalent: forall (f f': CNF) (m: PA), Equivalent f f' -> Entails f m -> Entails f' m.
Proof.
  intros f f' m Heqv Hentails.
  induction Hentails as [| m l Hentails IH | m l Himpl Hentails IH | m l Hpure Hentails IH].
  - apply e_nil.
  - now apply e_decide.
  - apply e_propagate.
    + intros m' Hm'. apply Himpl. now rewrite (model_union_equivalent m' f f' _ Heqv).
    + assumption.
  - apply e_pure.
    + intros m' Hm'. rewrite <- (model_union_equivalent _ f f' _ Heqv).
      apply Hpure. now rewrite (model_union_equivalent m' f f' _ Heqv).
    + assumption.
Qed.
