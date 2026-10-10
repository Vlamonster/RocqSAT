From Equations Require Import Equations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Model.
From RocqSAT.entailment Require Import Entails.

(* The older part of an entailed assignment is entailed. *)
Lemma entails_prefix: forall (f: CNF) (m n: PA), Entails f (m ++a n) -> Entails f m.
Proof.
  intros f m n. induction n as [|[l a] n IH].
  - now intros.
  - intros Hentails. apply IH. now inversion Hentails.
Qed.

(* A model of f and m extends to a model of f and m ++a n if n contains no decisions. *)
Lemma entails_extend: forall (f: CNF) (m n m': PA),
  Entails f (m ++a n) ->
  NoDecisions n ->
  Model m' (CNF.union f (units m)) ->
  exists (m'': PA), Model m'' (CNF.union f (units (m ++a n))).
Proof.
  intros f m n m' Hentails Hno_dec Hm'. induction n as [|[l a] n IH].
  - now exists m'.
  - inversion Hentails as [| m0 l0 Hentails' | m0 l0 Hentails' Himpl | m0 l0 Hentails' Hpure]; subst.
    + exfalso. apply Hno_dec. exists l. now left.
    + destruct IH as [m'' Hm''].
      * assumption.
      * intros [l' Hin]. apply Hno_dec. exists l'. now right.
      * exists m''. pose proof (Himpl m'' Hm'') as Hl. apply model_unit_cnf_iff in Hl.
        apply model_union_iff in Hm'' as [Hf Hrest]. apply model_union_iff. split.
        -- assumption.
        -- rewrite model_units_iff in *. simpl. intros l' a' [Heq|Hin].
          ++ now injection Heq as <- <-.
          ++ now apply (Hrest l' a').
    + destruct IH as [m'' Hm''].
      * assumption.
      * intros [l' Hin]. apply Hno_dec. exists l'. now right.
      * exists (m'' ++p l). apply Hpure in Hm''.
        apply model_union_iff in Hm'' as [Hf Hrest]. apply model_union_iff. split.
        -- assumption.
        -- rewrite model_units_iff in *. simpl. intros l' a' [Heq|Hin].
          ++ injection Heq as <- <-. simp l_eval. rewrite Neg.self_neqb_neg. now rewrite Lit.eqb_refl.
          ++ now apply (Hrest l' a').
Qed.
