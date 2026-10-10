From Stdlib Require Import List.
From Stdlib Require Import Relations.
Import ListNotations.

From Equations Require Import Equations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import Model.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import Trans.
From RocqSAT.entailment Require Import Entails.
From RocqSAT Require Import Measure.

(* Pure: Adds a literal that only occurs positively. *)

Lemma pure_entails: forall (m m': PA) (f: CNF) (Hwf: WellFormed m f) (Hwf': WellFormed m' f),
  state m f Hwf ==>[[Pure]] state m' f Hwf' -> Entails f m -> Entails f m'.
Proof.
  intros m m' f Hwf Hwf' Htrans Hentails.
  inversion Htrans as [| | | | m'' f' c_pure l_pure ? Hwf'' _ Hl_in_c Hc_in_f Hpure Hundef];
    try subst m''; try subst f'; try (simpl in *; intuition discriminate).
  apply e_pure.
  - assumption.
  - intros m'' Hm''. apply model_union_iff in Hm'' as [Hf Hm]. apply model_union_iff. split.
    + apply f_eval_true_iff. intros c Hc. apply c_eval_true_iff.
      unfold Model in Hf. rewrite f_eval_true_iff in Hf. apply Hf in Hc as G.
      rewrite c_eval_true_iff in G. destruct G as [l [Hin Hl]].
      exists l. split.
      * assumption.
      * simp l_eval. destruct (l =? ¬l_pure) eqn:G1, (l =? l_pure) eqn:G2; simpl.
        -- reflexivity.
        -- exfalso. apply Lit.eqb_eq in G1. subst l. now apply (Hpure c).
        -- reflexivity.
        -- assumption.
    + rewrite model_units_iff in *.
      intros l a Hin. simp l_eval. destruct (l =? ¬l_pure) eqn:G1, (l =? l_pure) eqn:G2; simpl.
      * reflexivity.
      * exfalso. apply Lit.eqb_eq in G1. subst l. apply (def_undef m l_pure).
        -- apply l_eval_some_iff. exists a. now right.
        -- assumption.
      * reflexivity.
      * now apply (Hm l a).
Qed.

Lemma pure_state_lt: forall (m: PA) (f: CNF) (s': State) (Hwf: WellFormed m f),
  state m f Hwf ==>[[Pure]] s' -> state m f Hwf >>[f] s'.
Proof.
  intros.
  inversion H as [| | | | m' f' c_pure l_pure ? Hwf' _ Hl_in_c Hc_in_f Hpure Hundef];
    subst s'; try subst m'; try subst f'; try (simpl in *; intuition discriminate).
  unfold StateLt. right. unfold MR. simp state_measure. apply left_slex.
  now apply prefix_prop.
Qed.

Lemma pure_model_final: forall (m: PA) (f: CNF) (Hwf: WellFormed m f),
  Model m f ->
  (forall (l: Lit), (exists (c: Clause), Clause.In l c /\ CNF.In c f) -> Def m l) ->
  ~ exists (s: State), state m f Hwf ==>[[Pure]] s.
Proof.
  intros m' f Hwf Heq Hall_def. unfold not. intros [s Htrans].
  inversion Htrans as [| | | | m f' c_pure l_pure ? Hwf' _ Hl_in_c Hc_in_f Hpure Hundef];
    subst s; try subst m; try subst f'; try (simpl in *; intuition discriminate).
  assert (Def m' l_pure).
  - apply Hall_def. now exists c_pure.
  - now apply def_undef in H.
Qed.
