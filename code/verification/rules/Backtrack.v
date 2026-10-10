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
From RocqSAT.entailment Require Import Properties.
From RocqSAT Require Import Measure.

(* Backtrack: Backtrack by flipping the most recent decision literal. *)

(* With a conflict after deciding l, no model of the formula and m makes l true. *)
Lemma backtrack_no_model: forall (m n: PA) (f: CNF) (c: Clause) (l: Lit) (m': PA),
  NoDecisions n ->
  Entails f (m ++d l ++a n) ->
  CNF.In c f ->
  c_eval (m ++d l ++a n) c = Some false ->
  Model m' (CNF.union f (units m)) -> l_eval m' l = Some true -> False.
Proof.
  intros m n f c l m' Hno_dec Hentails Hc_in_f Hconflict Hm' Hl.
  destruct (entails_extend f (m ++d l) n m' Hentails Hno_dec) as [m'' Hm''].
  - apply model_union_iff in Hm' as [Hf Hm]. apply model_union_iff. split.
    + assumption.
    + rewrite model_units_iff in *. intros l' a' [Heq|Hin].
      * now injection Heq as <- <-.
      * now apply (Hm l' a').
  - apply model_union_iff in Hm'' as [Hf Htrail].
    unfold Model in Hf. rewrite f_eval_true_iff in Hf. apply Hf in Hc_in_f.
    apply (units_transfer_c m'' _ _ Htrail) in Hconflict. congruence.
Qed.

(* Hence the formula and m force ¬l. *)
Lemma backtrack_neg: forall (m n: PA) (f: CNF) (c: Clause) (l: Lit),
  NoDecisions n ->
  Entails f (m ++d l ++a n) ->
  CNF.In c f ->
  c_eval (m ++d l ++a n) c = Some false ->
  CNF.union f (units m) ⊨ unit_cnf (¬l).
Proof.
  intros m n f c l Hno_dec Hentails Hc_in_f Hconflict m' Hm'. apply model_unit_cnf_iff.
  destruct (l_eval m' l) as [[|]|] eqn:Hl.
  - exfalso. now apply (backtrack_no_model m n f c l m').
  - now apply l_eval_neg_some_iff in Hl.
  - exfalso. apply (backtrack_no_model m n f c l (m' ++p l) Hno_dec Hentails Hc_in_f Hconflict).
    + now apply f_eval_extend_undef.
    + simp l_eval. rewrite Neg.self_neqb_neg. now rewrite Lit.eqb_refl.
Qed.

Lemma backtrack_entails: forall (m m': PA) (f: CNF) (Hwf: WellFormed m f) (Hwf': WellFormed m' f),
  state m f Hwf ==>[[Backtrack]] state m' f Hwf' -> Entails f m -> Entails f m'.
Proof.
  intros m m' f Hwf Hwf' Htrans Hentails.
  inversion Htrans as [| | | m_split n_split f' c_conflict l_split ? Hwf'' _ Hc_in_f Hconflict Hno_dec |];
    try subst m''; try subst f'; try (simpl in *; intuition discriminate).
  subst m. apply e_propagate.
  - apply (entails_prefix f m_split [(l_split, dec)]). now apply entails_prefix in Hentails.
  - now apply (backtrack_neg m_split n_split f c_conflict l_split).
Qed.

Lemma backtrack_state_lt: forall (m: PA) (f: CNF) (s': State) (Hwf: WellFormed m f),
  state m f Hwf ==>[[Backtrack]] s' -> state m f Hwf >>[f] s'.
Proof.
  intros.
  inversion H as [| | | m_split n_split f' c_conflict l_split ? Hwf' _ Hc_in_f Hconflict Hno_dec |];
    subst s'; try subst m'; try subst f'; try (simpl in *; intuition discriminate).
  unfold StateLt. right. unfold MR. simp state_measure. rewrite <- H0. apply left_slex.
  apply prefix_app.
  - assumption.
  - now rewrite H0.
Qed.

Lemma backtrack_model_final: forall (m: PA) (f: CNF) (Hwf: WellFormed m f),
  Model m f ->
  (forall (l: Lit), (exists (c: Clause), Clause.In l c /\ CNF.In c f) -> Def m l) ->
  ~ exists (s: State), state m f Hwf ==>[[Backtrack]] s.
Proof.
  intros m' f Hwf Heq Hall_def. unfold not. intros [s Htrans].
  inversion Htrans as [| | | m_split n_split f' c_conflict l_split ? Hwf' _ Hc_in_f Hconflict Hno_dec |];
    subst s; try subst m; try subst f'; try (simpl in *; intuition discriminate).
  rewrite H in *. assert (f_eval m' f = Some false).
  - apply f_eval_false_iff. now exists c_conflict.
  - congruence.
Qed.
