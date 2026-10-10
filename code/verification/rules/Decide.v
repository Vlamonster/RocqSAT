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

(* Decide: Arbitrarily set an unassigned literal in the formula to true. *)

Lemma decide_entails: forall (m m': PA) (f: CNF) (Hwf: WellFormed m f) (Hwf': WellFormed m' f),
  state m f Hwf ==>[[Decide]] state m' f Hwf' -> Entails f m -> Entails f m'.
Proof.
  intros m m' f Hwf Hwf' Htrans Hentails.
  inversion Htrans as [| | m'' f' c_decide l_decide ? Hwf'' _ Hx_in_c Hc_in_f Hundef | |];
    try subst m''; try subst f'; try (simpl in *; intuition discriminate).
  now apply e_decide.
Qed.

Lemma decide_state_lt: forall (m: PA) (f: CNF) (s': State) (Hwf: WellFormed m f),
  state m f Hwf ==>[[Decide]] s' -> state m f Hwf >>[f] s'.
Proof.
  intros.
  inversion H as [| | m' f' c_decide l_decide ? Hwf' _ Hx_in_c Hc_in_f Hundef | |];
    subst s'; try subst m'; try subst f'; try (simpl in *; intuition discriminate).
  unfold StateLt. right. unfold MR. simp state_measure. rewrite score_dec.
  - apply right_slex. now apply total_decide.
  - assumption.
Qed.

Lemma decide_model_final: forall (m: PA) (f: CNF) (Hwf: WellFormed m f),
  Model m f ->
  (forall (l: Lit), (exists (c: Clause), Clause.In l c /\ CNF.In c f) -> Def m l) ->
  ~ exists (s: State), state m f Hwf ==>[[Decide]] s.
Proof.
  intros m' f Hwf Heq Hall_def. unfold not. intros [s Htrans].
  inversion Htrans as [| | m f' c_decide l_decide ? Hwf' _ Hx_in_c Hc_in_f Hundef | |];
    subst s; try subst m; try subst f'; try (simpl in *; intuition discriminate).
  destruct Hx_in_c as [Hl_in_c|Hnegl_in_c].
  - assert (Def m' l_decide).
    + apply Hall_def. now exists c_decide.
    + now apply def_undef in H.
  - assert (Def m' (¬l_decide)).
    + apply Hall_def. now exists c_decide.
    + apply def_undef in H. unfold Undef in H. now rewrite <- l_eval_neg_none_iff in H.
Qed.
