From Stdlib Require Import List.
Import ListNotations.

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

(* Fail: Fail if all literals are assigned and there is a conflict. *)

Lemma fail_entails: forall (m m': PA) (f: CNF) (Hwf: WellFormed m f) (Hwf': WellFormed m' f),
  state m f Hwf ==>[[Fail]] state m' f Hwf' -> Entails f m -> Entails f m'.
Proof. intros. inversion H; simpl in *; intuition discriminate. Qed.

Lemma fail_state_lt: forall (m: PA) (f: CNF) (s': State) (Hwf: WellFormed m f),
  state m f Hwf ==>[[Fail]] s' -> state m f Hwf >>[f] s'.
Proof.
  intros.
  inversion H as [m' f' c_conflict Hwf' _ Hc_in_f Hconflict Hno_dec | | | |];
    subst s'; try subst m'; try subst f'; try (simpl in *; intuition discriminate).
  unfold StateLt. now left.
Qed.

Lemma fail_model_final: forall (m: PA) (f: CNF) (Hwf: WellFormed m f),
  Model m f ->
  (forall (l: Lit), (exists (c: Clause), Clause.In l c /\ CNF.In c f) -> Def m l) ->
  ~ exists (s: State), state m f Hwf ==>[[Fail]] s.
Proof.
  intros m' f Hwf Heq Hall_def. unfold not. intros [s Htrans].
  inversion Htrans as [m f' c_conflict Hwf' _ Hc_in_f Hconflict Hno_dec | | | |];
    subst s; try subst m; try subst f'; try (simpl in *; intuition discriminate).
  assert (f_eval m' f = Some false).
  - apply f_eval_false_iff. now exists c_conflict.
  - congruence.
Qed.
