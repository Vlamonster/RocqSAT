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

(* Unit: If a clause is false except for one unassigned literal, assign it to satisfy the clause. *)

Lemma unit_entails: forall (m m': PA) (f: CNF) (Hwf: WellFormed m f) (Hwf': WellFormed m' f),
  state m f Hwf ==>[[Unit]] state m' f Hwf' -> Entails f m -> Entails f m'.
Proof.
  intros m m' f Hwf Hwf' Htrans Hentails.
  inversion Htrans as [| m'' f' c_unit l_unit ? Hwf'' _ Hl_in_c Hc_in_f Hconflict Hundef | | |];
    try subst m''; try subst f'; try (simpl in *; intuition discriminate).
  apply e_propagate.
  - intros m'' Hm''. apply model_unit_cnf_iff.
    apply model_union_iff in Hm'' as [Hf Hm].
    apply (units_transfer_c m'' m _ Hm) in Hconflict.
    unfold Model in Hf. rewrite f_eval_true_iff in Hf. apply Hf in Hc_in_f.
    destruct (l_eval m'' l_unit) as [[|]|] eqn:Hl.
    + reflexivity.
    + rewrite (c_eval_remove_false_l _ _ _ Hconflict Hl) in Hc_in_f. discriminate.
    + rewrite (c_eval_remove_none_l _ _ _ Hl_in_c Hconflict Hl) in Hc_in_f. discriminate.
  - assumption.
Qed.

Lemma unit_state_lt: forall (m: PA) (f: CNF) (s': State) (Hwf: WellFormed m f),
  state m f Hwf ==>[[Unit]] s' -> state m f Hwf >>[f] s'.
Proof.
  intros.
  inversion H as [| m' f' c_unit l_unit ? Hwf' _ Hl_in_c Hc_in_f Hconflict Hundef | | |];
    subst s'; try subst m'; try subst f'; try (simpl in *; intuition discriminate).
  unfold StateLt. right. unfold MR. simp state_measure. apply left_slex.
  now apply prefix_prop.
Qed.

Lemma unit_model_final: forall (m: PA) (f: CNF) (Hwf: WellFormed m f),
  Model m f ->
  (forall (l: Lit), (exists (c: Clause), Clause.In l c /\ CNF.In c f) -> Def m l) ->
  ~ exists (s: State), state m f Hwf ==>[[Unit]] s.
Proof.
  intros m' f Hwf Heq Hall_def. unfold not. intros [s Htrans].
  inversion Htrans as [| m f' c_unit l_unit ? Hwf' _ Hl_in_c Hc_in_f Hconflict Hundef | | |];
    subst s; try subst m; try subst f'; try (simpl in *; intuition discriminate).
  assert (Def m' l_unit).
  - apply Hall_def. now exists c_unit.
  - now apply def_undef in H.
Qed.
