From Stdlib Require Import List.
From Stdlib Require Import Relations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import Model.
From RocqSAT Require Import State.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import Entails.
From RocqSAT Require Import Rule.
From RocqSAT Require Import Trans.
From RocqSAT Require Import Termination.
From RocqSAT Require Import Normalization.
From RocqSAT.rules Require Import Fail.
From RocqSAT.rules Require Import Decide.

(* m assigns a value to every literal occurring in f. *)
Definition Total (m: PA) (f: CNF): Prop := forall (l: Lit), l ∈ f -> Def m l.

Definition Sat (f: CNF): Prop := exists (m: PA), Model m f.
Definition Unsat (f: CNF): Prop := ~ Sat f.

(* If every reachable state can step or is final, a final state is reachable, since there are no infinite derivations. *)
Lemma final_exists_progress: forall (rs: list Rule) (f: CNF),
  (forall (s: State), state ⟨⟩ f ==>*[rs] s -> (exists (s': State), s ==>[rs] s') \/ Final rs s) ->
  exists (s: State), state ⟨⟩ f ==>*[rs] s /\ Final rs s.
Proof.
  intros rs f Hprogress.
  assert (Hreach: forall (s: State), state ⟨⟩ f ==>*[rs] s ->
    exists (s': State), state ⟨⟩ f ==>*[rs] s' /\ Final rs s').
  - intros s. induction s as [s IH] using (well_founded_ind (trans_well_founded rs)). intros Hs.
    destruct (Hprogress s Hs) as [[s' Htrans]|Hfinal].
    + apply (IH s').
      * split.
        -- destruct s as [|m f'].
           ++ easy.
           ++ apply (derivation_well_formed rs ⟨⟩ m f f' Hs). apply initial_well_formed.
        -- assumption.
      * apply rt_trans with (y := s).
        -- assumption.
        -- now apply rt_step.
    + now exists s.
  - apply (Hreach (state ⟨⟩ f)). apply rt_refl.
Qed.

(* With Decide, a model of f gives a reachable final state: its normalization. *)
Lemma sat_final: forall (rs: list Rule) (f: CNF),
  In Decide rs -> Sat f -> exists (m: PA), state ⟨⟩ f ==>*[rs] state m f /\ Final rs (state m f).
Proof.
  intros rs f Hdecide [m Heq]. exists (normalize m f). split.
  - now apply normalize_derivation.
  - intros [s Htrans]. apply trans_rule in Htrans as [r [_ Hstep]].
    apply (rule_model_final r (normalize m f) f).
    + now apply normalize_f.
    + apply normalize_all_def.
    + now exists s.
Qed.

(* If only Fail leads to fail, reaching fail means the formula is unsatisfiable. *)
Lemma fail_unsat: forall (rs: list Rule) (f: CNF),
  (forall (r: Rule) (s: State), In r rs -> step r s fail -> FailStep s fail) ->
  state ⟨⟩ f ==>*[rs] fail -> Unsat f.
Proof.
  intros rs f Hfail Hderivation. apply fail_predecessor in Hderivation as [m [f' [Hderivation Htrans]]].
  apply trans_rule in Htrans as [r [Hr Hstep]]. apply (Hfail r) in Hstep.
  - inversion Hstep as [? ? c Hc_in_f Hconflict Hno_dec]; subst.
    pose proof Hderivation as Hequivalent. apply derivation_equivalent in Hequivalent as [Hff' _].
    apply derivation_entails in Hderivation.
    + intros [m' Hsat]. apply Hff' in Hsat.
      destruct (entails_extend f' ⟨⟩ m m') as [m'' Hm''].
      * now rewrite PA.app_empty_l.
      * assumption.
      * apply model_union_iff. split.
        -- assumption.
        -- apply model_units_iff. intros l [].
      * apply model_union_iff in Hm'' as [Hf Htrail]. rewrite PA.app_empty_l in Htrail.
        unfold Model in Hf. rewrite f_eval_true_iff in Hf. apply Hf in Hc_in_f.
        apply (units_transfer_c m'' _ _ Htrail) in Hconflict. congruence.
    + constructor.
  - assumption.
Qed.

(* A reachable final state other than fail is a model of the initial formula, if final well-formed entailed states are models. *)
Lemma final_reachable_model: forall (rs: list Rule) (m: PA) (f f': CNF),
  (forall (m: PA) (f: CNF), WellFormed (state m f) -> Entails f m -> Final rs (state m f) -> Model m f) ->
  state ⟨⟩ f ==>*[rs] state m f' -> Final rs (state m f') -> Model m f.
Proof.
  intros rs m f f' Hmodel Hderivation Hfinal. pose proof Hderivation as [_ Hf'f]%derivation_equivalent.
  apply Hf'f. apply Hmodel.
  - apply (derivation_well_formed rs ⟨⟩ m f f' Hderivation). apply initial_well_formed.
  - apply (derivation_entails rs ⟨⟩ m f f' Hderivation). constructor.
  - assumption.
Qed.

(* The main theorems, for any rule set with the properties they need. *)
Theorem sat_iff_final: forall (rs: list Rule) (f: CNF),
  In Decide rs ->
  (forall (m: PA) (f: CNF), WellFormed (state m f) -> Entails f m -> Final rs (state m f) -> Model m f) ->
  (exists (m: PA), state ⟨⟩ f ==>*[rs] state m f /\ Final rs (state m f)) <-> Sat f.
Proof.
  intros rs f Hdecide Hmodel. split.
  - intros [m [Hderivation Hfinal]]. exists m. now apply (final_reachable_model rs m f f).
  - now apply sat_final.
Qed.

Theorem unsat_iff_fail: forall (rs: list Rule) (f: CNF),
  (forall (r: Rule) (s: State), In r rs -> step r s fail -> FailStep s fail) ->
  (forall (f: CNF), exists (s: State), state ⟨⟩ f ==>*[rs] s /\ Final rs s) ->
  (forall (m: PA) (f: CNF), WellFormed (state m f) -> Entails f m -> Final rs (state m f) -> Model m f) ->
  state ⟨⟩ f ==>*[rs] fail /\ Final rs fail <-> Unsat f.
Proof.
  intros rs f Hfail Hexists Hmodel. split.
  - intros [Hderivation _]. now apply (fail_unsat rs).
  - intros Hunsat. destruct (Hexists f) as [[|m f'] [Hderivation Hfinal]].
    + now split.
    + exfalso. apply Hunsat. exists m. now apply (final_reachable_model rs m f f').
Qed.

Theorem sat_or_unsat: forall (rs: list Rule) (f: CNF),
  (forall (r: Rule) (s: State), In r rs -> step r s fail -> FailStep s fail) ->
  (forall (f: CNF), exists (s: State), state ⟨⟩ f ==>*[rs] s /\ Final rs s) ->
  (forall (m: PA) (f: CNF), WellFormed (state m f) -> Entails f m -> Final rs (state m f) -> Model m f) ->
  Sat f \/ Unsat f.
Proof.
  intros rs f Hfail Hexists Hmodel. destruct (Hexists f) as [[|m f'] [Hderivation Hfinal]].
  - right. now apply (fail_unsat rs).
  - left. exists m. now apply (final_reachable_model rs m f f').
Qed.
