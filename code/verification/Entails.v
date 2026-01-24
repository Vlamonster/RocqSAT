From Equations Require Import Equations.
From Stdlib Require Import List Relations.
Import ListNotations.
From RocqSAT Require Import Lit Neg Clause CNF Evaluation WellFormed Trans.

Inductive Entails: CNF -> PA -> Prop :=
| e_intro (f: CNF) (n: PA):
  (forall (m: PA), 
    f_eval m f = Some true -> m_eval m n = Some true) ->
  NoDecisions n ->
  Entails f n
| e_step (f: CNF) (m n: PA) (l: Lit):
  (forall (m': PA), 
    f_eval m' f = Some true /\
    m_eval m' m = Some true /\
    l_eval m' l = Some true -> m_eval m' n = Some true) ->
  NoDecisions n ->
  Entails f m ->
  Entails f (m ++d l ++a n).

Lemma trans_entails: forall (m m': PA) (f: CNF) (Hwf: WellFormed m f) (Hwf': WellFormed m' f),
  state m f Hwf ==> state m' f Hwf' -> Entails f m -> Entails f m'.
Proof.
  intros m m' f Hwf Hwf' Htrans Hentails. inversion Htrans as
  [
    m'' f' c_conflict Hwf'' Hc_in_f Hconflict Hno_dec |
    m'' f' c_unit l_unit ? Hwf'' Hl_in_c Hc_in_f Hconflict Hundef |
    m'' f' c_decide l_decide ? Hwf'' Hx_in_c Hc_in_f Hundef |
    m_split n_split f' c_conflict l_split ? Hwf'' Hc_in_f Hconflict Hno_dec
  ]; try subst m''; try subst f'.
  (* t_unit *)
  - unfold Conflicting in Hconflict. inversion Hentails as
    [
      f' m'' Hcons Hno_dec Hf Hm |
      f' m'' n l_decide Hcons Hno_dec Hentails' Hf Hm
    ]; clear Htrans; clear Hwf; clear Hwf'; subst f'; try subst m''; subst m'.
    + apply e_intro.
      * intros m' Hmodel. simp m_eval. rewrite (Hcons _ Hmodel). 
        destruct (l_eval m' l_unit) as [[|]|] eqn:Hl.
        -- reflexivity.
        -- exfalso. assert (contra: c_eval m' (l_remove c_unit l_unit) = Some false).
          ++ apply (m_eval_transfer_c _ m).
            ** now apply Hcons.
            ** assumption.
          ++ apply c_eval_remove_false_l in contra.
            ** rewrite f_eval_true_iff in Hmodel. apply Hmodel in Hc_in_f. congruence.
            ** assumption.
        -- exfalso. assert (contra: c_eval m' (l_remove c_unit l_unit) = Some false).
          ++ apply (m_eval_transfer_c _ m).
            ** now apply Hcons.
            ** assumption.
          ++ apply c_eval_remove_none_l in contra.
            ** rewrite f_eval_true_iff in Hmodel. apply Hmodel in Hc_in_f. congruence.
            ** assumption.
            ** assumption.
      * unfold NoDecisions. unfold not. intros [l [contra|Hin]].
        -- discriminate.
        -- apply Hno_dec. now exists l.
    + admit.
  (* t_decide *)
  - rewrite <- app_nil_l. apply e_step.
    + intros. reflexivity.
    + unfold NoDecisions. unfold not. intros. now destruct H.
    + assumption.
  (* t_backtrack *)
  - admit.
Admitted.

Lemma derivation_entails: forall (m m': PA) (f: CNF) (Hwf: WellFormed m f) (Hwf': WellFormed m' f),
  state m f Hwf ==>* state m' f Hwf' -> Entails f m -> Entails f m'.
Proof.
  intros m m' f Hwf Hwf' H. apply clos_rt_rtn1_iff in H. 
  remember (state m f Hwf) as s eqn:Heqs.
  remember (state m' f Hwf') as s' eqn:Heqs'.
  generalize dependent m. generalize dependent m'.
  induction H.
  - intros. congruence.
  - intros. subst s; subst z. destruct y.
    + inversion H.
    + apply trans_same_formula in H as Heq. subst f0. apply trans_entails in H.
      * assumption.
      * now apply IHclos_refl_trans_n1 with (Hwf':= Hwf0) (Hwf:=Hwf).
Qed.
