From Equations Require Import Equations.
From Stdlib Require Import Arith List Relations Lia.
Import ListNotations.
From RocqSAT Require Import Lit Neg Clause CNF Evaluation WellFormed Trans Normalization.

Inductive Entails: CNF -> PA -> Prop :=
| e_intro (f: CNF) (n: PA):
  (forall (m: PA), 
    f_eval m f = Some true -> m_eval m n = Some true) ->
  NoDecisions n ->
  Entails f n
| e_decide (f: CNF) (m n: PA) (l: Lit):
  (forall (m': PA), 
    f_eval m' f = Some true /\
    m_eval m' m = Some true /\
    l_eval m' l = Some true -> m_eval m' n = Some true) ->
  NoDecisions n ->
  Entails f m ->
  Entails f (m ++d l ++a n)
| e_irrelevant (f: CNF) (m n: PA) (l: Lit):
  (forall (m': PA),
    f_eval m' f = Some true -> f_eval (m' ++p l) f = Some true) ->
  (forall (m': PA), 
    f_eval m' f = Some true /\
    m_eval m' m = Some true /\
    l_eval m' l = Some true -> m_eval m' n = Some true) ->
  NoDecisions n ->
  Entails f m ->
  Entails f (m ++p l ++a n).

Lemma m_eval_nodup_refl: forall (m: PA),
  NoDuplicates m -> m_eval m m = Some true.
Proof.
  induction m as [|[l a] m IH].
  - intros. reflexivity.
  - intros. simp m_eval. simp l_eval. rewrite eqb_refl. rewrite self_neqb_neg. simpl.
    apply m_eval_extend_undef.
    + now apply nodup_cons__undef in H.
    + apply IH. now apply nodup_cons__nodup in H.
Qed.

Lemma entailment: forall (m m': PA) (f: CNF),
  Entails f m -> WellFormed m f -> NoDecisions m -> f_eval m' f = Some true -> f_eval (m' ++a m) f = Some true.
Proof.
  intros m m' f Hentails Hwf Hno_dec Hmodel. induction Hentails.
  - apply f_eval_true_extend.
    + assumption.
    + now apply H.
  - exfalso. apply Hno_dec. exists l. apply in_elt.
  - assert (f_eval (m' ++a m) f = Some true).
    + apply IHHentails.
      * apply wf_app__wf in Hwf. now apply wf_cons__wf in Hwf.
      * unfold NoDecisions. unfold not. intros [l' Hin']. apply Hno_dec.
        exists l'. apply in_or_app. right. now right. 
      * assumption.
    + apply H in H2. assert (m_eval (m' ++a m ++p l) n = Some true).
      * apply H0. split.
        -- assumption.
        -- split.
          ++ apply m_eval_head_refl.
            ** apply (nodup_cons__undef _ _ prop). apply (nodup_app__nodup _ n). apply Hwf.
            ** apply m_eval_nodup_refl. apply (nodup_cons__nodup _ l prop).
               apply (nodup_app__nodup _ n). apply Hwf.
          ++ simp l_eval. rewrite self_neqb_neg. now rewrite eqb_refl.
      * rewrite <- app_assoc. simpl. now apply f_eval_true_extend.
Qed.

Lemma no_decisions_tail: forall (m m' n n': PA) (l l': Lit),
  NoDecisions n -> NoDecisions n' -> m ++d l ++a n = m' ++d l' ++a n' -> n = n'.
Proof. 
  intros. generalize dependent n'. induction n.
  - intros. simpl in H1. destruct n'.
    + reflexivity.
    + exfalso. injection H1. intros. destruct p. injection H3 as <- <-.
      apply H0. exists l. now left.
  - intros. destruct n'.
    + exfalso. simpl in H1. injection H1. intros. destruct a. injection H3 as -> ->.
      apply H. exists l'. now left.
    + injection H1. intros. f_equal.
      * assumption.
      * apply IHn.
        -- unfold NoDecisions. unfold not. intros. apply H. destruct H4. exists x. now right.
        -- unfold NoDecisions. unfold not. intros. apply H0. destruct H4. exists x. now right.
        -- assumption.
Qed.

Lemma entails_clip: forall (m n: PA) (f: CNF) (l: Lit),
  Entails f (m ++d l ++a n) -> 
  NoDecisions n ->
  0 < length n -> 
  exists (n': PA), 
    Entails f (m ++d l ++a n') /\ 
    (forall (m': PA), 
      f_eval m' f = Some true /\
      m_eval m' m = Some true /\
      l_eval m' l = Some true /\
      m_eval m' n' = Some true -> f_eval (m' ++a m ++d l ++a n) f = Some true) /\
    length n' < length n.
Proof.
  intros. inversion H.
  - exfalso. apply H3. intros. exists l. apply in_or_app. right. now left.
  - exists []. simpl. assert (n0 = n) by now apply no_decisions_tail in H2. subst n0. split.
    + rewrite <- app_nil_l. apply e_decide.
      * intros. reflexivity.
      * unfold NoDecisions. unfold not. intros. destruct H7. contradiction.
      * apply app_inv_head in H2. now injection H2 as -> ->.
    + split.
      * intros. apply app_inv_head in H2. injection H2 as -> ->.
        rewrite app_comm_cons. rewrite app_assoc.
        apply f_eval_true_extend.
        -- intuition.
        -- apply m_eval_true_iff. intros. apply in_app_or in H2.
           destruct H2.
          ++ assert (m_eval m' n = Some true) by intuition.
             rewrite m_eval_true_iff in H8. now apply (H8 _ a).
          ++ destruct H2.
            ** injection H2 as <- <-. intuition.
            ** assert (m_eval m' m = Some true) by intuition.
               rewrite m_eval_true_iff in H8. now apply (H8 _ a).
      * assumption.
  - assert (exists (n': PA), n' ++p l0 ++a n0 = n). admit.
    destruct H8 as [n' Heq]. exists n'. rewrite <- Heq in H2.
    rewrite <- app_assoc in H2. rewrite <- app_comm_cons in H2.
    apply app_inv_head in H2. injection H2. intros. split.
    + congruence.
    + split.
      * intros. admit.
      * rewrite <- Heq. rewrite length_app. simpl. lia.
Admitted.

Lemma bla': forall (m n: PA) (f: CNF) (l: Lit),
  Entails f (m ++d l ++a n) -> 
  Entails f (m ++d l) /\
  (forall (m': PA), 
    f_eval m' f = Some true /\
    m_eval m' m = Some true /\
    l_eval m' l = Some true -> f_eval (m' ++a m ++d l ++a n) f = Some true).
Proof. Admitted.

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
      f' m'' n l_decide Hcons Hno_dec Hentails' Hf Hm |
      f' m'' n l_irrel Hirrel Hcons Hno_dec Hentails' Hf Hm
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
    + rewrite app_comm_cons. apply e_decide.
      * intros m' [Hmodel_f [Hmodel_m'' Hmodel_l]].
        assert (Hmodel_n: m_eval m' n = Some true).
        -- now apply Hcons.
        -- assert (Hmodel_m: m_eval m' (m'' ++d l_decide ++a n) = Some true).
          ++ apply m_eval_true_iff. intros l a Hin. apply in_app_or in Hin as [Hin|Hin].
            ** rewrite m_eval_true_iff in Hmodel_n. now apply (Hmodel_n _ a).
            ** destruct Hin as [Hin|Hin].
              --- congruence.
              --- rewrite m_eval_true_iff in Hmodel_m''. now apply (Hmodel_m'' _ a).
          ++ rewrite Hm in Hmodel_m. simp m_eval. rewrite Hmodel_n.
             destruct (l_eval m' l_unit) as [[|]|] eqn:Hl.
            ** reflexivity.
            ** exfalso. assert (contra: c_eval m' (l_remove c_unit l_unit) = Some false).
              --- now apply (m_eval_transfer_c _ m).
              --- apply c_eval_remove_false_l in contra.
                +++ rewrite f_eval_true_iff in Hmodel_f. apply Hmodel_f in Hc_in_f. congruence.
                +++ assumption.
            ** exfalso. assert (contra: c_eval m' (l_remove c_unit l_unit) = Some false).
              --- now apply (m_eval_transfer_c _ m).
              --- apply c_eval_remove_none_l in contra.
                +++ rewrite f_eval_true_iff in Hmodel_f. apply Hmodel_f in Hc_in_f. congruence.
                +++ assumption.
                +++ assumption.
      * unfold NoDecisions. unfold not. intros [l [contra|Hin]].
        -- discriminate.
        -- apply Hno_dec. now exists l.
      * assumption.
    + rewrite app_comm_cons. apply e_irrelevant.
      * assumption.
      * intros m' [Hmodel_f [Hmodel_m'' Hmodel_l]].
        assert (Hmodel_n: m_eval m' n = Some true).
        -- now apply Hcons.
        -- assert (Hmodel_m: m_eval m' (m'' ++p l_irrel ++a n) = Some true).
          ++ apply m_eval_true_iff. intros l a Hin. apply in_app_or in Hin as [Hin|Hin].
            ** rewrite m_eval_true_iff in Hmodel_n. now apply (Hmodel_n _ a).
            ** destruct Hin as [Hin|Hin].
              --- congruence.
              --- rewrite m_eval_true_iff in Hmodel_m''. now apply (Hmodel_m'' _ a).
          ++ rewrite Hm in Hmodel_m. simp m_eval. rewrite Hmodel_n.
             destruct (l_eval m' l_unit) as [[|]|] eqn:Hl.
            ** reflexivity.
            ** exfalso. assert (contra: c_eval m' (l_remove c_unit l_unit) = Some false).
              --- now apply (m_eval_transfer_c _ m).
              --- apply c_eval_remove_false_l in contra.
                +++ rewrite f_eval_true_iff in Hmodel_f. apply Hmodel_f in Hc_in_f. congruence.
                +++ assumption.
            ** exfalso. assert (contra: c_eval m' (l_remove c_unit l_unit) = Some false).
              --- now apply (m_eval_transfer_c _ m).
              --- apply c_eval_remove_none_l in contra.
                +++ rewrite f_eval_true_iff in Hmodel_f. apply Hmodel_f in Hc_in_f. congruence.
                +++ assumption.
                +++ assumption.
      * unfold NoDecisions. unfold not. intros [l [Hin|Hin]].
        -- discriminate.
        -- apply Hno_dec. now exists l.
      * assumption.
  (* t_decide *)
  - rewrite <- app_nil_l. apply e_decide.
    + intros. reflexivity.
    + unfold NoDecisions. unfold not. intros. now destruct H.
    + assumption.
  (* t_backtrack *)
  - unfold Conflicting in Hconflict. inversion Hentails as
    [
      f' m'' Hcons Hno_dec' Hf Hm |
      f' m'' n l_decide Hcons Hno_dec' Hentails' Hf Hm |
      f' m'' n l_irrel Hirrel Hcons Hentails' Hf Hm
    ]; clear Htrans; clear Hwf; clear Hwf'; subst f'; try subst m''; subst m'.
    + apply e_intro.
      * intros m' Hmodel_f. assert (Hmodel_m: m_eval m' m = Some true).
        -- now apply Hcons.
        -- assert (Hmodel_m_split: m_eval m' m_split = Some true).
          ++ rewrite m_eval_true_iff in Hmodel_m. apply m_eval_true_iff.
             intros l a Hin. apply (Hmodel_m _ a). rewrite <- H. apply in_or_app.
             right. now right.
          ++ simp m_eval. rewrite Hmodel_m_split. 
             destruct (l_eval m' (¬l_split)) as [[|]|] eqn:Hl.
            ** reflexivity.
            ** exfalso. apply (m_eval_transfer_c _ _ c_conflict) in Hmodel_m.
              --- rewrite f_eval_true_iff in Hmodel_f. apply Hmodel_f in Hc_in_f. congruence.
              --- congruence.
            ** exfalso. rewrite l_eval_neg_none_iff in Hl. rewrite involutive in Hl.
               assert (contra: l_eval m' l_split = Some true).
              --- rewrite m_eval_true_iff in Hmodel_m. apply (Hmodel_m _ dec).
                  rewrite <- H. apply in_or_app. right. now left.
              --- congruence.
      * unfold NoDecisions. unfold not. intros [l [contra|Hin]].
        -- discriminate.
        -- apply Hno_dec'. exists l. rewrite <- H. apply in_or_app. right. now right.
    + assert (n_split = n).
      * apply (no_decisions_tail m_split m'' _ _ l_split l_decide); congruence.
      * subst n. rewrite <- Hm in H. apply app_inv_head in H. injection H as <-. subst m''.
        clear Hno_dec. clear Hno_dec'. clear Hentails.
        inversion Hentails' as
        [
          f' m'' Hcons' Hno_dec Hf Hm' |
          f' m'' n l_decide Hcons' Hno_dec Hentails Hf Hm' |
          f' m'' n l_irrel Hirrel Hcons' Hno_dec Hentails Hf Hm'
        ]; try subst f'; try subst m''.
        -- apply e_intro.
          ++ intros m' Hmodel_f. simp m_eval.
             destruct (l_eval m' l_split) as [[|]|] eqn:Hl.
            ** exfalso. assert (Hmodel_m_split: m_eval m' m_split = Some true).
              --- now apply Hcons'.
              --- assert (Hmodel_n_split: m_eval m' n_split = Some true).
                +++ now apply Hcons.
                +++ assert (Hmodel_m: m_eval m' m = Some true).
                  *** apply m_eval_true_iff. intros. rewrite <- Hm in H. apply in_app_or in H.
                      destruct H.
                    ---- rewrite m_eval_true_iff in Hmodel_n_split. now apply (Hmodel_n_split _ a).
                    ---- destruct H.
                      ++++ congruence.
                      ++++ rewrite m_eval_true_iff in Hmodel_m_split. now apply (Hmodel_m_split _ a).
                  *** apply (m_eval_transfer_c _ _ c_conflict) in Hmodel_m.
                    ---- rewrite f_eval_true_iff in Hmodel_f. apply Hmodel_f in Hc_in_f. congruence.
                    ---- congruence.
            ** apply l_eval_neg_some_iff in Hl. rewrite Hl. now rewrite (Hcons' _ Hmodel_f).
            ** exfalso. assert (Hmodel_f': f_eval (m' ++p l_split) f = Some true).
              --- now apply f_eval_extend_undef.
              --- assert (Hmodel_m_split: m_eval (m' ++p l_split) m_split = Some true).
                +++ now apply Hcons'.
                +++ assert (Hmodel_l_split: l_eval (m' ++p l_split) l_split = Some true).
                  *** simp l_eval. rewrite eqb_refl. now rewrite self_neqb_neg.
                  *** assert (Hmodel_n_split: m_eval (m' ++p l_split) n_split = Some true).
                    ---- now apply Hcons.
                    ---- assert (Hmodel_m: m_eval (m' ++p l_split) m = Some true).
                      ++++ apply m_eval_true_iff. intros. rewrite <- Hm in H. apply in_app_or in H.
                           destruct H.
                        **** rewrite m_eval_true_iff in Hmodel_n_split. now apply (Hmodel_n_split _ a).
                        **** destruct H.
                          ----- congruence.
                          ----- rewrite m_eval_true_iff in Hmodel_m_split. now apply (Hmodel_m_split _ a).
                      ++++ apply (m_eval_transfer_c _ _ c_conflict) in Hmodel_m.
                        **** rewrite f_eval_true_iff in Hmodel_f'. apply Hmodel_f' in Hc_in_f. congruence.
                        **** congruence.
          ++ unfold NoDecisions. unfold not. intros [l [contra|Hin]].
            ** discriminate.
            ** apply Hno_dec. now exists l.
        -- rewrite app_comm_cons. apply e_decide.
          ++ intros m' [Hmodel_f [Hmodel_m'' Hmodel_l]].
             assert (Hmodel_n: m_eval m' n = Some true).
            ** now apply Hcons'.
            ** assert (Hmodel_m_split: m_eval m' m_split = Some true).
              --- apply m_eval_true_iff. intros. rewrite <- Hm' in H. apply in_app_or in H.
                  destruct H.
                +++ rewrite m_eval_true_iff in Hmodel_n. now apply (Hmodel_n _ a).
                +++ destruct H.
                  *** congruence.
                  *** rewrite m_eval_true_iff in Hmodel_m''. now apply (Hmodel_m'' _ a).
              --- destruct (l_eval m' l_split) as [[|]|] eqn:Hl.
                +++ exfalso. assert (Hmodel_n_split: m_eval m' n_split = Some true).
                  *** now apply Hcons.
                  *** assert (Hmodel_m: m_eval m' m = Some true).
                    ---- apply m_eval_true_iff. intros. rewrite <- Hm in H. apply in_app_or in H.
                         destruct H.
                      ++++ rewrite m_eval_true_iff in Hmodel_n_split. now apply (Hmodel_n_split _ a).
                      ++++ destruct H.
                        **** congruence.
                        **** rewrite m_eval_true_iff in Hmodel_m_split. now apply (Hmodel_m_split _ a).
                    ---- apply (m_eval_transfer_c _ _ c_conflict) in Hmodel_m.
                      ++++ rewrite f_eval_true_iff in Hmodel_f. apply Hmodel_f in Hc_in_f. congruence.
                      ++++ congruence.
                +++ apply l_eval_neg_some_iff in Hl. simp m_eval. rewrite Hl. now rewrite Hmodel_n.
                +++ exfalso. 
                    assert (Hmodel_f': f_eval (m' ++p l_split) f = Some true) 
                      by now apply f_eval_extend_undef.
                    assert (Hmodel_m_split': m_eval (m' ++p l_split) m_split = Some true) 
                      by now apply m_eval_extend_undef.
                    assert (Hmodel_l_split': l_eval (m' ++p l_split) l_split = Some true).
                  *** simp l_eval. rewrite eqb_refl. now rewrite self_neqb_neg.
                  *** assert (Hmodel_n_split': m_eval (m' ++p l_split) n_split = Some true).
                    ---- now apply Hcons.
                    ---- assert (Hmodel_m: m_eval (m' ++p l_split) m = Some true).
                      ++++ apply m_eval_true_iff. intros. rewrite <- Hm in H. apply in_app_or in H.
                           destruct H.
                        **** rewrite m_eval_true_iff in Hmodel_n_split'. now apply (Hmodel_n_split' _ a).
                        **** destruct H.
                          ----- congruence.
                          ----- rewrite m_eval_true_iff in Hmodel_m_split'. now apply (Hmodel_m_split' _ a).
                      ++++ apply (m_eval_transfer_c _ _ c_conflict) in Hmodel_m.
                        **** rewrite f_eval_true_iff in Hmodel_f'. apply Hmodel_f' in Hc_in_f. congruence.
                        **** congruence.
          ++ unfold NoDecisions. unfold not. intros [l [contra|Hin]].
            ** discriminate.
            ** apply Hno_dec. now exists l.
          ++ assumption.
        -- rewrite app_comm_cons. apply e_irrelevant.
          ++ assumption.
          ++ intros m' [Hmodel_f [Hmodel_m'' Hmodel_l]].
             assert (Hmodel_n: m_eval m' n = Some true).
            ** now apply Hcons'.
            ** assert (Hmodel_m_split: m_eval m' m_split = Some true).
              --- apply m_eval_true_iff. intros. rewrite <- Hm' in H. apply in_app_or in H.
                  destruct H.
                +++ rewrite m_eval_true_iff in Hmodel_n. now apply (Hmodel_n _ a).
                +++ destruct H.
                  *** congruence.
                  *** rewrite m_eval_true_iff in Hmodel_m''. now apply (Hmodel_m'' _ a).
              --- destruct (l_eval m' l_split) as [[|]|] eqn:Hl.
                +++ exfalso. assert (Hmodel_n_split: m_eval m' n_split = Some true).
                  *** now apply Hcons.
                  *** assert (Hmodel_m: m_eval m' m = Some true).
                    ---- apply m_eval_true_iff. intros. rewrite <- Hm in H. apply in_app_or in H.
                         destruct H.
                      ++++ rewrite m_eval_true_iff in Hmodel_n_split. now apply (Hmodel_n_split _ a).
                      ++++ destruct H.
                        **** congruence.
                        **** rewrite m_eval_true_iff in Hmodel_m_split. now apply (Hmodel_m_split _ a).
                    ---- apply (m_eval_transfer_c _ _ c_conflict) in Hmodel_m.
                      ++++ rewrite f_eval_true_iff in Hmodel_f. apply Hmodel_f in Hc_in_f. congruence.
                      ++++ congruence.
                +++ apply l_eval_neg_some_iff in Hl. simp m_eval. rewrite Hl. now rewrite Hmodel_n.
                +++ exfalso. 
                    assert (Hmodel_f': f_eval (m' ++p l_split) f = Some true) 
                      by now apply f_eval_extend_undef.
                    assert (Hmodel_m_split': m_eval (m' ++p l_split) m_split = Some true) 
                      by now apply m_eval_extend_undef.
                    assert (Hmodel_l_split': l_eval (m' ++p l_split) l_split = Some true).
                  *** simp l_eval. rewrite eqb_refl. now rewrite self_neqb_neg.
                  *** assert (Hmodel_n_split': m_eval (m' ++p l_split) n_split = Some true).
                    ---- now apply Hcons.
                    ---- assert (Hmodel_m: m_eval (m' ++p l_split) m = Some true).
                      ++++ apply m_eval_true_iff. intros. rewrite <- Hm in H. apply in_app_or in H.
                           destruct H.
                        **** rewrite m_eval_true_iff in Hmodel_n_split'. now apply (Hmodel_n_split' _ a).
                        **** destruct H.
                          ----- congruence.
                          ----- rewrite m_eval_true_iff in Hmodel_m_split'. now apply (Hmodel_m_split' _ a).
                      ++++ apply (m_eval_transfer_c _ _ c_conflict) in Hmodel_m.
                        **** rewrite f_eval_true_iff in Hmodel_f'. apply Hmodel_f' in Hc_in_f. congruence.
                        **** congruence.
          ++ unfold NoDecisions. unfold not. intros [l [Hin|Hin]].
            ** discriminate.
            ** apply Hno_dec. now exists l. 
          ++ assumption.
    + rewrite <- H in Hentails. apply bla' in Hentails as [Hentails Hcons']. inversion Hentails.
      * exfalso. apply H1. exists l_split. now left.
      * assert (m0 = m_split). admit. subst m0. inversion H5.
        -- apply e_intro.
          ++ admit.
          ++ admit.
        -- admit.
        -- admit.
      * admit.
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
