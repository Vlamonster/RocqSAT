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

Lemma no_decisions_tail': forall (m m' n n': PA) (l: Lit),
  NoDecisions n -> NoDecisions n' -> m ++d l ++a n = m' ++a n' -> exists (n'': PA), n'' ++a n' = n.
Proof.
  intros. generalize dependent n. induction n'.
  - intros. exists n. reflexivity.
  - intros. destruct a. destruct a.
    + exfalso. apply H0. exists l0. now left.
    + destruct n.
      * simpl in H1. injection H1. intros. discriminate.
      * destruct p. destruct a.
        -- exfalso. apply H. exists l1. now left.
        -- simpl in H1. injection H1. intros. subst l1.
           assert (exists n'': PA, n'' ++a n' = n).
          ++ apply IHn'.
            ** unfold NoDecisions. unfold not. intros. apply H0. destruct H3. exists x. now right.
            ** unfold NoDecisions. unfold not. intros. apply H. destruct H3. exists x. now right.
            ** assumption.
          ++ destruct H3. exists x. simpl. now f_equal.
Qed.

Lemma entails_clip_aux: forall (m n: PA) (f: CNF) (l: Lit),
  Entails f (m ++d l ++a n) -> 
  WellFormed (m ++d l ++a n) f ->
  NoDecisions n ->
  0 < length n -> 
  exists (n': PA), 
    Entails f (m ++d l ++a n') /\
    WellFormed (m ++d l ++a n') f /\
    NoDecisions n' /\
    (forall (m': PA), 
      f_eval m' f = Some true /\
      m_eval m' m = Some true /\
      l_eval m' l = Some true /\
      m_eval m' n' = Some true -> f_eval (m' ++a m ++d l ++a n) f = Some true) /\
    length n' < length n.
Proof.
  intros. inversion H.
  - exfalso. apply H4. intros. exists l. apply in_or_app. right. now left.
  - exists []. simpl. assert (n0 = n) by now apply no_decisions_tail in H3. subst n0. split.
    + rewrite <- app_nil_l. apply e_decide.
      * intros. reflexivity.
      * unfold NoDecisions. unfold not. intros. destruct H8. contradiction.
      * apply app_inv_head in H3. now injection H3 as -> ->.
    + split.
      * now apply wf_app__wf in H0.
      * split.
        -- unfold NoDecisions. unfold not. intros. destruct H8. contradiction.
        -- split.
          ++ intros. apply app_inv_head in H3. injection H3 as -> ->.
             rewrite app_comm_cons. rewrite app_assoc.
             apply f_eval_true_extend.
            ** intuition.
            ** apply m_eval_true_iff. intros. apply in_app_or in H3.
               destruct H3.
              --- assert (m_eval m' n = Some true) by intuition.
                  rewrite m_eval_true_iff in H9. now apply (H9 _ a).
              --- destruct H3.
                +++ injection H3 as <- <-. intuition.
                +++ assert (m_eval m' m = Some true) by intuition.
                    rewrite m_eval_true_iff in H9. now apply (H9 _ a).
          ++ assumption.
  - assert (exists (n': PA), n' ++p l0 ++a n0 = n).
    + symmetry in H3. assert (m0 ++p l0 ++a n0 = m0 ++a ([] ++p l0 ++a n0)).
      * now rewrite <- app_assoc.
      * rewrite H9 in H3. apply no_decisions_tail' in H3.
        -- destruct H3. rewrite <- app_assoc in H3. simpl in H3. now exists x.
        -- assumption.
        -- unfold NoDecisions. unfold not. intros. destruct H10.
           apply in_app_or in H10. destruct H10.
          ++ apply H6. now exists x.
          ++ destruct H10.
            ** discriminate.
            ** contradiction.
    + destruct H9 as [n' Heq]. exists n'. rewrite <- Heq in H3.
      rewrite <- app_assoc in H3. rewrite <- app_comm_cons in H3.
      apply app_inv_head in H3. injection H3. intros. split.
      * congruence.
      * split.
        -- rewrite <- Heq in H0. rewrite <- app_assoc in H0. simpl in H0.
           apply wf_app__wf in H0. now apply wf_cons__wf in H0.
        -- split.
          ++ rewrite <- Heq in H1. unfold NoDecisions. unfold not. intros. apply H1.
             destruct H10. exists x. apply in_or_app. right. now right.
          ++ split.
            ** intros m' [Hmodel_f [Hmodel_m [Hmodel_l Hmodel_n']]].
               assert (f_eval (m' ++a m ++d l ++a n') f = Some true).
              --- rewrite app_comm_cons. rewrite app_assoc. apply f_eval_true_extend.
                +++ assumption.
                +++ apply m_eval_true_iff. intros. apply in_app_or in H10. destruct H10.
                  *** rewrite m_eval_true_iff in Hmodel_n'. now apply (Hmodel_n' _ a).
                  *** destruct H10.
                    ---- now injection H10 as <- <-.
                    ---- rewrite m_eval_true_iff in Hmodel_m. now apply (Hmodel_m _ a).
              --- apply H4 in H10. repeat rewrite app_comm_cons in H10. rewrite app_assoc in H10.
                  rewrite <- app_comm_cons in H10. rewrite <- H3 in H10. simpl in H10.
                  rewrite <- Heq. rewrite <- app_assoc. simpl.
                  assert (m' ++a m ++d l ++a n' ++p l0 ++a n0 = m' ++a (m ++d l ++a n') ++p l0 ++a n0).
                +++ now rewrite <- app_assoc.
                +++ rewrite H11. rewrite <- H9. apply f_eval_true_extend.
                  *** assumption.
                  *** apply H5. split.
                    ---- assumption.
                    ---- split.
                      ++++ rewrite <- Heq in H0. rewrite <- app_assoc in H0. simpl in H0.
                           rewrite <- H9 in H0. apply wf_app__wf in H0. apply m_eval_head_refl.
                        **** apply (nodup_cons__undef _ _ prop). apply H0.
                        **** apply m_eval_nodup_refl. apply wf_cons__wf in H0. apply H0.
                      ++++ simp l_eval. rewrite self_neqb_neg. now rewrite eqb_refl.
            ** rewrite <- Heq. rewrite length_app. simpl. lia.
Qed.

Lemma entails_clip_aux': forall (k: nat) (m n: PA) (f: CNF) (l: Lit),
  length n < k ->
  WellFormed (m ++d l ++a n) f ->
  NoDecisions n ->
  Entails f (m ++d l ++a n) -> 
  Entails f (m ++d l) /\
  (forall (m': PA),
    f_eval m' f = Some true /\
    m_eval m' m = Some true /\
    l_eval m' l = Some true -> exists (m'': PA), f_eval (m'' ++a m ++d l ++a n) f = Some true).
Proof.
  induction k.
  - intros. lia.
  - intros. destruct n.
    + split.
      * now simpl in H2.
      * intros m' [Hmodel_f [Hmodel_m Hmodel_l]]. simpl.
        exists m'. rewrite app_comm_cons. apply f_eval_true_extend.
        -- assumption.
        -- apply m_eval_true_iff. intros. destruct H3.
          ++ now injection H3 as <- <-.
          ++ rewrite m_eval_true_iff in Hmodel_m. now apply (Hmodel_m _ a).
    + destruct p. destruct a.
      * exfalso. apply H1. exists l0. now left.
      * apply entails_clip_aux in H2.
        -- destruct H2. destruct H2. destruct H3. destruct H4. destruct H5. assert (length x < k) by lia.
           apply (IHk m _ f l) in H7.
          ++ destruct H7. split.
            ** assumption.
            ** intros. assert (exists (m'': PA), f_eval (m'' ++a m ++d l ++a x) f = Some true).
              --- now apply (H8 m').
              --- destruct H10 as [m'' H10]. 
                  assert (f_eval (m'' ++a m ++d l ++a x ++a m ++d l ++a (n ++p l0)) f = Some true).
                +++ apply H5.
                  *** repeat split.
                    ---- assumption.
                    ---- admit.
                    ---- admit.
                    ---- admit.
                +++ now exists (m'' ++a m ++d l ++a x).
          ++ assumption.
          ++ assumption.
          ++ assumption.
        -- assumption.
        -- assumption.
        -- simpl. lia.
Admitted.

Lemma entails_clip: forall (m n: PA) (f: CNF) (l: Lit),
  WellFormed (m ++d l ++a n) f ->
  NoDecisions n ->
  Entails f (m ++d l ++a n) -> 
  Entails f (m ++d l) /\
  (forall (m': PA),
    f_eval m' f = Some true /\
    m_eval m' m = Some true /\
    l_eval m' l = Some true -> exists (m'': PA), f_eval (m'' ++a m ++d l ++a n) f = Some true).
Proof.
  intros. apply (entails_clip_aux' (S (length n))).
  - lia.
  - assumption.
  - assumption.
  - assumption.
Qed.

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
  - subst m. apply entails_clip in Hentails as [Hentails Hcons].
    + inversion Hentails as
      [
        f' m'' Hcons' Hno_dec' Hf Hm |
        f' m'' n l_decide Hcons' Hno_dec' Hentails' Hf Hm |
        f' m'' n l_irrel Hirrel Hcons' Hentails' Hf Hm
      ]; clear Htrans; clear Hwf; clear Hwf'; subst f'; try subst m''; subst m'.
      * exfalso. apply Hno_dec'. exists l_split. now left.
      * destruct n.
        -- simpl in Hm. injection Hm as -> ->. clear Hcons'. clear Hno_dec'.
           inversion Hentails'.
          ++ subst f0; subst n. apply e_intro.
            ** intros. destruct (l_eval m l_split) as [[|]|] eqn:Hl.
              --- exfalso. assert (exists (m': PA), f_eval (m' ++a m_split ++d l_split ++a n_split) f = Some true).
                +++ apply (Hcons m). split.
                  *** assumption.
                  *** split.
                    ---- now apply H.
                    ---- assumption.
                +++ assert (f_eval (m_split ++d l_split ++a n_split) f = Some false).
                  *** apply f_eval_false_iff. now exists c_conflict.
                  *** destruct H2 as [m' H2]. apply (f_eval_false_extend _ m') in H3.
                      rewrite <- app_assoc in H3. simpl in H3. congruence.
              --- simp m_eval. rewrite (H m H1). apply l_eval_neg_some_iff in Hl. now rewrite Hl.
              --- exfalso. assert (exists (m': PA), f_eval (m' ++a m_split ++d l_split ++a n_split) f = Some true).
                +++ apply (Hcons (m ++p l_split)). split.
                  *** now apply f_eval_extend_undef.
                  *** split.
                    ---- apply H. now apply f_eval_extend_undef.
                    ---- simp l_eval. rewrite self_neqb_neg. now rewrite eqb_refl.
                +++ assert (f_eval (m_split ++d l_split ++a n_split) f = Some false).
                  *** apply f_eval_false_iff. now exists c_conflict.
                  *** destruct H2 as [m' H2]. apply (f_eval_false_extend _ m') in H3.
                      rewrite <- app_assoc in H3. simpl in H3. congruence.
            ** unfold NoDecisions. unfold not. intros. destruct H1. destruct H1.
              --- discriminate.
              --- apply H0. now exists x.
          ++ subst f0. rewrite app_comm_cons. apply e_decide.
            ** intros m' [Hmodel_f [Hmodel_m Hmodel_l]]. destruct (l_eval m' l_split) as [[|]|] eqn:Hl.
              --- assert (exists (m'': PA), f_eval (m'' ++a m_split ++d l_split ++a n_split) f = Some true).
                +++ apply (Hcons m'). split.
                  *** intuition.
                  *** split.
                    ---- rewrite <- H3. apply m_eval_true_iff. intros.
                         apply in_app_or in H2. destruct H2.
                      ++++ assert (Hmodel_n: m_eval m' n = Some true).
                        **** now apply H.
                        **** rewrite m_eval_true_iff in Hmodel_n. now apply (Hmodel_n _ a).
                      ++++ destruct H2.
                        **** now injection H2 as <- <-.
                        **** rewrite m_eval_true_iff in Hmodel_m. now apply (Hmodel_m _ a).
                    ---- assumption.
                +++ assert (f_eval (m_split ++d l_split ++a n_split) f = Some false).
                  *** apply f_eval_false_iff. now exists c_conflict.
                  *** destruct H2 as [m'' H2]. apply (f_eval_false_extend _ m'') in H4.
                      rewrite <- app_assoc in H4. simpl in H4. congruence.
              --- simp m_eval. assert (Hmodel_n: m_eval m' n = Some true).
                +++ now apply H.
                +++ rewrite Hmodel_n. apply l_eval_neg_some_iff in Hl. now rewrite Hl.
              --- assert (exists (m'': PA), f_eval (m'' ++a m_split ++d l_split ++a n_split) f = Some true).
                +++ apply (Hcons (m' ++p l_split)). split.
                  *** now apply f_eval_extend_undef.
                  *** split.
                    ---- rewrite <- H3. apply m_eval_true_iff. intros.
                         apply in_app_or in H2. destruct H2.
                      ++++ assert (Hmodel_n: m_eval (m' ++p l_split) n = Some true).
                        **** apply H. split.
                          ----- now apply f_eval_extend_undef.
                          ----- split.
                            +++++ now apply m_eval_extend_undef.
                            +++++ now apply l_eval_extend_undef.
                        **** rewrite m_eval_true_iff in Hmodel_n. now apply (Hmodel_n _ a).
                      ++++ destruct H2.
                        **** injection H2 as <- <-. now apply l_eval_extend_undef.
                        **** apply l_eval_extend_undef.
                          ----- congruence.
                          ----- rewrite m_eval_true_iff in Hmodel_m. now apply (Hmodel_m _ a).
                    ---- simp l_eval. rewrite self_neqb_neg. now rewrite eqb_refl.
                +++ assert (f_eval (m_split ++d l_split ++a n_split) f = Some false).
                  *** apply f_eval_false_iff. now exists c_conflict.
                  *** destruct H2 as [m'' H2]. apply (f_eval_false_extend _ m'') in H4.
                      rewrite <- app_assoc in H4. simpl in H4. congruence.
            ** unfold NoDecisions. unfold not. intros. destruct H2. destruct H2.
              --- discriminate.
              --- apply H0. now exists x.
            ** assumption.
          ++ subst f0. rewrite app_comm_cons. apply e_irrelevant.
            ** assumption.
            ** intros m' [Hmodel_f [Hmodel_m Hmodel_l]]. destruct (l_eval m' l_split) as [[|]|] eqn:Hl.
              --- assert (exists (m'': PA), f_eval (m'' ++a m_split ++d l_split ++a n_split) f = Some true).
                +++ apply (Hcons m'). split.
                  *** assumption.
                  *** split.
                    ---- rewrite <- H4. apply m_eval_true_iff. intros.
                         apply in_app_or in H3. destruct H3.
                      ++++ assert (Hmodel_n: m_eval m' n = Some true).
                        **** now apply H0.
                        **** rewrite m_eval_true_iff in Hmodel_n. now apply (Hmodel_n _ a).
                      ++++ destruct H3.
                        **** now injection H3 as <- <-.
                        **** rewrite m_eval_true_iff in Hmodel_m. now apply (Hmodel_m _ a).
                    ---- assumption.
                +++ assert (f_eval (m_split ++d l_split ++a n_split) f = Some false).
                  *** apply f_eval_false_iff. now exists c_conflict.
                  *** destruct H3 as [m'' H3]. apply (f_eval_false_extend _ m'') in H5. 
                      rewrite <- app_assoc in H5. simpl in H5. congruence.
              --- assert (Hmodel_n: m_eval m' n = Some true).
                +++ now apply H0.
                +++ simp m_eval. rewrite Hmodel_n. rewrite l_eval_neg_some_iff in Hl. now rewrite Hl.
              --- assert (exists (m'': PA), f_eval (m'' ++a m_split ++d l_split ++a n_split) f = Some true).
                +++ apply (Hcons (m' ++p l_split)). split.
                  *** now apply f_eval_extend_undef.
                  *** split.
                    ---- apply m_eval_extend_undef.
                      ++++ congruence.
                      ++++ rewrite <- H4. apply m_eval_true_iff. intros.
                           apply in_app_or in H3. destruct H3.
                        **** assert (Hmodel_n: m_eval m' n = Some true).
                          ----- now apply H0.
                          ----- rewrite m_eval_true_iff in Hmodel_n. now apply (Hmodel_n _ a).
                        **** destruct H3.
                          ----- now injection H3 as <- <-.
                          ----- rewrite m_eval_true_iff in Hmodel_m. now apply (Hmodel_m _ a).
                    ---- simp l_eval. rewrite self_neqb_neg. now rewrite eqb_refl.
                +++ assert (f_eval (m_split ++d l_split ++a n_split) f = Some false).
                  *** apply f_eval_false_iff. now exists c_conflict.
                  *** destruct H3 as [m'' H3]. apply (f_eval_false_extend _ m'') in H5.
                      rewrite <- app_assoc in H5. simpl in H5. congruence.
            ** unfold NoDecisions. unfold not. intros. destruct H3. destruct H3.
              --- discriminate.
              --- apply H1. now exists x.
            ** assumption.
        -- destruct p. destruct a.
          ++ exfalso. apply Hno_dec'. exists l. now left.
          ++ simpl in Hm. injection Hm. intros. discriminate.
      * destruct n.
        -- simpl in H. injection H. intros. discriminate.
        -- simpl in H. injection H. intros. destruct p. destruct a.
          ++ exfalso. apply Hentails'. exists l. now left.
          ++ discriminate.
    + assumption.
    + assumption.
Qed.

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
