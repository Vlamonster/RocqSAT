From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import Relations.
Import ListNotations.

From Equations Require Import Equations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import Trans.
From RocqSAT Require Import Inspect.
From RocqSAT Require Import WellFormed.

Definition Strategy (next: State -> option State): Prop :=
  (next fail = None) /\
  (forall (s: State), next s = None -> FinalB s) /\
  (forall (s s': State), next s = Some s' -> s ==>+ s').

Lemma strategy_trans: forall (f: CNF) (s s': State) (next: State -> option State) (Hstrat: Strategy next),
  next s = Some s' ->
  state [] f (initial_wf f) ==>* s ->
  state [] f (initial_wf f) ==>* s'.
Proof.
  intros f s s' next Hstrat ns H. eapply rt_trans.
  - apply H.
  - apply Hstrat in ns. now apply clos_t_clos_rt in ns.
Qed.

Definition find_conflict (m: PA) (f: CNF): option Clause :=
CNF.choose (CNF.filter (c_false m) f).

Lemma find_conflict_c_in_f: forall (m: PA) (f: CNF) (c: Clause), 
  find_conflict m f = Some c -> CNF.In c f.
Proof.
  intros m f c Hfind. unfold find_conflict in Hfind. apply CNF.choose_spec1 in Hfind.
  apply CNF.filter_spec in Hfind as [Hc_in_f _].
  - assumption.
  - intros c1 c2 Heq. unfold c_false. unfold c_eval.
    rewrite (Clause.c_equal_exists _ c1 c2 Heq). now rewrite (Clause.c_equal_forall _ c1 c2 Heq).
Qed.

Lemma find_conflict_conflicting: forall (m: PA) (f: CNF) (c: Clause), 
  find_conflict m f = Some c -> c_eval m c = Some false.
Proof.
  intros m f c Hfind. unfold find_conflict in Hfind. apply CNF.choose_spec1 in Hfind.
  apply CNF.filter_spec in Hfind as [_ Hc].
  - unfold c_false in Hc. destruct (c_eval m c) as [[|]|]; easy.
  - intros c1 c2 Heq. unfold c_false. unfold c_eval.
    rewrite (Clause.c_equal_exists _ c1 c2 Heq). now rewrite (Clause.c_equal_forall _ c1 c2 Heq).
Qed.

Lemma find_conflict_exists_iff: forall (m: PA) (f: CNF),
  (exists (c: Clause), find_conflict m f = Some c) <-> exists (c: Clause), CNF.In c f /\ c_eval m c = Some false.
Proof.
  intros m f. split.
  - intros [c Hfind]. exists c. split.
    + now apply find_conflict_c_in_f in Hfind.
    + now apply find_conflict_conflicting in Hfind.
  - intros [c [Hc_in_f Hc]]. unfold find_conflict.
    destruct (CNF.choose (CNF.filter (c_false m) f)) as [c'|] eqn:Hchoose.
    + now exists c'.
    + apply CNF.choose_spec2 in Hchoose. exfalso. apply (Hchoose c). apply CNF.filter_spec.
      * intros c1 c2 Heq. unfold c_false. unfold c_eval.
          rewrite (Clause.c_equal_exists _ c1 c2 Heq). now rewrite (Clause.c_equal_forall _ c1 c2 Heq).
      * split.
        -- assumption.
        -- unfold c_false. now rewrite Hc.
Qed.

Equations split_last_decision (m: PA): option (PA * Lit) :=
split_last_decision [] := None;
split_last_decision (m ++d l) := Some (m, l);
split_last_decision (m ++p l) := split_last_decision m.

Lemma split_decomp: forall (m m': PA) (l': Lit),
  split_last_decision m = Some (m', l') -> exists (n': PA), m = m' ++d l' ++a n' /\ NoDecisions n'.
Proof.
  unfold NoDecisions. unfold not. intros. funelim (split_last_decision m).
  - discriminate.
  - rewrite <- Heqcall in H. injection H as <- <-. exists []. intuition. now destruct H.
  - rewrite <- Heqcall in H0. destruct (H m' l' H0). destruct H1. rewrite H1. exists (x ++p l).
    intuition. apply H2. destruct H3. destruct H3.
    + discriminate.
    + now exists x0.
Qed.

Definition find_unit_l (m: PA) (c: Clause): option Lit :=
Clause.choose (Clause.filter (fun (l: Lit) => l_undef m l && c_false m (Clause.remove l c)) c).

Definition find_unit (m: PA) (f: CNF): option (Clause * Lit) :=
CNF.fold (fun (c: Clause) (r: option (Clause * Lit)) =>
  match r with
  | Some p => Some p
  | None   => option_map (pair c) (find_unit_l m c)
  end) f None.

Lemma find_unit_decomp: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  find_unit m f = Some (c, l) -> find_unit_l m c = Some l /\ CNF.In c f.
Proof.
  intros m f c l. unfold find_unit. apply CNF.MP.fold_rec_nodep.
  - discriminate.
  - intros c' r Hc'_in_f IH Hr. destruct r as [p|].
    + now apply IH.
    + destruct (find_unit_l m c') as [l'|] eqn:Hfind.
      * simpl in Hr. injection Hr as <- <-. now split.
      * discriminate.
Qed.

Lemma find_unit_undef: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  find_unit m f = Some (c, l) -> Undef m l.
Proof.
  intros m f c l Hfind. apply find_unit_decomp in Hfind as [Hfind _].
  unfold find_unit_l in Hfind. apply Clause.choose_spec1 in Hfind.
  apply Clause.filter_spec in Hfind as [_ Hl].
  - apply andb_true_iff in Hl as [Hundef _]. unfold Undef. unfold l_undef in Hundef.
    destruct (l_eval m l); easy.
  - now intros ? ? ->.
Qed.

Lemma find_unit_l_l_in_c: forall (m: PA) (c: Clause) (l: Lit),
  find_unit_l m c = Some l -> Clause.In l c.
Proof.
  intros m c l Hfind. unfold find_unit_l in Hfind. apply Clause.choose_spec1 in Hfind.
  apply Clause.filter_spec in Hfind as [Hl_in_c _].
  - assumption.
  - now intros ? ? ->.
Qed.

Lemma find_unit_l_in_c: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  find_unit m f = Some (c, l) -> Clause.In l c.
Proof.
  intros m f c l Hfind. apply find_unit_decomp in Hfind as [Hfind _].
  now apply find_unit_l_l_in_c in Hfind.
Qed.

Lemma find_unit_c_in_f: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  find_unit m f = Some (c, l) -> CNF.In c f.
Proof. intros m f c l Hfind. now apply find_unit_decomp in Hfind. Qed.

Lemma find_unit_bounded: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  find_unit m f = Some (c, l) -> l_in_f f l = true.
Proof.
  intros m f c l Hfind. apply CNF.l_in_f_true_iff. exists c. split.
  - left. now apply find_unit_l_in_c in Hfind.
  - now apply find_unit_c_in_f in Hfind.
Qed.

Definition find_undef_l (m: PA) (c: Clause): option Lit :=
Clause.choose (Clause.filter (l_undef m) c).

Lemma find_undef_l_in_c: forall (m: PA) (c: Clause) (l: Lit), 
  find_undef_l m c = Some l -> Clause.In l c.
Proof.
  intros m c l Hfind. unfold find_undef_l in Hfind. apply Clause.choose_spec1 in Hfind.
  apply Clause.filter_spec in Hfind as [Hl_in_c _].
  - assumption.
  - now intros ? ? ->.
Qed.

Lemma find_undef_l_undef: forall (m: PA) (c: Clause) (l: Lit), 
  find_undef_l m c = Some l -> Undef m l.
Proof.
  intros m c l Hfind. unfold find_undef_l in Hfind. apply Clause.choose_spec1 in Hfind.
  apply Clause.filter_spec in Hfind as [_ Hundef].
  - unfold Undef. unfold l_undef in Hundef. destruct (l_eval m l); easy.
  - now intros ? ? ->.
Qed.

Lemma find_undef_l_def: forall (m: PA) (c: Clause),
  find_undef_l m c = None -> exists (b: bool), c_eval m c = Some b.
Proof.
  intros m c Hfind. unfold find_undef_l in Hfind. apply Clause.choose_spec2 in Hfind.
  destruct (c_eval m c) as [b|] eqn:Hc.
  - now exists b.
  - apply c_eval_none_iff in Hc as [_ [l [Hl_in_c Hl]]]. exfalso. apply (Hfind l).
    apply Clause.filter_spec.
    + now intros ? ? ->.
    + split.
      * assumption.
      * unfold l_undef. now rewrite Hl.
Qed.

Lemma find_undef_l_exists : forall (m: PA) (c: Clause) (l: Lit),
  Clause.In l c -> Undef m l -> exists (l': Lit), find_undef_l m c = Some l'.
Proof.
  intros m c l Hl_in_c Hundef. unfold find_undef_l.
  destruct (Clause.choose (Clause.filter (l_undef m) c)) as [l'|] eqn:Hchoose.
  - now exists l'.
  - apply Clause.choose_spec2 in Hchoose. exfalso. apply (Hchoose l). apply Clause.filter_spec.
    + now intros ? ? ->.
    + split.
      * assumption.
      * unfold l_undef. unfold Undef in Hundef. now rewrite Hundef.
Qed.

Definition find_decision (m: PA) (f: CNF): option Lit :=
CNF.fold (fun (c: Clause) (r: option Lit) =>
  match r with
  | Some l => Some l
  | None   => find_undef_l m c
  end) f None.

Lemma find_decision_decomp: forall (m: PA) (f: CNF) (l: Lit), 
  find_decision m f = Some l -> exists (c: Clause), find_undef_l m c = Some l /\ CNF.In c f.
Proof.
  intros m f l. unfold find_decision. apply CNF.MP.fold_rec_nodep.
  - discriminate.
  - intros c r Hc_in_f IH Hr. destruct r as [l'|].
    + now apply IH.
    + now exists c.
Qed.

Lemma find_decision_exists: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  Clause.In l c -> CNF.In c f -> Undef m l -> exists (l': Lit), find_decision m f = Some l'.
Proof.
  intros m f c l Hl_in_c Hc_in_f Hundef. unfold find_decision. revert Hc_in_f.
  apply CNF.MP.fold_rec.
  - intros f' Hempty Hc_in_f'. now apply Hempty in Hc_in_f'.
  - intros c' r f' f'' _ _ Hadd IH Hc_in_f''. destruct r as [l'|].
    + now exists l'.
    + apply Hadd in Hc_in_f'' as [Hequal|Hc_in_f'].
      * apply Hequal in Hl_in_c. now apply (find_undef_l_exists m c' l).
      * apply IH in Hc_in_f' as [l' Hcontra]. discriminate.
Qed.

Lemma undef_decision_exists: forall (m: PA) (f: CNF),
  f_eval m f = None -> exists (l: Lit), find_decision m f = Some l.
Proof.
  intros m f Hf. unfold f_eval in Hf.
  destruct (CNF.for_all (c_true m) f) eqn:Hall.
  - discriminate.
  - destruct (CNF.exists_ (c_false m) f) eqn:Hexists.
    + discriminate.
    + apply CNF.for_all_mem_4 in Hall as [c [Hc_in_f Hc_true]].
      * apply CNF.mem_spec in Hc_in_f. destruct (c_eval m c) as [[|]|] eqn:Hc.
        -- unfold c_true in Hc_true. now rewrite Hc in Hc_true.
        -- assert (Hc_false: CNF.exists_ (c_false m) f = true).
          ++ apply CNF.exists_spec.
            ** intros c1 c2 Heq. unfold c_false. unfold c_eval.
               rewrite (Clause.c_equal_exists _ c1 c2 Heq). now rewrite (Clause.c_equal_forall _ c1 c2 Heq).
            ** exists c. split.
              --- assumption.
              --- unfold c_false. now rewrite Hc.
          ++ congruence.
        -- apply c_eval_none_iff in Hc as [_ [l [Hl_in_c Hl]]].
           now apply (find_decision_exists m f c l).
      * intros c1 c2 Heq. unfold c_true. unfold c_eval.
        rewrite (Clause.c_equal_exists _ c1 c2 Heq). now rewrite (Clause.c_equal_forall _ c1 c2 Heq).
Qed.

Lemma find_decision_undef: forall (m: PA) (f: CNF) (l: Lit),
  find_decision m f = Some l -> Undef m l.
Proof.
  intros m f l Hfind. apply find_decision_decomp in Hfind as [c [Hfind _]].
  now apply find_undef_l_undef in Hfind.
Qed.

Lemma find_decision_bounded: forall (m: PA) (f: CNF) (l: Lit),
  find_decision m f = Some l -> l_in_f f l = true.
Proof.
  intros m f l Hfind. apply find_decision_decomp in Hfind as [c [Hfind Hc_in_f]].
  apply CNF.l_in_f_true_iff. exists c. split.
  - left. now apply find_undef_l_in_c in Hfind.
  - assumption.
Qed.

Lemma wf_backtrack: forall (m m': PA) (f: CNF) (l: Lit),
  split_last_decision m = Some (m', l) ->
  WellFormed m f -> WellFormed (m' ++p (¬l)) f.
Proof.
  unfold WellFormed. intros m m' f l Heq Hwf. apply split_decomp in Heq as [n [Heq _]].
  rewrite Heq in Hwf. split.
  - destruct Hwf as [Hnodup _]. apply (nodup_app__nodup (m' ++d l)) in Hnodup.
    assert (Hnodup': NoDuplicates m').
    + now apply (nodup_cons__nodup) in Hnodup.
    + apply nodup_cons__undef in Hnodup as Hundef. 
      apply l_eval_neg_none_iff in Hundef.
      apply (nodup_cons _ _ _ Hnodup' Hundef).
  - destruct Hwf as [_ Hbounded]. apply (bounded_incl (m' ++d l)) in Hbounded.
    + assert (Hbounded': Bounded m' f).
      * apply (bounded_incl m') in Hbounded.
        -- assumption.
        -- apply incl_tl. apply incl_refl.
      * assert (In (l, dec) (m' ++d l)).
        -- now left.
        -- apply Hbounded in H as [c [Hc_in_f [Hl_in_c|Hnegl_in_c]]].
          ++ intros l' a' Hin. destruct Hin.
            ** injection H as <- <-. exists c. rewrite Neg.involutive. intuition.
            ** now apply Hbounded' in H.
          ++ intros l' a' Hin. destruct Hin.
            ** injection H as <- <-. exists c. intuition.
            ** now apply Hbounded' in H.
    + apply incl_appr. apply incl_refl.
Qed.

Lemma wf_unit: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  find_unit m f = Some (c, l) ->
  WellFormed m f -> WellFormed (m ++p l) f.
Proof.
  unfold WellFormed. intros m f c l Heq Hwf. split.
  - apply nodup_cons.
    + intuition congruence.
    + now apply find_unit_undef in Heq.
  - apply bounded_cons. 
    + intuition congruence. 
    + now apply find_unit_bounded in Heq.
Qed.

Lemma wf_decide: forall (m: PA) (f: CNF) (l: Lit),
  find_decision m f = Some l ->
  WellFormed m f -> WellFormed (m ++d l) f.
Proof.
  unfold WellFormed. intros m f l Heq Hwf. split.
  - apply nodup_cons.
    + intuition.
    + now apply find_decision_undef in Heq.
  - apply bounded_cons.
    + intuition.
    + now apply find_decision_bounded in Heq.
Qed.

Equations next_state (s: State): option State :=
next_state fail := None;
next_state (state m f Hwf) :=
  match find_conflict m f with
  | Some c =>
    match inspect (split_last_decision m) with
    (* t_fail *)
    | None         eqn:Heq => Some fail
    (* t_backtrack *)
    | Some (m', l) eqn:Heq => Some (state (m' ++p (¬l)) f (wf_backtrack m m' f l Heq Hwf))
    end
  | _      =>
  (* t_unit *)
  match inspect (find_unit m f) with
  | Some (c, l)    eqn:Heq => Some (state (m ++p l) f (wf_unit m f c l Heq Hwf))
  | None           eqn:Heq =>
  (* t_decide *)
  match inspect (find_decision m f) with
  | Some l         eqn:Heq => Some (state (m ++d l) f (wf_decide m f l Heq Hwf))
  | None           eqn:Heq => None
  end end end.

Lemma split_none_iff: forall (m: PA), split_last_decision m = None <-> NoDecisions m.
Proof. 
  unfold NoDecisions. unfold not. intros. split.
  - intros. funelim (split_last_decision m).
    + destruct H0. destruct H0.
    + discriminate.
    + destruct H1. destruct H1.
      * discriminate.
      * apply (H m H0).
        -- now exists x.
        -- reflexivity.
        -- reflexivity.
  - intros. funelim (split_last_decision m).
    + reflexivity.
    + exfalso. apply H. exists l. now left.
    + apply H. intros. apply H0. destruct H1. exists x. now right.
Qed.

Lemma find_unit_conflicting: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  find_unit m f = Some (c, l) -> c_eval m (Clause.remove l c) = Some false.
Proof.
  intros m f c l Hfind. apply find_unit_decomp in Hfind as [Hfind _].
  unfold find_unit_l in Hfind. apply Clause.choose_spec1 in Hfind.
  apply Clause.filter_spec in Hfind as [_ Hl].
  - apply andb_true_iff in Hl as [_ Hc]. unfold c_false in Hc.
    destruct (c_eval m (Clause.remove l c)) as [[|]|]; easy.
  - now intros ? ? ->.
Qed.

Lemma next_state_sound: forall (s s': State), next_state s = Some s' -> s ==> s'.
Proof.
  intros. funelim (next_state s); rewrite H in Heqcall; clear H.
  - discriminate.
  - destruct (find_conflict m f) as [c_conflict|] eqn:find_conflict.
    + destruct (inspect (split_last_decision m)) as [[(m_split, l_split)|] split_last_decision].
      (* t_backtrack *)
      * injection Heqcall as <-.
        destruct (split_decomp _ _ _ split_last_decision) as [n_split [-> no_dec]].
        apply (t_backtrack m_split n_split f c_conflict l_split).
        -- now apply (find_conflict_c_in_f (m_split ++d l_split ++a n_split) f c_conflict).
        -- now apply (find_conflict_conflicting (m_split ++d l_split ++a n_split) f c_conflict).
        -- assumption.
      (* t_fail *)
      * injection Heqcall as <-. apply (t_fail m f c_conflict).
        -- now apply (find_conflict_c_in_f m f c_conflict).
        -- now apply (find_conflict_conflicting m f c_conflict).
        -- now apply (split_none_iff m).
    + destruct (inspect (find_unit m f)) as [[(c_unit, l_unit)|] find_unit].
      (* t_unit *)
      * injection Heqcall as <-. apply (t_unit m f c_unit l_unit).
        -- now apply (find_unit_l_in_c m f c_unit l_unit).
        -- now apply (find_unit_c_in_f m f c_unit l_unit).
        -- now apply (find_unit_conflicting m f c_unit l_unit).
        -- now apply (find_unit_undef m f c_unit l_unit).
      * destruct (inspect (find_decision m f)) as [[l_decide|] find_decision].
        (* t_decide *)
        -- injection Heqcall as <-.
           destruct (find_decision_decomp m f l_decide find_decision) as [c_decide [Hc Hc_in_f]].
           apply (t_decide m f c_decide l_decide).
          ++ left. now apply (find_undef_l_in_c m c_decide l_decide).
          ++ assumption.
          ++ now apply (find_undef_l_undef m c_decide l_decide).
        -- discriminate.
Qed.

(* The rhs is weaker because there could be multiple { s': State | s ==>b s' }. *)
Lemma next_state_exists: forall (s s': State), s ==>b s' -> exists (s'': State), next_state s = Some s''.
Proof.
  intros. inversion H as 
    [
      m f c_conflict Hwf Hc_in_f Hconflict Hno_dec |
      m f c_decide l_decide Hwf Hwf' Hx_in_c Hc_in_f Hundef |
      m_split n_split f c_conflict l_split Hwf Hwf' Hc_in_f Hconflict Hno_dec
    ]; subst s s'.
  (* t_fail *)
  - funelim (next_state (state m f Hwf)).
    + discriminate.
    + injection eqargs as <- <-.
      destruct (find_conflict m f) as [c_conflict'|] eqn:Hfind_conflict.
      * destruct (inspect (split_last_decision m)) as [[(m_split, l_split)|] Hsplit].
        -- now exists (state (m_split ++p (¬l_split)) f (wf_backtrack m m_split f l_split Hsplit Hwf)).
        -- now exists fail.
      * destruct (proj2 (find_conflict_exists_iff m f)). now exists c_conflict. congruence.
  (* t_decide *)
  - funelim (next_state (state m f Hwf)).
    + discriminate.
    + injection eqargs as <- <-.
      destruct (find_conflict m f) as [c_conflict'|] eqn:Hfind_conflict.
      * destruct (inspect (split_last_decision m)) as [[(m_split, l_split)|] Hsplit].
        -- now exists (state (m_split ++p (¬l_split)) f (wf_backtrack m m_split f l_split Hsplit Hwf)).
        -- now exists fail.
      * destruct (inspect (find_unit m f)) as [[(c_unit', l_unit')|] Hfind_unit].
        -- now exists (state (m ++p l_unit') f (wf_unit m f c_unit' l_unit' Hfind_unit Hwf)).
        -- destruct (inspect (find_decision m f)) as [[l_decide'|] Hfind_dec].
          ++ now exists (state (m ++d l_decide') f (wf_decide m f l_decide' Hfind_dec Hwf)).
          ++ destruct Hx_in_c as [Hl_in_c|Hnegl_in_c].
            ** destruct (find_decision_exists m f c_decide l_decide Hl_in_c Hc_in_f Hundef). congruence.
            ** apply l_eval_neg_none_iff in Hundef.
               destruct (find_decision_exists m f c_decide (¬l_decide) Hnegl_in_c Hc_in_f Hundef). congruence.
  (* t_backtrack *)
  - funelim (next_state (state (m_split ++d l_split ++a n_split) f Hwf)).
    + discriminate.
    + injection eqargs as ? <-. rewrite <- H0 in *. clear H0.
      destruct (find_conflict m f) as [c_conflict'|] eqn:Hfind_conflict.
      * destruct (inspect (split_last_decision m)) as [[(m_split', l_split')|] Hsplit].
        -- now exists (state (m_split' ++p (¬l_split')) f (wf_backtrack m m_split' f l_split' Hsplit Hwf)).
        -- now exists fail.
      * destruct (inspect (find_unit m f)) as [[(c_unit', l_unit')|] Hfind_unit].
        -- now exists (state (m ++p l_unit') f (wf_unit m f c_unit' l_unit' Hfind_unit Hwf)).
        -- destruct (inspect (find_decision m f)) as [[l_decide'|] Hfind_dec].
          ++ now exists (state (m ++d l_decide') f (wf_decide m f l_decide' Hfind_dec Hwf)).
          ++ destruct (proj2 (find_conflict_exists_iff m f)). now exists c_conflict. congruence.
Qed.

Lemma next_state_strategy: Strategy (next_state).
Proof.
  unfold Strategy. split.
  - reflexivity.
  - split.
    + intros. unfold FinalB. unfold not. intros. destruct H0. 
      apply next_state_exists in H0. destruct H0. congruence.
    + intros. apply t_step. now apply next_state_sound.
Qed.
