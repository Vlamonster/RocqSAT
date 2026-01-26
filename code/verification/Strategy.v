From Equations Require Import Equations.
From Stdlib Require Import Bool List Relations.
Import ListNotations.
From RocqSAT Require Import Lit Neg Clause CNF Evaluation Trans Inspect WellFormed Termination.

Definition Strategy (next: State -> option State): Prop :=
  (next fail = None) /\
  (forall (s: State), next s = None -> Final s) /\
  (forall (s s': State), next s = Some s' -> s ==> s').

Lemma strategy_trans: forall (f: CNF) (s s': State) (next: State -> option State) (Hstrat: Strategy next),
  next s = Some s' ->
  state [] f (initial_wf f) ==>* s ->
  state [] f (initial_wf f) ==>* s'.
Proof.
  intros f s s' next Hstrat ns H. eapply rt_trans.
  - apply H.
  - apply rt_step. now apply Hstrat.
Qed.

Equations is_conflict (m: PA) (c: Clause): bool :=
is_conflict m c with c_eval m c :=
  | Some false := true
  | _          := false.

Equations find_conflict (m: PA) (f: CNF): option Clause :=
find_conflict m f := find (is_conflict m) f.

Lemma find_conflict_c_in_f: forall (m: PA) (f: CNF) (c: Clause), 
  find_conflict m f = Some c -> In c f.
Proof. intros. simp find_conflict in H. now apply find_some in H. Qed.

Lemma find_conflict_conflicting: forall (m: PA) (f: CNF) (c: Clause), 
  find_conflict m f = Some c -> Conflicting m c.
Proof. 
  unfold Conflicting. intros. simp find_conflict in H. apply find_some in H as [_ H]. 
  funelim (is_conflict m c); congruence.
Qed.

Lemma find_conflict_exists_iff: forall (m: PA) (f: CNF),
  (exists (c: Clause), find_conflict m f = Some c) <-> exists (c: Clause), In c f /\ Conflicting m c.
Proof.
  unfold Conflicting. intros. split.
  - intros [c Hfind]. exists c. split.
    + now apply find_conflict_c_in_f in Hfind.
    + now apply find_conflict_conflicting in Hfind.
  - intros [c [Hin Hc]]. destruct (find_conflict m f) as [c'|] eqn:Hfind.
    + now exists c'.
    + simp find_conflict in Hfind. apply find_none with (x := c) in Hfind as contra.
      * simp is_conflict in contra. now rewrite Hc in contra.
      * assumption.
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

Equations find_unit_l (m: PA) (c: Clause): option Lit :=
find_unit_l m c := find (fun (l: Lit) => is_conflict m (l_remove c l)) c.

Equations find_unit (m: PA) (f: CNF): option (Clause * Lit) :=
find_unit m [] := None;
find_unit m (c :: f) with c_eval m c, find_unit_l m c :=
  | None, Some l := Some (c, l)
  | _   , _      := find_unit m f.

Lemma find_unit_undef: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  find_unit m f = Some (c, l) -> Undef m l.
Proof. 
  unfold Undef. intros. funelim (find_unit m f).
  - discriminate.
  - apply (H c0 l0). congruence.
  - rewrite H in Heqcall. injection Heqcall as <- <-. funelim (find_unit_l m c).
    rewrite Heq in Heqcall. apply find_some in Heqcall. destruct Heqcall.
    funelim (is_conflict m (l_remove c l)).
    + congruence.
    + apply (undef_remove_false__undef _ _ _ Heq1 Heq).
    + congruence.
  - apply (H c0 l). congruence.
Qed.

Lemma find_unit_l_l_in_c: forall (m: PA) (c: Clause) (l: Lit),
  find_unit_l m c = Some l -> In l c.
Proof.
  intros. funelim (find_unit_l m c). rewrite H in Heqcall. 
  apply find_some in Heqcall. intuition.
Qed.

Lemma find_unit_l_in_c: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  find_unit m f = Some (c, l) -> In l c.
Proof. 
  intros. funelim (find_unit m f).
  - congruence.
  - apply H. congruence.
  - rewrite H in Heqcall. injection Heqcall as <- <-.
    now apply find_unit_l_l_in_c in Heq.
  - apply H. congruence.
Qed.

Lemma find_unit_c_in_f: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  find_unit m f = Some (c, l) -> In c f.
Proof. 
  intros. funelim (find_unit m f).
  - congruence.
  - right. apply (H c0 l0). congruence.
  - rewrite H in Heqcall. injection Heqcall as <- <-. now left.
  - right. apply (H c0 l). congruence.
Qed.

Lemma find_unit_bounded: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  find_unit m f = Some (c, l) -> l_in_f f l = true.
Proof.
  intros. simp l_in_f. apply existsb_exists. exists c. split.
  - now apply find_unit_c_in_f in H.
  - simp l_in_c. apply orb_true_iff. left. apply existsb_exists. exists l. split.
    + now apply find_unit_l_in_c in H.
    + apply eqb_refl.
Qed.

Equations is_undefined_l (m: PA) (l: Lit): bool :=
is_undefined_l m l with l_eval m l := 
  | None := true
  | _    := false.

Equations find_undef_l (m: PA) (c: Clause): option Lit :=
find_undef_l m c := find (is_undefined_l m) c.

Lemma find_undef_l_def: forall (m: PA) (c: Clause),
  find_undef_l m c = None -> exists (b: bool), c_eval m c = Some b.
Proof.
  intros. simp find_undef_l in H. funelim (c_eval m c).
  - now exists false.
  - now exists true.
  - now exists true.
  - now exists false.
  - simpl in H. simp is_undefined_l in H. rewrite Heq0 in H. simpl in H.
    apply Hind in H; destruct H; congruence.
  - now exists true.
  - apply find_none with (x := l) in H.
    + simp is_undefined_l in H. now rewrite Heq0 in H.
    + now left.
  - apply find_none with (x := l) in H.
    + simp is_undefined_l in H. now rewrite Heq0 in H.
    + now left.
Qed.

Equations find_decision (m: PA) (f: CNF): option Lit :=
find_decision m [] := None;
find_decision m (c :: f) with find_undef_l m c, find_decision m f :=
  | Some l, _ := Some l
  | _     , r := r.

Lemma undef_decision_exists: forall (m: PA) (f: CNF),
  f_eval m f = None -> exists (l: Lit), find_decision m f = Some l.
Proof.
  intros. funelim (find_decision m f).
  - discriminate.
  - now exists l.
  - apply Hind.
    + simp f_eval in H. apply find_undef_l_def in Heq as [[|] Heq].
      * now rewrite Heq in H.
      * now rewrite Heq in H.
    + reflexivity.
    + reflexivity.
Qed.

Lemma find_decision_undef: forall (m: PA) (f: CNF) (l: Lit),
  find_decision m f = Some l -> Undef m l.
Proof.
  unfold Undef. intros. funelim (find_decision m f).
  - congruence.
  - rewrite H in Heqcall. injection Heqcall as <-. funelim (find_undef_l m c).
    rewrite Heq in Heqcall. apply find_some in Heqcall. funelim (is_undefined_l m l).
    + intuition congruence.
    + assumption.
  - rewrite H in Heqcall. now apply Hind.
Qed.

Lemma find_decision_bounded: forall (m: PA) (f: CNF) (l: Lit),
  find_decision m f = Some l -> l_in_f f l = true.
Proof. 
  intros. funelim (find_decision m f).
  - congruence.
  - rewrite H in Heqcall. injection Heqcall as <-. funelim (find_undef_l m c).
    rewrite Heq in Heqcall. apply find_some in Heqcall.
    simp l_in_f. apply existsb_exists. exists c. split.
    + now left.
    + simp l_in_c. apply orb_true_iff. left. destruct Heqcall as [Hin _].
      apply existsb_exists. exists l. intuition. apply eqb_refl.
  - rewrite H in Heqcall. apply Hind in Heqcall. simp l_in_f in *.
    apply existsb_exists in Heqcall. destruct Heqcall. destruct H0.
    apply existsb_exists. exists x. split.
    + now right.
    + assumption.
Qed.

Lemma wf_backtrack: forall (m m': PA) (f: CNF) (l: Lit),
  split_last_decision m = Some (m', l) ->
  WellFormed m f -> WellFormed (m' ++p ¬l) f.
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
    | Some (m', l) eqn:Heq => Some (state (m' ++p ¬l) f (wf_backtrack m m' f l Heq Hwf))
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
  find_unit m f = Some (c, l) -> Conflicting m (l_remove c l).
Proof.
  unfold Conflicting. intros. funelim (find_unit m f).
  - discriminate.
  - apply H. congruence.
  - rewrite H in Heqcall. injection Heqcall as <- <-.
    funelim (find_unit_l m c). rewrite Heq in Heqcall. apply find_some in Heqcall.
    destruct Heqcall. funelim (is_conflict m (l_remove c l)); congruence.
  - apply H. congruence.
Qed.

Lemma find_decision_decomp: forall (m: PA) (f: CNF) (l: Lit), 
  find_decision m f = Some l -> exists (c: Clause), find_undef_l m c = Some l /\ In c f.
Proof.
  intros. funelim (find_decision m f).
  - congruence.
  - rewrite H in Heqcall. injection Heqcall as <-. exists c. split.
    + assumption.
    + now left.
  - rewrite H in Heqcall. apply Hind in Heqcall. destruct Heqcall. destruct H0.
    exists x. split.
    + assumption.
    + now right.
Qed.

Lemma find_undef_l_in_c: forall (m: PA) (c: Clause) (l: Lit), 
  find_undef_l m c = Some l -> In l c.
Proof.
  intros. funelim (find_undef_l m c). rewrite H in Heqcall. 
  apply find_some in Heqcall. now destruct Heqcall.
Qed.

Lemma find_undef_l_undef: forall (m: PA) (c: Clause) (l: Lit), 
  find_undef_l m c = Some l -> Undef m l.
Proof. 
  unfold Undef. intros. funelim (find_undef_l m c). rewrite H in Heqcall. 
  apply find_some in Heqcall. destruct Heqcall. funelim (is_undefined_l m l); congruence.
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

Lemma find_undef_l_exists : forall (m: PA) (c: Clause) (l: Lit),
  In l c -> Undef m l -> exists (l': Lit), find_undef_l m c = Some l'.
Proof.
  unfold Undef. intros. destruct (find_undef_l m c) eqn:G.
  - now exists l0.
  - simp find_undef_l in G. apply (find_none (is_undefined_l m) c G l) in H.
    simp is_undefined_l in H. rewrite H0 in H. discriminate.
Qed.

Lemma find_decision_exists: forall (m: PA) (f: CNF) (c: Clause) (l: Lit),
  In l c -> In c f -> Undef m l -> exists (l': Lit), find_decision m f = Some l'.
Proof. 
  intros. funelim (find_decision m f).
  - contradiction.
  - now exists l.
  - apply (Hind c0 l); auto. inversion H0; auto. subst.
    destruct (find_undef_l_exists m c0 l H H1). congruence.
Qed.

(* The rhs is weaker because there could be multiple { s': State | s ==> s' }. *)
Lemma next_state_exists: forall (s s': State), s ==> s' -> exists (s'': State), next_state s = Some s''.
Proof.
  intros. inversion H as 
    [
      m f c_conflict Hwf Hc_in_f Hconflict Hno_dec |
      m f c_unit l_unit Hwf Hwf' Hl_in_c Hc_in_f Hconflict Hundef |
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
  (* t_unit *)
  - funelim (next_state (state m f Hwf)).
    + discriminate.
    + injection eqargs as <- <-.
      destruct (find_conflict m f) as [c_conflict'|] eqn:Hfind_conflict.
      * destruct (inspect (split_last_decision m)) as [[(m_split, l_split)|] Hsplit].
        -- now exists (state (m_split ++p (¬l_split)) f (wf_backtrack m m_split f l_split Hsplit Hwf)).
        -- now exists fail.
      * destruct (inspect (find_unit m f)) as [[(c_unit', l_unit')|] Hfind_unit].
        -- now exists (state (m ++p l_unit') f (wf_unit m f c_unit' l_unit' Hfind_unit Hwf)).
        -- destruct (inspect (find_decision m f)) as [[l_decide|] Hfind_dec].
          ++ now exists (state (m ++d l_decide) f (wf_decide m f l_decide Hfind_dec Hwf)).
          ++ destruct (find_decision_exists m f c_unit l_unit Hl_in_c Hc_in_f Hundef). congruence.
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

Lemma next_state_final_refl: forall (s: State), next_state s = None <-> Final s.
Proof.
  unfold Final. unfold not. intros. split.
  - intros. destruct H0. apply next_state_exists in H0. destruct H0. congruence.
  - intros. destruct (next_state s) eqn:G.
    + apply next_state_sound in G. exfalso. apply H. now exists s0.
    + reflexivity.
Qed.

Lemma next_state_strategy: Strategy (next_state).
Proof.
  unfold Strategy. split.
  - reflexivity.
  - split.
    + apply next_state_final_refl.
    + apply next_state_sound.
Qed.
