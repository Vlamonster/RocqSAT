From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import Relations.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import State.
From RocqSAT Require Import Trans.
From RocqSAT.rules Require Import Fail.
From RocqSAT.rules Require Import Unit.
From RocqSAT.rules Require Import Decide.
From RocqSAT.rules Require Import Backtrack.

(* A strategy picks the next state: it never steps from fail, it only stops at states that are final for Basic, and every step it takes is a non-empty derivation. *)
Definition Strategy (next: State -> option State): Prop :=
  (next fail = None) /\
  (forall (s: State), next s = None -> Final Basic s) /\
  (forall (s s': State), next s = Some s' -> s ==>+ s').

(* States produced by a strategy stay reachable from the initial state. *)
Lemma strategy_trans: forall (f: CNF) (s s': State) (next: State -> option State) (Hstrat: Strategy next),
  next s = Some s' ->
  state [] f ==>* s ->
  state [] f ==>* s'.
Proof.
  intros f s s' next Hstrat ns H. eapply rt_trans.
  - apply H.
  - apply Hstrat in ns. now apply clos_t_clos_rt in ns.
Qed.

(* Some clause of f that is false under m, if there is one. *)
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

(* A literal of c that is unassigned while the rest of c is false, i.e. the unit literal if c is a unit clause. *)
Definition find_unit_l (m: PA) (c: Clause): option Lit :=
Clause.choose (Clause.filter (fun (l: Lit) => l_undef m l && c_false m (Clause.remove l c)) c).

(* The first clause of f that is a unit clause, together with its unit literal. *)
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

(* Some literal of c without a value. *)
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

(* Some literal of f without a value, taken from the first clause that has one. *)
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

(* If f is undefined under m, there is still a literal to decide. *)
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

(* One solver step: on a conflict, backtrack (or fail if there is no decision to undo); otherwise propagate a unit literal if there is one; otherwise decide a literal; otherwise stop. *)
Definition next_state (s: State): option State :=
match s with
| fail      => None
| state m f =>
  match find_conflict m f with
  | Some _ =>
    match split_last_decision m with
    (* Fail *)
    | None         => Some fail
    (* Backtrack *)
    | Some (m', l) => Some (state (m' ++p (¬l)) f)
    end
  | None   =>
  (* Unit *)
  match find_unit m f with
  | Some (_, l) => Some (state (m ++p l) f)
  | None        =>
  (* Decide *)
  match find_decision m f with
  | Some l => Some (state (m ++d l) f)
  | None   => None
  end end end
end.

(* The unit clause that find_unit returns is false apart from its unit literal. *)
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
  intros [|m f] s' Hnext.
  - discriminate.
  - unfold next_state in Hnext. destruct (find_conflict m f) as [c_conflict|] eqn:Hfind_conflict.
    + destruct (split_last_decision m) as [[m_split l_split]|] eqn:Hsplit.
      (* Backtrack *)
      * injection Hnext as <-.
        apply split_last_decision_some_iff in Hsplit as [n_split [-> Hno_dec]].
        apply (t_step Backtrack).
        -- right. right. right. now left.
        -- apply (r_backtrack m_split n_split f c_conflict l_split).
          ++ now apply (find_conflict_c_in_f (m_split ++d l_split ++a n_split) f c_conflict).
          ++ now apply (find_conflict_conflicting (m_split ++d l_split ++a n_split) f c_conflict).
          ++ assumption.
      (* Fail *)
      * injection Hnext as <-. apply (t_step Fail).
        -- now left.
        -- apply (r_fail m f c_conflict).
          ++ now apply (find_conflict_c_in_f m f c_conflict).
          ++ now apply (find_conflict_conflicting m f c_conflict).
          ++ now apply (split_last_decision_none_iff m).
    + destruct (find_unit m f) as [[c_unit l_unit]|] eqn:Hfind_unit.
      (* Unit *)
      * injection Hnext as <-. apply (t_step Unit).
        -- right. now left.
        -- apply (r_unit m f c_unit l_unit).
          ++ now apply (find_unit_l_in_c m f c_unit l_unit).
          ++ now apply (find_unit_c_in_f m f c_unit l_unit).
          ++ now apply (find_unit_conflicting m f c_unit l_unit).
          ++ now apply (find_unit_undef m f c_unit l_unit).
      * destruct (find_decision m f) as [l_decide|] eqn:Hfind_decision.
        (* Decide *)
        -- injection Hnext as <-.
           destruct (find_decision_decomp m f l_decide Hfind_decision) as [c_decide [Hc Hc_in_f]].
           apply (t_step Decide).
          ++ right. right. now left.
          ++ apply (r_decide m f c_decide l_decide).
            ** left. now apply (find_undef_l_in_c m c_decide l_decide).
            ** assumption.
            ** now apply (find_undef_l_undef m c_decide l_decide).
        -- discriminate.
Qed.

(* next_state only stops at a state without a conflict and without a literal to decide. *)
Lemma next_state_none: forall (m: PA) (f: CNF),
  next_state (state m f) = None -> find_conflict m f = None /\ find_decision m f = None.
Proof.
  intros m f Hnext. unfold next_state in Hnext. destruct (find_conflict m f).
  - destruct (split_last_decision m) as [[m' l]|].
    + discriminate.
    + discriminate.
  - destruct (find_unit m f) as [[c l]|].
    + discriminate.
    + destruct (find_decision m f).
      * discriminate.
      * now split.
Qed.

(* The rhs is weaker because there could be multiple { s': State | s ==>[Basic] s' }. *)
Lemma next_state_exists: forall (s s': State), s ==>[Basic] s' -> exists (s'': State), next_state s = Some s''.
Proof.
  intros s s' Htrans. inversion Htrans as [r m f s'' Hr Hstep]; subst.
  destruct (next_state (state m f)) as [s''|] eqn:Hnext.
  - now exists s''.
  - exfalso. apply next_state_none in Hnext as [Hno_conflict Hno_decision].
    destruct Hr as [<-|[<-|[<-|[]]]].
    (* Fail *)
    + inversion Hstep as [? ? c_conflict Hc_in_f Hconflict Hno_dec]; subst.
      destruct (proj2 (find_conflict_exists_iff m f)).
      * now exists c_conflict.
      * congruence.
    (* Decide *)
    + inversion Hstep as [? ? c_decide l_decide Hx_in_c Hc_in_f Hundef]; subst.
      destruct Hx_in_c as [Hl_in_c|Hnegl_in_c].
      * destruct (find_decision_exists m f c_decide l_decide Hl_in_c Hc_in_f Hundef). congruence.
      * apply l_eval_neg_none_iff in Hundef.
        destruct (find_decision_exists m f c_decide (¬l_decide) Hnegl_in_c Hc_in_f Hundef). congruence.
    (* Backtrack *)
    + inversion Hstep as [m_split n_split ? c_conflict l_split Hc_in_f Hconflict Hno_dec]; subst.
      destruct (proj2 (find_conflict_exists_iff (m_split ++d l_split ++a n_split) f)).
      * now exists c_conflict.
      * congruence.
Qed.

Lemma next_state_strategy: Strategy (next_state).
Proof.
  unfold Strategy. split.
  - reflexivity.
  - split.
    + intros. unfold Final. unfold not. intros. destruct H0. 
      apply next_state_exists in H0. destruct H0. congruence.
    + intros. apply Relation_Operators.t_step. now apply next_state_sound.
Qed.
