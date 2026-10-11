From RocqSAT Require Import Lit.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import State.
From RocqSAT Require Import Trans.
From RocqSAT Require Import Strategy.
From RocqSAT.rules Require Import Fail.
From RocqSAT.rules Require Import Unit.
From RocqSAT.rules Require Import Decide.
From RocqSAT.rules Require Import Backtrack.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Search.

(* One solver step from state m f, where v are the values of m: on a conflict, backtrack (or fail if there is no decision to undo); otherwise propagate a unit literal if there is one; otherwise decide a literal; otherwise stop. *)
Definition next_state_values (v: Values) (m: PA) (f: CNF): option State :=
  match find_conflict v f with
  | Some _ =>
    match split_last_decision m with
    (* Fail *)
    | None         => Some fail
    (* Backtrack *)
    | Some (m', l) => Some (state ⟨m', (¬l)⟩ f)
    end
  | None   =>
  (* Unit *)
  match find_unit v f with
  | Some (_, l) => Some (state ⟨m, l⟩ f)
  | None        =>
  (* Decide *)
  match find_decision v f with
  | Some l => Some (state ⟨m; l⟩ f)
  | None   => None
  end end end.

(* One solver step, computing the values of the trail once. *)
Definition next_state (s: State): option State :=
match s with
| fail      => None
| state m f => next_state_values (values m) m f
end.

Lemma next_state_sound: forall (s s': State), next_state s = Some s' -> s ==> s'.
Proof.
  intros [|m f] s' Hnext.
  - discriminate.
  - unfold next_state, next_state_values in Hnext. destruct (find_conflict (values m) f) as [c_conflict|] eqn:Hfind_conflict.
    + destruct (split_last_decision m) as [[m_split l_split]|] eqn:Hsplit.
      (* Backtrack *)
      * injection Hnext as <-.
        apply PA.split_last_decision_some_iff in Hsplit as [n_split [-> Hno_dec]].
        apply (t_step Backtrack).
        -- right. right. right. now left.
        -- apply (r_backtrack m_split n_split f c_conflict l_split).
          ++ now apply (find_conflict_c_in_f ⟨m_split; l_split ++ n_split⟩ f c_conflict).
          ++ now apply (find_conflict_conflicting ⟨m_split; l_split ++ n_split⟩ f c_conflict).
          ++ assumption.
      (* Fail *)
      * injection Hnext as <-. apply (t_step Fail).
        -- now left.
        -- apply (r_fail m f c_conflict).
          ++ now apply (find_conflict_c_in_f m f c_conflict).
          ++ now apply (find_conflict_conflicting m f c_conflict).
          ++ now apply (PA.split_last_decision_none_iff m).
    + destruct (find_unit (values m) f) as [[c_unit l_unit]|] eqn:Hfind_unit.
      (* Unit *)
      * injection Hnext as <-. apply (t_step Unit).
        -- right. now left.
        -- apply (r_unit m f c_unit l_unit).
          ++ now apply (find_unit_l_in_c m f c_unit l_unit).
          ++ now apply (find_unit_c_in_f m f c_unit l_unit).
          ++ now apply (find_unit_conflicting m f c_unit l_unit).
          ++ now apply (find_unit_undef m f c_unit l_unit).
      * destruct (find_decision (values m) f) as [l_decide|] eqn:Hfind_decision.
        (* Decide *)
        -- injection Hnext as <-.
           destruct (find_decision_decomp m f l_decide Hfind_decision) as [c_decide [Hc Hc_in_f]].
           apply (t_step Decide).
          ++ right. right. now left.
          ++ apply r_decide.
            ** left. exists c_decide. split.
              --- now apply (find_undef_l_in_c m c_decide l_decide).
              --- assumption.
            ** now apply (find_undef_l_undef m c_decide l_decide).
        -- discriminate.
Qed.

(* next_state only stops at a state without a conflict and without a literal to decide. *)
Lemma next_state_none: forall (m: PA) (f: CNF),
  next_state (state m f) = None -> find_conflict (values m) f = None /\ find_decision (values m) f = None.
Proof.
  intros m f Hnext. unfold next_state, next_state_values in Hnext.
  destruct (find_conflict (values m) f), (split_last_decision m) as [[]|], (find_unit (values m) f) as [[]|], (find_decision (values m) f); easy.
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
    + inversion Hstep as [? ? l_decide Hl_in_f Hundef]; subst.
      destruct Hl_in_f as [Hl_in_f|Hnegl_in_f].
      * destruct (find_decision_exists m f l_decide Hl_in_f Hundef). congruence.
      * apply l_eval_neg_none_iff in Hundef.
        destruct (find_decision_exists m f (¬l_decide) Hnegl_in_f Hundef). congruence.
    (* Backtrack *)
    + inversion Hstep as [m_split n_split ? c_conflict l_split Hc_in_f Hconflict Hno_dec]; subst.
      destruct (proj2 (find_conflict_exists_iff ⟨m_split; l_split ++ n_split⟩ f)).
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
