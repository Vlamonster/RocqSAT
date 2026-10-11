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

Lemma next_state_values_sound: forall (m: PA) (f: CNF) (s': State),
  next_state_values (values m) m f = Some s' -> state m f ==> s'.
Proof.
  intros m f s' Hnext. unfold next_state_values in Hnext.
  destruct (find_conflict (values m) f) as [c_conflict|] eqn:Hfind_conflict.
  - destruct (split_last_decision m) as [[m_split l_split]|] eqn:Hsplit.
    (* Backtrack *)
    + injection Hnext as <-.
      apply PA.split_last_decision_some_iff in Hsplit as [n_split [-> Hno_dec]].
      apply (t_step Backtrack).
      * right. right. right. now left.
      * apply (r_backtrack m_split n_split f c_conflict l_split).
        -- now apply (find_conflict_c_in_f ⟨m_split; l_split ++ n_split⟩ f c_conflict).
        -- now apply (find_conflict_conflicting ⟨m_split; l_split ++ n_split⟩ f c_conflict).
        -- assumption.
    (* Fail *)
    + injection Hnext as <-. apply (t_step Fail).
      * now left.
      * apply (r_fail m f c_conflict).
        -- now apply (find_conflict_c_in_f m f c_conflict).
        -- now apply (find_conflict_conflicting m f c_conflict).
        -- now apply (PA.split_last_decision_none_iff m).
  - destruct (find_unit (values m) f) as [[c_unit l_unit]|] eqn:Hfind_unit.
    (* Unit *)
    + injection Hnext as <-. apply (t_step Unit).
      * right. now left.
      * apply (r_unit m f c_unit l_unit).
        -- now apply (find_unit_l_in_c m f c_unit l_unit).
        -- now apply (find_unit_c_in_f m f c_unit l_unit).
        -- now apply (find_unit_conflicting m f c_unit l_unit).
        -- now apply (find_unit_undef m f c_unit l_unit).
    + destruct (find_decision (values m) f) as [l_decide|] eqn:Hfind_decision.
      (* Decide *)
      * injection Hnext as <-.
        destruct (find_decision_decomp m f l_decide Hfind_decision) as [c_decide [Hc Hc_in_f]].
        apply (t_step Decide).
        -- right. right. now left.
        -- apply r_decide.
          ++ left. exists c_decide. split.
            ** now apply (find_undef_l_in_c m c_decide l_decide).
            ** assumption.
          ++ now apply (find_undef_l_undef m c_decide l_decide).
      * discriminate.
Qed.

(* next_state_values only stops at a state without a conflict and without a literal to decide. *)
Lemma next_state_values_none: forall (m: PA) (f: CNF),
  next_state_values (values m) m f = None -> find_conflict (values m) f = None /\ find_decision (values m) f = None.
Proof.
  intros m f Hnext. unfold next_state_values in Hnext.
  destruct (find_conflict (values m) f), (split_last_decision m) as [[]|], (find_unit (values m) f) as [[]|], (find_decision (values m) f); easy.
Qed.

(* The rhs is weaker because there could be multiple { s': State | s ==>[Basic] s' }. *)
Lemma next_state_values_exists: forall (m: PA) (f: CNF) (s': State),
  state m f ==>[Basic] s' -> exists (s'': State), next_state_values (values m) m f = Some s''.
Proof.
  intros m f s' Htrans. inversion Htrans as [r ? ? s'' Hr Hstep]; subst.
  destruct (next_state_values (values m) m f) as [s''|] eqn:Hnext.
  - now exists s''.
  - exfalso. apply next_state_values_none in Hnext as [Hno_conflict Hno_decision].
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

(* The context of the solver: the values of the trail, kept up to date while stepping. *)
Definition ValuesInv (s: State) (v: Values): Prop :=
match s with
| fail      => True
| state m _ => v = values m
end.

(* One solver step, as next_state_values, that also updates the values: by adding the new literal, or by
   recomputing them after a backtrack. *)
Definition next_state (p: State * Values): option (State * Values) :=
match p with
| (fail, _)      => None
| (state m f, v) =>
  match find_conflict v f with
  | Some _ =>
    match split_last_decision m with
    (* Fail *)
    | None         => Some (fail, v)
    (* Backtrack *)
    | Some (m', l) => Some (state ⟨m', (¬l)⟩ f, values ⟨m', (¬l)⟩)
    end
  | None   =>
  (* Unit *)
  match find_unit v f with
  | Some (_, l) => Some (state ⟨m, l⟩ f, AtomMap.add (extract l) (is_pos l) v)
  | None        =>
  (* Decide *)
  match find_decision v f with
  | Some l => Some (state ⟨m; l⟩ f, AtomMap.add (extract l) (is_pos l) v)
  | None   => None
  end end end
end.

(* With up-to-date values, next_state takes the same step as next_state_values. *)
Lemma next_state_fst: forall (m: PA) (f: CNF),
  option_map fst (next_state (state m f, values m)) = next_state_values (values m) m f.
Proof.
  intros m f. unfold next_state, next_state_values.
  destruct (find_conflict (values m) f), (split_last_decision m) as [[]|], (find_unit (values m) f) as [[]|],
    (find_decision (values m) f); reflexivity.
Qed.

(* ... and keeps the values up to date. *)
Lemma next_state_inv: forall (s s': State) (v v': Values),
  ValuesInv s v -> next_state (s, v) = Some (s', v') -> ValuesInv s' v'.
Proof.
  intros [|m f] s' v v' Hinv Hnext.
  - discriminate.
  - simpl in Hinv. subst v. unfold next_state in Hnext.
    destruct (find_conflict (values m) f), (split_last_decision m) as [[]|], (find_unit (values m) f) as [[]|],
      (find_decision (values m) f); inversion Hnext; now simpl.
Qed.

Lemma next_state_strategy: Strategy ValuesInv next_state.
Proof.
  split.
  - reflexivity.
  - split.
    + intros [|m f] v Hinv Hnext [s' Htrans].
      * inversion Htrans.
      * simpl in Hinv. subst v. apply next_state_values_exists in Htrans as [s'' Hs''].
        rewrite <- next_state_fst, Hnext in Hs''. discriminate.
    + intros [|m f] s' v v' Hinv Hnext.
      * discriminate.
      * split.
        -- apply Relation_Operators.t_step. apply next_state_values_sound.
           simpl in Hinv. subst v. now rewrite <- next_state_fst, Hnext.
        -- now apply next_state_inv with (state m f) v.
Qed.

(* The values of the initial trail. *)
Lemma initial_values_inv: forall (f: CNF), ValuesInv (state ⟨⟩ f) (AtomMap.empty bool).
Proof. reflexivity. Qed.
