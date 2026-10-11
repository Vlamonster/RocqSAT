From Stdlib Require Import List.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
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
From RocqSAT.refinement Require Import Watches.

(* The context of the solver. *)
Record SolverContext: Type := mkContext {
  vals: Values;                (* the values of the trail *)
  cmap: ClauseMap;             (* the clauses of the formula with their literals, by index *)
  lits: list Lit;              (* the literals to decide on, from the first unassigned one *)
  wat: Watches;                (* the two watched literals of each clause *)
  wls: WatchLists;             (* for each literal, the clauses that watch it *)
  todo: list (Lit * list nat); (* false literals with the watchers still to visit *)
  saved: list (list Lit)       (* the literals to decide on before each decision *)
}.

(* The context agrees with the state m f; the saved literals and the watches before each decision are treated
   separately (SavedOK, SavedWatches). *)
Record CoreInv (m: PA) (f: CNF) (x: SolverContext): Prop := {
  core_vals: ValuesOf (vals x) m;
  core_sound: forall (i: nat) (ls: list Lit), tget (cmap x) i = Some ls -> In ls (clause_lists f);
  core_complete: forall (ls: list Lit), In ls (clause_lists f) -> exists (i: nat), tget (cmap x) i = Some ls;
  core_cursor: Cursor (vals x) f (lits x);
  core_struct: WatchStruct (cmap x) (wat x) (wls x) (todo x);
  core_cover: Covered (vals x) (cmap x) (wat x) (todo x)
}.

(* For every decision on m, the saved literals to decide on are those before it. *)
Fixpoint SavedOK (f: CNF) (m: PA) (st: list (list Lit)): Prop :=
match m with
| ⟨⟩     => st = []
| ⟨m, _⟩ => SavedOK f m st
| ⟨m; _⟩ =>
  match st with
  | ls :: st' => Cursor (values m) f ls /\ SavedOK f m st'
  | []        => False
  end
end.

(* The most recent decision on m is the first one saved. *)
Lemma saved_ok_split: forall (f: CNF) (m n: PA) (l: Lit) (st: list (list Lit)),
  NoDecisions n ->
  SavedOK f ⟨m; l ++ n⟩ st ->
  exists (ls: list Lit) (st': list (list Lit)), st = ls :: st' /\ Cursor (values m) f ls /\ SavedOK f m st'.
Proof.
  intros f m n l st. induction n as [|n IH l'|n IH l']; simpl.
  - intros _ Hsaved. destruct st as [|ls st'].
    + contradiction.
    + now exists ls, st'.
  - assumption.
  - intros [].
Qed.

(* At every decision on m, the watches w are fine with respect to the values before it, so a backtrack can keep
   the watches. *)
Fixpoint SavedWatches (cm: ClauseMap) (w: Watches) (m: PA): Prop :=
match m with
| ⟨⟩     => True
| ⟨m, _⟩ => SavedWatches cm w m
| ⟨m; _⟩ => AllWatchOK (values m) cm w /\ SavedWatches cm w m
end.

(* The watches are fine with respect to the values before the most recent decision. *)
Lemma saved_watches_split: forall (cm: ClauseMap) (w: Watches) (m n: PA) (l: Lit),
  NoDecisions n ->
  SavedWatches cm w ⟨m; l ++ n⟩ ->
  AllWatchOK (values m) cm w /\ SavedWatches cm w m.
Proof.
  intros cm w m n l. induction n as [|n IH l'|n IH l']; simpl.
  - intros _ Hsaved. assumption.
  - assumption.
  - intros [].
Qed.

(* The trail before the most recent decision is fresh, and the decision was unassigned in it. *)
Lemma fresh_split: forall (m n: PA) (l: Lit), NoDecisions n -> Fresh ⟨m; l ++ n⟩ -> Fresh m /\ l_eval m l = None.
Proof.
  intros m n l. induction n as [|n IH l'|n IH l']; simpl.
  - intros _ Hfresh. assumption.
  - intros Hno_dec [Hfresh _]. now apply IH.
  - intros [].
Qed.

(* Processing keeps the watches fine with respect to the values before each decision. *)
Lemma saved_watches_process: forall (v: Values) (cm: ClauseMap) (todo todo': list (Lit * list nat))
  (w w': Watches) (wl wl': WatchLists) (m: PA),
  WatchStruct cm w wl todo ->
  process v cm w wl todo = (w', wl', todo') ->
  Fresh m ->
  Incl (values m) v ->
  SavedWatches cm w m -> SavedWatches cm w' m.
Proof.
  intros v cm todo todo' w w' wl wl' m Hstruct Hprocess. induction m as [|m IH l|m IH l]; simpl.
  - easy.
  - intros [Hfresh Hl] Hincl Hsaved. apply IH.
    + assumption.
    + apply (incl_trans (values m) (set_value (values m) l) v).
      * apply incl_set_value.
        -- apply incl_refl.
        -- now rewrite lookup_values.
      * assumption.
    + assumption.
  - intros [Hfresh Hl] Hincl [Hok Hsaved].
    assert (Hincl': Incl (values m) v).
    + apply (incl_trans (values m) (set_value (values m) l) v).
      * apply incl_set_value.
        -- apply incl_refl.
        -- now rewrite lookup_values.
      * assumption.
    + split.
      * now apply (process_watch_ok (values m) v cm todo w w' wl wl' todo').
      * now apply IH.
Qed.

Definition ContextInv (s: State) (x: SolverContext): Prop :=
match s with
| fail      => True
| state m f => CoreInv m f x /\ Fresh m /\ SavedOK f m (saved x) /\ SavedWatches (cmap x) (wat x) m
end.

(* The context after assigning l: ¬l becomes false, so its watchers are taken out of its watch list and become
   pending. *)
Definition assign (x: SolverContext) (l: Lit): SolverContext :=
mkContext (set_value (vals x) l) (cmap x) (lits x) (wat x) (tset (wls x) (lit_key (¬l)) [])
  ((¬l, watching (wls x) (¬l)) :: todo x) (saved x).

(* x with other values, literals to decide on, watches, pending items and saved literals. *)
Definition update (x: SolverContext) (v: Values) (ls: list Lit) (w: Watches) (wl: WatchLists)
  (todo: list (Lit * list nat)) (st: list (list Lit)): SolverContext :=
mkContext v (cmap x) ls w wl todo st.

(* One solver step: visit the pending watchers, repairing their watches; on a clause that cannot be repaired,
   propagate its unit literal, or backtrack (or fail if there is no decision to undo) if it is false; if all
   watches are fine, decide a literal; otherwise stop. *)
Definition next_state (p: State * SolverContext): option (State * SolverContext) :=
match p with
| (fail, _)      => None
| (state m f, x) =>
  match process (vals x) (cmap x) (wat x) (wls x) (todo x) with
  | (w, wl, (q, i :: ws) :: rest) =>
    match tget (cmap x) i with
    | None    => None
    | Some ls =>
      match find (not_false (vals x)) ls with
      (* Unit *)
      | Some u => Some (state ⟨m, u⟩ f, assign (update x (vals x) (lits x) w wl ((q, i :: ws) :: rest) (saved x)) u)
      | None   =>
        match split_last_decision m with
        (* Fail *)
        | None         => Some (fail, update x (vals x) (lits x) w wl ((q, i :: ws) :: rest) (saved x))
        (* Backtrack: unassign the last decision level and restore the literals to decide on; the watches are
           kept, since they are fine with respect to the values before the decision, so the pending clauses
           go back into the watch lists unvisited *)
        | Some (m', l) =>
          match saved x with
          | ls' :: st =>
            Some (state ⟨m', (¬l)⟩ f,
              assign (update x (unassign_level (vals x) m) ls' w (unpend wl ((q, i :: ws) :: rest)) [] st) (¬l))
          | []        => None
          end
        end
      end
    end
  | (_, _, (_, []) :: _) => None
  | (w, wl, []) =>
  (* Decide the first unassigned literal, saving the literals to decide on *)
  match skip_assigned (vals x) (lits x) with
  | l :: ls => Some (state ⟨m; l⟩ f, assign (update x (vals x) (l :: ls) w wl [] ((l :: ls) :: saved x)) l)
  | []      => None
  end
  end
end.

(* What process gives on a consistent context. *)
Lemma process_core: forall (m: PA) (f: CNF) (x: SolverContext) (w: Watches) (wl: WatchLists)
  (todo': list (Lit * list nat)),
  CoreInv m f x ->
  process (vals x) (cmap x) (wat x) (wls x) (todo x) = (w, wl, todo') ->
  CoreInv m f (update x (vals x) (lits x) w wl todo' (saved x)) /\
  (todo' = [] \/ exists (p: Lit) (i: nat) (ws: list nat) (rest: list (Lit * list nat)),
    todo' = (p, i :: ws) :: rest /\ Stuck (vals x) (cmap x) w i).
Proof.
  intros m f x w wl todo' [Hvals Hsound Hcomplete Hlits Hstruct Hcover] Hprocess.
  destruct (process_spec (vals x) (cmap x) (todo x) (wat x) w (wls x) wl todo' Hstruct Hcover Hprocess)
    as (Hstruct' & Hcover' & Hresult). split.
  - now split.
  - assumption.
Qed.

(* A settled clause is not false. *)
Lemma settled_not_false: forall (v: Values) (m: PA) (c: Clause),
  ValuesOf v m -> Settled v (Clause.elements c) -> c_eval m c <> Some false.
Proof.
  intros v m c Hv Hsettled Hc. rewrite c_eval_false_iff in Hc.
  destruct Hsettled as [[l [Hl_in Hl]]|[l1 [_ [Hl1_in [_ [_ [Hl1 _]]]]]]].
  - apply clause_elements_iff, Hc in Hl_in. rewrite Hv in Hl. congruence.
  - apply clause_elements_iff, Hc in Hl1_in. rewrite Hv in Hl1. congruence.
Qed.

Lemma next_state_sound: forall (m: PA) (f: CNF) (x: SolverContext) (s': State) (x': SolverContext),
  ContextInv (state m f) x -> next_state (state m f, x) = Some (s', x') -> state m f ==> s'.
Proof.
  intros m f x s' x' [Hcore _] Hnext. pose proof Hcore as [Hvals Hsound _ Hlits _ _]. unfold next_state in Hnext.
  destruct (process (vals x) (cmap x) (wat x) (wls x) (todo x)) as [[w wl] todo'] eqn:Hprocess.
  destruct (process_core m f x w wl todo' Hcore Hprocess) as [Hcore' Hresult].
  destruct todo' as [|[q [|i ws]] rest].
  (* Decide *)
  - destruct (skip_assigned (vals x) (lits x)) as [|l ls] eqn:Hskip.
    + discriminate.
    + injection Hnext as <- _. apply skip_assigned_cursor in Hlits as [Hls _]. rewrite Hskip in Hls.
      apply skip_assigned_head in Hskip as Hl. rewrite Hvals in Hl. apply (t_step Decide).
      * right. right. now left.
      * apply r_decide.
        -- left. apply Hls. now left.
        -- assumption.
  - discriminate.
  - destruct Hresult as [Hnil|(p & i' & ws' & rest' & Heq & (ls & w1 & w2 & Hc & Hw & Hrepair))].
    + discriminate.
    + injection Heq as <- <- <- <-. rewrite Hc in Hnext.
      destruct Hcore' as [_ _ _ _ Hstruct' _].
      assert (Hunsettled: ~ Settled (vals x) ls).
      * now apply (stuck_unsettled (vals x) (cmap x) w wl ((q, i :: ws) :: rest) i ls w1 w2).
      * apply Hsound, in_clause_lists in Hc as [c [-> Hc_in_f]].
        destruct (find (not_false (vals x)) (Clause.elements c)) as [u|] eqn:Hfind.
        (* Unit *)
        -- injection Hnext as <- _.
           destruct (unsettled_unit (vals x) (Clause.elements c) u Hunsettled Hfind) as (Hu_in & Hu & Hrest).
           apply (t_step Unit).
          ++ right. now left.
          ++ apply (r_unit m f c u).
            ** now apply clause_elements_iff.
            ** assumption.
            ** apply c_eval_false_iff. intros l' Hl'_in. apply Clause.remove_spec in Hl'_in as [Hl'_in_c Hneq].
               rewrite <- Hvals. apply Hrest.
              --- now apply clause_elements_iff.
              --- assumption.
            ** unfold Undef. now rewrite <- Hvals.
        -- assert (Hc_false: c_eval m c = Some false).
          ++ apply c_eval_false_iff. intros l Hl_in. rewrite <- Hvals.
             apply (unsettled_conflict (vals x) (Clause.elements c)).
            ** assumption.
            ** now apply clause_elements_iff.
          ++ destruct (split_last_decision m) as [[m_split l_split]|] eqn:Hsplit.
            (* Backtrack *)
            ** destruct (saved x) as [|ls' st].
              --- discriminate.
              --- injection Hnext as <- _.
                  apply PA.split_last_decision_some_iff in Hsplit as [n_split [-> Hno_dec]].
                  apply (t_step Backtrack).
                +++ right. right. right. now left.
                +++ now apply (r_backtrack m_split n_split f c l_split).
            (* Fail *)
            ** injection Hnext as <- _. apply (t_step Fail).
              --- now left.
              --- apply (r_fail m f c).
                +++ assumption.
                +++ assumption.
                +++ now apply PA.split_last_decision_none_iff.
Qed.

(* next_state only stops at a state without a false clause and without a literal to decide. *)
Lemma next_state_none: forall (m: PA) (f: CNF) (x: SolverContext),
  ContextInv (state m f) x ->
  next_state (state m f, x) = None ->
  (forall (c: Clause), c ∈ f -> c_eval m c <> Some false) /\ (forall (l: Lit), l ∈ f -> ~ Undef m l).
Proof.
  intros m f x (Hcore & _ & Hsaved & _) Hnext. pose proof Hcore as [Hvals _ Hcomplete Hlits _ _].
  unfold next_state in Hnext.
  destruct (process (vals x) (cmap x) (wat x) (wls x) (todo x)) as [[w wl] todo'] eqn:Hprocess.
  destruct (process_core m f x w wl todo' Hcore Hprocess) as [Hcore' Hresult].
  destruct Hcore' as [_ _ _ _ Hstruct' Hcover'].
  destruct Hresult as [->|(p & i & ws & rest & -> & (ls & w1 & w2 & Hc & Hw & Hrepair))].
  - destruct (skip_assigned (vals x) (lits x)) as [|l ls] eqn:Hskip.
    + split.
      * intros c Hc_in_f Hc. apply clause_lists_in in Hc_in_f as [c' [Heq Hin]].
        destruct (Hcomplete _ Hin) as [i Hi]. destruct (tget w i) as [w1 w2] eqn:Hw.
        destruct (Hcover' i _ w1 w2 Hi Hw) as [Hok|[[ws [[] _]]|[ws [[] _]]]].
        apply watch_ok_settled in Hok. apply (settled_not_false (vals x) m c') in Hok.
        -- apply Hok. unfold c_eval.
           rewrite <- (Clause.c_equal_exists _ c c' Heq), <- (Clause.c_equal_forall _ c c' Heq). assumption.
        -- assumption.
      * intros l Hl_in_f Hundef. apply skip_assigned_cursor in Hlits as [_ Hls]. rewrite Hskip in Hls.
        apply (Hls l).
        -- assumption.
        -- now rewrite Hvals.
    + discriminate.
  - rewrite Hc in Hnext. destruct (find (not_false (vals x)) ls) as [u|].
    + discriminate.
    + destruct (split_last_decision m) as [[m' l]|] eqn:Hsplit.
      * destruct (saved x) as [|ls' st] eqn:Hsaved_x.
        -- apply PA.split_last_decision_some_iff in Hsplit as [n [-> Hno_dec]].
           destruct (saved_ok_split f m' n l [] Hno_dec Hsaved) as (ls0 & st & Heq & _).
           discriminate.
        -- discriminate.
      * discriminate.
Qed.

(* The rhs is weaker because there could be multiple { s': State | s ==>[Basic] s' }. *)
Lemma next_state_exists: forall (m: PA) (f: CNF) (x: SolverContext) (s': State),
  ContextInv (state m f) x -> state m f ==>[Basic] s' -> exists (p: State * SolverContext), next_state (state m f, x) = Some p.
Proof.
  intros m f x s' Hinv Htrans. destruct (next_state (state m f, x)) as [p|] eqn:Hnext.
  - now exists p.
  - exfalso. destruct (next_state_none m f x Hinv Hnext) as [Hno_conflict Hno_decision].
    inversion Htrans as [r ? ? s'' Hr Hstep]; subst.
    destruct Hr as [<-|[<-|[<-|[]]]].
    (* Fail *)
    + inversion Hstep as [? ? c Hc_in_f Hc Hno_dec]; subst. now apply (Hno_conflict c).
    (* Decide *)
    + inversion Hstep as [? ? l Hl_in_f Hundef]; subst.
      destruct Hl_in_f as [Hl_in_f|Hnegl_in_f].
      * now apply (Hno_decision l).
      * apply (Hno_decision (¬l)).
        -- assumption.
        -- now apply l_eval_neg_none_iff in Hundef.
    (* Backtrack *)
    + inversion Hstep as [m_split n_split ? c l_split Hc_in_f Hc Hno_dec]; subst. now apply (Hno_conflict c).
Qed.

(* Assigning an unassigned literal l keeps the context consistent: only the watchers of ¬l can stop being
   fine, and they all become pending. *)
Lemma assign_inv: forall (m m': PA) (f: CNF) (x: SolverContext) (l: Lit),
  CoreInv m f x ->
  (forall (y: Lit), l_eval m' y = l_eval_step y l (l_eval m y)) ->
  lookup (vals x) l = None ->
  CoreInv m' f (assign x l).
Proof.
  intros m m' f x l [Hvals Hsound Hcomplete Hlits Hstruct Hcover] Hvalues Hl.
  (* Every watcher of a literal stays in its watch list or becomes pending *)
  assert (Hholds: forall (i: nat) (y: Lit), Watched (wls x) (todo x) i y ->
    Watched (tset (wls x) (lit_key (¬l)) []) ((¬l, watching (wls x) (¬l)) :: todo x) i y).
  - intros i y [Hin|Hpend].
    + unfold Watched. rewrite watching_add. destruct (Lit.eq_dec (¬l) y) as [<-|Hneq].
      * right. apply pending_cons. left. now split.
      * now left.
    + right. apply pending_cons. now right.
  - split.
    + intros y. simpl. now rewrite lookup_add, Hvals, Hvalues.
    + assumption.
    + assumption.
    + now apply cursor_set_value.
    + intros i ls w1 w2 Hi Hw. destruct (Hstruct i ls w1 w2 Hi Hw) as (Hin1 & Hin2 & Hmembers). split.
      * now apply Hholds.
      * split.
        -- now apply Hholds.
        -- assumption.
    + intros i ls w1 w2 Hi Hw. destruct (Hcover i ls w1 w2 Hi Hw) as [Hok|[Hpend1|Hpend2]].
      * destruct (Hstruct i ls w1 w2 Hi Hw) as (Hin1 & Hin2 & _). destruct (Lit.eq_dec w1 (¬l)) as [->|Hneq1].
        -- right. left. apply pending_cons. destruct Hin1 as [Hin1|Hpend1].
          ++ left. now split.
          ++ now right.
        -- destruct (Lit.eq_dec w2 (¬l)) as [->|Hneq2].
          ++ right. right. apply pending_cons. destruct Hin2 as [Hin2|Hpend2].
            ** left. now split.
            ** now right.
          ++ left. simpl. now apply watch_ok_cons.
      * right. left. apply pending_cons. now right.
      * right. right. apply pending_cons. now right.
Qed.

(* next_state keeps the context consistent. *)
Lemma next_state_inv: forall (s s': State) (x x': SolverContext),
  ContextInv s x -> next_state (s, x) = Some (s', x') -> ContextInv s' x'.
Proof.
  intros [|m f] s' x x' Hinv Hnext.
  - discriminate.
  - destruct Hinv as (Hcore & Hfresh & Hsaved & Hwatches).
    pose proof Hcore as [Hvals Hsound Hcomplete Hlits Hstruct _].
    unfold next_state in Hnext.
    destruct (process (vals x) (cmap x) (wat x) (wls x) (todo x)) as [[w wl] todo'] eqn:Hprocess.
    destruct (process_core m f x w wl todo' Hcore Hprocess) as [Hcore' Hresult].
    (* The values before each decision are included in the current ones *)
    assert (Hwatches': SavedWatches (cmap x) w m).
    + apply (saved_watches_process (vals x) (cmap x) (todo x) todo' (wat x) w (wls x) wl m).
      * assumption.
      * assumption.
      * assumption.
      * intros y b Hy. rewrite lookup_values in Hy. now rewrite Hvals.
      * assumption.
    + destruct todo' as [|[q [|i ws]] rest].
      (* Decide *)
      * destruct (skip_assigned (vals x) (lits x)) as [|l ls] eqn:Hskip.
        -- discriminate.
        -- injection Hnext as <- <-. apply skip_assigned_cursor in Hlits. rewrite Hskip in Hlits.
           apply skip_assigned_head in Hskip as Hl.
           destruct Hcore' as [_ _ _ _ Hstruct' Hcover'].
           (* The values of m, saved implicitly for the decision *)
           assert (Hext: forall (y: Lit), lookup (vals x) y = lookup (values m) y).
          ++ intros y. now rewrite lookup_values, Hvals.
          ++ split.
            ** apply (assign_inv m ⟨m; l⟩ f (update x (vals x) (l :: ls) w wl [] ((l :: ls) :: saved x)) l).
              --- now split.
              --- intros y. reflexivity.
              --- assumption.
            ** split.
              --- split.
                +++ assumption.
                +++ now rewrite <- Hvals.
              --- split.
                +++ simpl. split.
                  *** now apply (cursor_ext (vals x)).
                  *** assumption.
                (* All watches are fine before the decision *)
                +++ simpl. split.
                  *** intros j ls' w1 w2 Hj Hwj.
                      destruct (Hcover' j ls' w1 w2 Hj Hwj) as [Hok|[[ws [[] _]]|[ws [[] _]]]].
                      now apply (watch_ok_ext (vals x)).
                  *** assumption.
      * discriminate.
      * destruct Hresult as [Hnil|(p & i' & ws' & rest' & Heq & (ls & w1 & w2 & Hc & Hw & Hrepair))].
        -- discriminate.
        -- injection Heq as <- <- <- <-. rewrite Hc in Hnext. pose proof Hcore' as [_ _ _ _ Hstruct' _].
           assert (Hunsettled: ~ Settled (vals x) ls).
          ++ now apply (stuck_unsettled (vals x) (cmap x) w wl ((q, i :: ws) :: rest) i ls w1 w2).
          ++ destruct (find (not_false (vals x)) ls) as [u|] eqn:Hfind.
            (* Unit *)
            ** injection Hnext as <- <-.
               destruct (unsettled_unit (vals x) ls u Hunsettled Hfind) as (_ & Hu & _). split.
              --- apply (assign_inv m ⟨m, u⟩ f (update x (vals x) (lits x) w wl ((q, i :: ws) :: rest) (saved x)) u).
                +++ assumption.
                +++ intros y. reflexivity.
                +++ assumption.
              --- split.
                +++ split.
                  *** assumption.
                  *** now rewrite <- Hvals.
                +++ now split.
            ** destruct (split_last_decision m) as [[m' l]|] eqn:Hsplit.
              (* Backtrack: the values of m' and the watches, which are fine with respect to them *)
              --- assert (Hvals': ValuesOf (unassign_level (vals x) m) m').
                +++ now apply (unassign_level_spec (vals x) m m' l).
                +++ apply PA.split_last_decision_some_iff in Hsplit as [n [-> Hno_dec]].
                    destruct (saved_ok_split f m' n l (saved x) Hno_dec Hsaved) as (ls' & st & Hsaved_x & Hls' & Hsaved').
                    destruct (saved_watches_split (cmap x) w m' n l Hno_dec Hwatches') as [Hok' Hwatches''].
                    destruct (fresh_split m' n l Hno_dec Hfresh) as [Hfresh' Hl].
                    rewrite Hsaved_x in Hnext. injection Hnext as <- <-.
                    assert (Hext: forall (y: Lit),
                      lookup (values m') y = lookup (unassign_level (vals x) ⟨m'; l ++ n⟩) y).
                  *** intros y. now rewrite lookup_values, Hvals'.
                  *** split.
                    ---- apply (assign_inv m' ⟨m', (¬l)⟩ f
                           (update x (unassign_level (vals x) ⟨m'; l ++ n⟩) ls' w (unpend wl ((q, i :: ws) :: rest)) [] st)
                           (¬l)).
                      ++++ split.
                        **** assumption.
                        **** assumption.
                        **** assumption.
                        **** now apply (cursor_ext (values m')).
                        **** now apply unpend_struct.
                        **** intros j ls'' w1' w2' Hj Hwj. left. apply (watch_ok_ext (values m')).
                          ----- assumption.
                          ----- now apply (Hok' j ls'').
                      ++++ intros y. reflexivity.
                      ++++ simpl. rewrite Hvals'. now apply l_eval_neg_none_iff in Hl.
                    ---- split.
                      ++++ split.
                        **** assumption.
                        **** now apply l_eval_neg_none_iff in Hl.
                      ++++ now split.
              (* Fail *)
              --- injection Hnext as <- <-. now simpl.
Qed.

Lemma next_state_strategy: Strategy ContextInv next_state.
Proof.
  split.
  - reflexivity.
  - split.
    + intros [|m f] x Hinv Hnext [s' Htrans].
      * inversion Htrans.
      * destruct (next_state_exists m f x s' Hinv Htrans) as [p Hp]. congruence.
    + intros [|m f] s' x x' Hinv Hnext.
      * discriminate.
      * split.
        -- apply Relation_Operators.t_step. now apply next_state_sound with x x'.
        -- now apply next_state_inv with (state m f) x.
Qed.

(* The context of the initial state: no values, and the clauses indexed with their first literals watched and
   each pending once. *)
Definition initial_context (f: CNF): SolverContext :=
match index_clauses 0 (clause_lists f) (tmake None) (tmake (Pos 0, Pos 0)) (tmake []) [] with
| (cm, w, wl, todo) =>
  mkContext (tmake None) cm (Clause.elements (formula_lits f)) w wl todo []
end.

Lemma initial_context_inv: forall (f: CNF), ContextInv (state ⟨⟩ f) (initial_context f).
Proof.
  intros f. unfold initial_context.
  destruct (index_clauses 0 (clause_lists f) (tmake None) (tmake (Pos 0, Pos 0)) (tmake []) [])
    as [[[cm w] wl] todo] eqn:Hindex.
  destruct (index_clauses_spec (clause_lists f) 0 (tmake None) cm (tmake (Pos 0, Pos 0)) w (tmake []) wl [] todo)
    as (Hstruct & Hpending & Hsound & Hcomplete & _).
  - intros i ls Hi. now rewrite tget_tmake in Hi.
  - intros i ls w1 w2 Hi. now rewrite tget_tmake in Hi.
  - intros i ls w1 w2 Hi. now rewrite tget_tmake in Hi.
  - assumption.
  - split.
    + split.
      * intros l. reflexivity.
      * intros i ls Hi. apply Hsound in Hi as [Hi|Hin].
        -- now rewrite tget_tmake in Hi.
        -- assumption.
      * assumption.
      * split.
        -- intros l Hl. simpl in Hl. now rewrite clause_elements_iff, formula_lits_spec in Hl.
        -- intros l Hl_in_f _. simpl. now rewrite clause_elements_iff, formula_lits_spec.
      * assumption.
      * intros i ls w1 w2 Hi Hw. right. left. now apply (Hpending i ls w1 w2).
    + split.
      * easy.
      * split.
        -- reflexivity.
        -- easy.
Qed.
