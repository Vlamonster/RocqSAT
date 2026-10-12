From Stdlib Require Import List.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import Model.
From RocqSAT Require Import State.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import Entails.
From RocqSAT Require Import Trans.
From RocqSAT Require Import Strategy.
From RocqSAT.rules Require Import Fail.
From RocqSAT.rules Require Import Unit.
From RocqSAT.rules Require Import Decide.
From RocqSAT.rules Require Import Backtrack.
From RocqSAT.rules Require Import Backjump.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Search.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import Analysis.

(* The context of the solver. *)
Record SolverContext: Type := mkContext {
  vals: Values;                (* the values of the trail *)
  cmap: ClauseMap;             (* the clauses of the formula with their literals, by index *)
  lits: list Lit;              (* the literals to decide on, from the first unassigned one *)
  wat: Watches;                (* the two watched literals of each clause *)
  wls: WatchLists;             (* for each literal, the clauses that watch it *)
  todo: list (Lit * list nat); (* false literals with the watchers still to visit *)
  saved: list (list Lit);      (* the literals to decide on before each decision *)
  rsn: Table nat;              (* hint: S i if clause i propagated the atom, 0 if nothing did *)
  lvl: Table nat;              (* hint: the decision level at which the atom was assigned *)
  dl: nat;                     (* hint: the current decision level *)
  mrk: Table bool;             (* marks of literals by lit_key, used by the analysis and cleared after it *)
  phs: Values                  (* hint: the value each atom last had, used to decide *)
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

(* The number of decisions on m. *)
Fixpoint decisions (m: PA): nat :=
match m with
| ⟨⟩     => 0
| ⟨m, _⟩ => decisions m
| ⟨m; _⟩ => S (decisions m)
end.

Lemma no_decisions_zero: forall (m: PA), NoDecisions m -> decisions m = 0.
Proof.
  intros m. induction m as [|m IH l|m IH l]; simpl.
  - reflexivity.
  - assumption.
  - intros [].
Qed.

(* The decision l of ⟨m; l ++ n⟩ is saved after those of n. *)
Lemma saved_ok_split: forall (f: CNF) (m n: PA) (l: Lit) (st: list (list Lit)),
  SavedOK f ⟨m; l ++ n⟩ st ->
  exists (ls: list Lit) (st': list (list Lit)),
    skipn (decisions n) st = ls :: st' /\ Cursor (values m) f ls /\ SavedOK f m st'.
Proof.
  intros f m n l. induction n as [|n IH l'|n IH l']; simpl; intros st Hsaved.
  - destruct st as [|ls st'].
    + contradiction.
    + now exists ls, st'.
  - now apply IH.
  - destruct st as [|ls st'].
    + contradiction.
    + destruct Hsaved as [_ Hsaved]. now apply IH.
Qed.

(* At every decision on m, the watches w are fine with respect to the values before it, so a backtrack can keep
   the watches. *)
Fixpoint SavedWatches (cm: ClauseMap) (w: Watches) (m: PA): Prop :=
match m with
| ⟨⟩     => True
| ⟨m, _⟩ => SavedWatches cm w m
| ⟨m; _⟩ => AllWatchOK (values m) cm w /\ SavedWatches cm w m
end.

(* The watches are fine with respect to the values before the decision l of ⟨m; l ++ n⟩. *)
Lemma saved_watches_split: forall (cm: ClauseMap) (w: Watches) (m n: PA) (l: Lit),
  SavedWatches cm w ⟨m; l ++ n⟩ -> AllWatchOK (values m) cm w /\ SavedWatches cm w m.
Proof.
  intros cm w m n l. induction n as [|n IH l'|n IH l']; simpl.
  - intros Hsaved. assumption.
  - assumption.
  - intros [_ Hsaved]. now apply IH.
Qed.

(* The trail before the decision l of ⟨m; l ++ n⟩ is fresh, and l was unassigned in it. *)
Lemma fresh_split: forall (m n: PA) (l: Lit), Fresh ⟨m; l ++ n⟩ -> Fresh m /\ l_eval m l = None.
Proof.
  intros m n l. induction n as [|n IH l'|n IH l']; simpl.
  - intros Hfresh. assumption.
  - intros [Hfresh _]. now apply IH.
  - intros [Hfresh _]. now apply IH.
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

(* The context agrees with the state. *)
Definition ContextCore (s: State) (x: SolverContext): Prop :=
match s with
| fail      => True
| state m f => CoreInv m f x /\ Fresh m /\ SavedOK f m (saved x) /\ SavedWatches (cmap x) (wat x) m /\ Unmarked (mrk x)
end.

(* Moreover the state is well-formed and entailed, as every reachable state is; a backtrack relies on this to be
   a backjump (backtrack_backjump). *)
Definition ContextInv (s: State) (x: SolverContext): Prop :=
ContextCore s x /\
match s with
| fail      => True
| state m f => WellFormed (state m f) /\ Entails f m
end.

(* The context after assigning l with reason r at the current level: ¬l becomes false, so its watchers are taken
   out of its watch list and become pending; l is also the new phase of its atom. *)
Definition assign (x: SolverContext) (l: Lit) (r: nat): SolverContext :=
mkContext (set_value (vals x) l) (cmap x) (lits x) (wat x) (tset (wls x) (lit_key (¬l)) [])
  ((¬l, watching (wls x) (¬l)) :: todo x) (saved x) (tset (rsn x) (extract l) r) (tset (lvl x) (extract l) (dl x))
  (dl x) (mrk x) (set_value (phs x) l).

(* x with other values, literals to decide on, watches, pending items, saved literals and decision level. *)
Definition update (x: SolverContext) (v: Values) (ls: list Lit) (w: Watches) (wl: WatchLists)
  (todo: list (Lit * list nat)) (st: list (list Lit)) (d: nat): SolverContext :=
mkContext v (cmap x) ls w wl todo st (rsn x) (lvl x) d (mrk x) (phs x).

(* x with other marks. *)
Definition with_marks (x: SolverContext) (mk: Table bool): SolverContext :=
mkContext (vals x) (cmap x) (lits x) (wat x) (wls x) (todo x) (saved x) (rsn x) (lvl x) (dl x) mk (phs x).

(* One solver step: visit the pending watchers, repairing their watches; on a clause that cannot be repaired,
   propagate its unit literal, or backjump (or fail if there is no decision to undo) if it is false; if all
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
      | Some u =>
        Some (state ⟨m, u⟩ f,
          assign (update x (vals x) (lits x) w wl ((q, i :: ws) :: rest) (saved x) (dl x)) u (S i))
      | None   =>
        match split_last_decision m with
        (* Fail *)
        | None         => Some (fail, update x (vals x) (lits x) w wl ((q, i :: ws) :: rest) (saved x) (dl x))
        | Some (m', l) =>
          (* Analyse the conflict, marking the literals of the clause, mark all of the result for the plan, and
             clear the marks afterwards *)
          match analyze (cmap x) (rsn x) (lvl x) (dl x) m (set_marks (mrk x) ls true) ls (count_level (lvl x) (dl x) ls) with
          | (c, mk) =>
            match plan (vals x) (lvl x) (dl x) m (set_marks mk c true) c with
            (* Backjump: unassign the levels from the decision d on and restore the literals to decide on; the
               watches are kept, since they are fine with respect to the values before d, so the pending clauses
               go back into the watch lists unvisited *)
            | Some (u, (mt, d, n)) =>
              match skipn (decisions n) (saved x) with
              | ls' :: st =>
                Some (state ⟨mt, u⟩ f,
                  assign (with_marks (update x (unassign_segment (vals x) d n) ls' w (unpend wl ((q, i :: ws) :: rest)) []
                    st (dl x - S (decisions n))) (set_marks (set_marks mk c true) c false)) u 0)
              | []        => None
              end
            (* Otherwise the last decision is flipped, in the same way *)
            | None =>
              match saved x with
              | ls' :: st =>
                Some (state ⟨m', (¬l)⟩ f,
                  assign (with_marks (update x (unassign_level (vals x) m) ls' w (unpend wl ((q, i :: ws) :: rest)) [] st
                    (dl x - 1)) (set_marks (set_marks mk c true) c false)) (¬l) 0)
              | []        => None
              end
            end
          end
        end
      end
    end
  | (_, _, (_, []) :: _) => None
  | (w, wl, []) =>
  (* Decide the first unassigned atom with its phase, saving the literals to decide on *)
  match skip_assigned (vals x) (lits x) with
  | l :: ls =>
    Some (state ⟨m; (phase (phs x) l)⟩ f,
      assign (update x (vals x) (l :: ls) w wl [] ((l :: ls) :: saved x) (S (dl x))) (phase (phs x) l) 0)
  | []      => None
  end
  end
end.

(* What process gives on a consistent context. *)
Lemma process_core: forall (m: PA) (f: CNF) (x: SolverContext) (w: Watches) (wl: WatchLists)
  (todo': list (Lit * list nat)),
  CoreInv m f x ->
  process (vals x) (cmap x) (wat x) (wls x) (todo x) = (w, wl, todo') ->
  CoreInv m f (update x (vals x) (lits x) w wl todo' (saved x) (dl x)) /\
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

(* Assigning an unassigned literal l keeps the context consistent: only the watchers of ¬l can stop being
   fine, and they all become pending. *)
Lemma assign_inv: forall (m m': PA) (f: CNF) (x: SolverContext) (l: Lit) (r: nat),
  CoreInv m f x ->
  (forall (y: Lit), l_eval m' y = l_eval_step y l (l_eval m y)) ->
  lookup (vals x) l = None ->
  CoreInv m' f (assign x l r).
Proof.
  intros m m' f x l r [Hvals Hsound Hcomplete Hlits Hstruct Hcover] Hvalues Hl.
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

(* Every clause of the clause table follows from f, and hence so does the analysed clause of a conflict. *)
Lemma core_entailed: forall (m: PA) (f: CNF) (x: SolverContext) (i: nat) (ls: list Lit),
  CoreInv m f x -> tget (cmap x) i = Some ls -> Entailed f ls.
Proof. intros m f x i ls [_ Hsound _ _ _ _] Hi. apply entailed_clause_lists. now apply Hsound with i. Qed.

Lemma next_state_sound: forall (m: PA) (f: CNF) (x: SolverContext) (s': State) (x': SolverContext),
  ContextInv (state m f) x -> next_state (state m f, x) = Some (s', x') -> state m f ==>[DPLL_BJ] s'.
Proof.
  intros m f x s' x' [(Hcore & Hfresh & _ & _ & Hmarks) [Hwf Hentails]] Hnext. pose proof Hcore as [Hvals Hsound _ Hlits _ _].
  unfold next_state in Hnext.
  destruct (process (vals x) (cmap x) (wat x) (wls x) (todo x)) as [[w wl] todo'] eqn:Hprocess.
  destruct (process_core m f x w wl todo' Hcore Hprocess) as [Hcore' Hresult].
  destruct todo' as [|[q [|i ws]] rest].
  (* Decide *)
  - destruct (skip_assigned (vals x) (lits x)) as [|l ls] eqn:Hskip.
    + discriminate.
    + injection Hnext as <- _. apply skip_assigned_cursor in Hlits as [Hls _]. rewrite Hskip in Hls.
      apply skip_assigned_head, (phase_undef _ (phs x)) in Hskip as Hl. rewrite Hvals in Hl.
      apply (t_step Decide).
      * right. right. now left.
      * apply r_decide.
        -- apply phase_in, Hls. now left.
        -- assumption.
  - discriminate.
  - destruct Hresult as [Hnil|(p & i' & ws' & rest' & Heq & (ls & w1 & w2 & Hc & Hw & Hrepair))].
    + discriminate.
    + injection Heq as <- <- <- <-. rewrite Hc in Hnext.
      destruct Hcore' as [_ _ _ _ Hstruct' _].
      assert (Hunsettled: ~ Settled (vals x) ls).
      * now apply (stuck_unsettled (vals x) (cmap x) w wl ((q, i :: ws) :: rest) i ls w1 w2).
      * assert (Hls: Entailed f ls).
        -- now apply (core_entailed m f x i).
        -- apply Hsound, in_clause_lists in Hc as [c [-> Hc_in_f]].
           destruct (find (not_false (vals x)) (Clause.elements c)) as [u|] eqn:Hfind.
           (* Unit *)
           ++ injection Hnext as <- _.
              destruct (unsettled_unit (vals x) (Clause.elements c) u Hunsettled Hfind) as (Hu_in & Hu & Hrest).
              apply (t_step Unit).
              ** right. now left.
              ** apply (r_unit m f c u).
                 --- now apply clause_elements_iff.
                 --- assumption.
                 --- apply c_eval_false_iff. intros l' Hl'_in. apply Clause.remove_spec in Hl'_in as [Hl'_in_c Hneq].
                     rewrite <- Hvals. apply Hrest.
                     +++ now apply clause_elements_iff.
                     +++ assumption.
                 --- unfold Undef. now rewrite <- Hvals.
           ++ assert (Hc_false: c_eval m c = Some false).
              ** apply c_eval_false_iff. intros l Hl_in. rewrite <- Hvals.
                 apply (unsettled_conflict (vals x) (Clause.elements c)).
                 --- assumption.
                 --- now apply clause_elements_iff.
              ** destruct (split_last_decision m) as [[m_split l_split]|] eqn:Hsplit.
                 --- destruct (analyze (cmap x) (rsn x) (lvl x) (dl x) m (set_marks (mrk x) (Clause.elements c) true)
                       (Clause.elements c) (count_level (lvl x) (dl x) (Clause.elements c))) as [c' mk] eqn:Hanalyze.
                     destruct (analyze_spec f (cmap x) (rsn x) (lvl x) (dl x) m _ mk (Clause.elements c) c' _
                       (fun (j: nat) (r: list Lit) (Hj: tget (cmap x) j = Some r) => core_entailed m f x j r Hcore Hj)
                       Hls (set_marks_marked_in (mrk x) (Clause.elements c) Hmarks) Hanalyze) as [Hc' _].
                     destruct (plan (vals x) (lvl x) (dl x) m (set_marks mk c' true) c') as [[u [[mt d] n]]|] eqn:Hplan.
                     (* Backjump *)
                     +++ destruct (skipn (decisions n) (saved x)) as [|ls' st].
                         *** discriminate.
                         *** injection Hnext as <- _.
                             destruct (plan_spec (vals x) (lvl x) (dl x) m mt n _ _ u d Hvals Hfresh (set_marks_in _ _ true) Hplan)
                               as (Hm & Hu_in & Hu_false & Hu & Hrest).
                             apply (t_step Backjump).
                             ---- right. right. right. now left.
                             ---- rewrite Hm. apply (r_backjump mt n f c (clause_of c') d u).
                                  ++++ assumption.
                                  ++++ now rewrite <- Hm.
                                  ++++ now apply entailed_consequence.
                                  ++++ now apply clause_of_spec.
                                  ++++ apply c_eval_false_iff. intros y Hy. apply Clause.remove_spec in Hy as [Hy Hneq].
                                       apply clause_of_spec in Hy. now apply Hrest.
                                  ++++ assumption.
                                  ++++ destruct Hwf as [_ Hbounded]. apply l_eval_false_in, Hbounded in Hu_false.
                                       rewrite Neg.involutive in Hu_false. now apply or_comm.
                     (* Otherwise a backtrack, which is a backjump *)
                     +++ destruct (saved x) as [|ls' st].
                         *** discriminate.
                         *** injection Hnext as <- _. apply (t_step Backjump).
                             ---- right. right. right. now left.
                             ---- apply backtrack_backjump.
                                  ++++ assumption.
                                  ++++ assumption.
                                  ++++ apply PA.split_last_decision_some_iff in Hsplit as [n_split [-> Hno_dec]].
                                       now apply (r_backtrack m_split n_split f c l_split).
                 (* Fail *)
                 --- injection Hnext as <- _. apply (t_step Fail).
                     +++ now left.
                     +++ apply (r_fail m f c).
                         *** assumption.
                         *** assumption.
                         *** now apply PA.split_last_decision_none_iff.
Qed.

(* next_state only stops at a state without a false clause and without a literal to decide. *)
Lemma next_state_none: forall (m: PA) (f: CNF) (x: SolverContext),
  ContextInv (state m f) x ->
  next_state (state m f, x) = None ->
  (forall (c: Clause), c ∈ f -> c_eval m c <> Some false) /\ (forall (l: Lit), l ∈ f -> ~ Undef m l).
Proof.
  intros m f x [(Hcore & Hfresh & Hsaved & _) _] Hnext. pose proof Hcore as [Hvals _ Hcomplete Hlits _ _].
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
      * destruct (analyze (cmap x) (rsn x) (lvl x) (dl x) m (set_marks (mrk x) ls true) ls (count_level (lvl x) (dl x) ls))
          as [c mk].
        destruct (plan (vals x) (lvl x) (dl x) m (set_marks mk c true) c) as [[u [[mt d] n]]|] eqn:Hplan.
        -- destruct (skipn (decisions n) (saved x)) as [|ls' st] eqn:Hskip.
           ++ destruct (plan_spec (vals x) (lvl x) (dl x) m mt n _ _ u d Hvals Hfresh (set_marks_in _ _ true) Hplan) as (-> & _).
              destruct (saved_ok_split f mt n d (saved x) Hsaved) as (ls0 & st0 & Heq & _). congruence.
           ++ discriminate.
        -- destruct (saved x) as [|ls' st] eqn:Hsaved_x.
           ++ apply PA.split_last_decision_some_iff in Hsplit as [n [-> Hno_dec]].
              destruct (saved_ok_split f m' n l [] Hsaved) as (ls0 & st & Heq & _).
              rewrite no_decisions_zero in Heq.
              ** discriminate.
              ** assumption.
           ++ discriminate.
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

(* The marks do not matter for CoreInv. *)
Lemma core_with_marks: forall (m: PA) (f: CNF) (x: SolverContext) (mk: Table bool),
  CoreInv m f x -> CoreInv m f (with_marks x mk).
Proof. intros m f x mk [Hvals Hsound Hcomplete Hlits Hstruct Hcover]. now split. Qed.

(* After a backjump or backtrack to before the decision d of ⟨mt; d ++ n⟩, the context agrees with mt: the
   watches w were fine with respect to its values. *)
Lemma jump_core: forall (mt n: PA) (f: CNF) (x: SolverContext) (d: Lit) (v': Values) (w: Watches)
  (wl: WatchLists) (todo': list (Lit * list nat)) (ls': list Lit) (st: list (list Lit)) (k: nat),
  CoreInv ⟨mt; d ++ n⟩ f (update x (vals x) (lits x) w wl todo' (saved x) (dl x)) ->
  ValuesOf v' mt ->
  Cursor (values mt) f ls' ->
  AllWatchOK (values mt) (cmap x) w ->
  CoreInv mt f (update x v' ls' w (unpend wl todo') [] st k).
Proof.
  intros mt n f x d v' w wl todo' ls' st k [_ Hsound Hcomplete _ Hstruct _] Hvals' Hls' Hok'.
  assert (Hext: forall (y: Lit), lookup (values mt) y = lookup v' y).
  - intros y. now rewrite lookup_values, Hvals'.
  - split.
    + assumption.
    + assumption.
    + assumption.
    + now apply (cursor_ext (values mt)).
    + now apply unpend_struct.
    + intros j ls w1 w2 Hj Hwj. left. apply (watch_ok_ext (values mt)).
      * assumption.
      * now apply (Hok' j ls).
Qed.

(* next_state keeps the context in agreement with the state. *)
Lemma next_state_core: forall (s s': State) (x x': SolverContext),
  ContextCore s x -> next_state (s, x) = Some (s', x') -> ContextCore s' x'.
Proof.
  intros [|m f] s' x x' Hinv Hnext.
  - discriminate.
  - destruct Hinv as (Hcore & Hfresh & Hsaved & Hwatches & Hmarks).
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
           apply skip_assigned_head, (phase_undef _ (phs x)) in Hskip as Hl.
           destruct Hcore' as [_ _ _ _ Hstruct' Hcover'].
           split.
           ++ apply (assign_inv m ⟨m; (phase (phs x) l)⟩ f
                (update x (vals x) (l :: ls) w wl [] ((l :: ls) :: saved x) (S (dl x))) (phase (phs x) l)).
              ** now split.
              ** intros y. reflexivity.
              ** assumption.
           ++ split.
              ** split.
                 --- assumption.
                 --- now rewrite <- Hvals.
              ** split.
                 --- simpl. split.
                     +++ apply (cursor_ext (vals x)).
                         *** intros y. now rewrite lookup_values, Hvals.
                         *** assumption.
                     +++ assumption.
                 --- split.
                     (* All watches are fine before the decision *)
                     +++ simpl. split.
                         *** intros j ls' w1 w2 Hj Hwj.
                             destruct (Hcover' j ls' w1 w2 Hj Hwj) as [Hok|[[ws [[] _]]|[ws [[] _]]]].
                             apply (watch_ok_ext (vals x)).
                             ---- intros y. now rewrite lookup_values, Hvals.
                             ---- assumption.
                         *** assumption.
                     +++ assumption.
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
                 --- apply (assign_inv m ⟨m, u⟩ f
                       (update x (vals x) (lits x) w wl ((q, i :: ws) :: rest) (saved x) (dl x)) u).
                     +++ assumption.
                     +++ intros y. reflexivity.
                     +++ assumption.
                 --- split.
                     +++ split.
                         *** assumption.
                         *** now rewrite <- Hvals.
                     +++ now repeat split.
              ** destruct (split_last_decision m) as [[m' l]|] eqn:Hsplit.
                 --- destruct (analyze (cmap x) (rsn x) (lvl x) (dl x) m (set_marks (mrk x) ls true) ls
                       (count_level (lvl x) (dl x) ls)) as [c mk] eqn:Hanalyze.
                     destruct (analyze_spec f (cmap x) (rsn x) (lvl x) (dl x) m _ mk ls c _
                       (fun (j: nat) (r: list Lit) (Hj: tget (cmap x) j = Some r) => core_entailed m f x j r Hcore Hj)
                       (core_entailed m f x i ls Hcore Hc) (set_marks_marked_in (mrk x) ls Hmarks) Hanalyze) as [_ Hmk].
                     destruct (plan (vals x) (lvl x) (dl x) m (set_marks mk c true) c) as [[u [[mt d] n]]|] eqn:Hplan.
                     (* Backjump *)
                     +++ destruct (plan_spec (vals x) (lvl x) (dl x) m mt n _ _ u d Hvals Hfresh (set_marks_in _ _ true) Hplan)
                           as (-> & _ & _ & Hu & _).
                         destruct (saved_ok_split f mt n d (saved x) Hsaved) as (ls' & st & Hskip & Hls' & Hsaved').
                         destruct (saved_watches_split (cmap x) w mt n d Hwatches') as [Hok' Hwatches''].
                         destruct (fresh_split mt n d Hfresh) as [Hfresh' _].
                         assert (Hvals': ValuesOf (unassign_segment (vals x) d n) mt).
                         *** now apply unassign_segment_spec.
                         *** rewrite Hskip in Hnext. injection Hnext as <- <-. split.
                             ---- apply (assign_inv mt ⟨mt, u⟩ f).
                                  ++++ apply core_with_marks. now apply (jump_core mt n f x d _ w wl ((q, i :: ws) :: rest)).
                                  ++++ intros y. reflexivity.
                                  ++++ simpl. now rewrite Hvals'.
                             ---- split.
                                  ++++ now split.
                                  ++++ split.
                                       **** assumption.
                                       **** split.
                                            ----- assumption.
                                            ----- now apply set_marks_unmarked, set_marks_true_marked_in.
                     (* Backtrack: the values of m' and the watches, which are fine with respect to them *)
                     +++ apply PA.split_last_decision_some_iff in Hsplit as [n [-> Hno_dec]].
                         destruct (saved_ok_split f m' n l (saved x) Hsaved) as (ls' & st & Hsaved_x & Hls' & Hsaved').
                         rewrite no_decisions_zero in Hsaved_x.
                         2: assumption.
                         destruct (saved_watches_split (cmap x) w m' n l Hwatches') as [Hok' Hwatches''].
                         destruct (fresh_split m' n l Hfresh) as [Hfresh' Hl].
                         assert (Hvals': ValuesOf (unassign_level (vals x) ⟨m'; l ++ n⟩) m').
                         *** apply (unassign_level_spec (vals x) ⟨m'; l ++ n⟩ m' l).
                             ---- assumption.
                             ---- assumption.
                             ---- apply PA.split_last_decision_some_iff. now exists n.
                         *** simpl in Hsaved_x. rewrite Hsaved_x in Hnext. injection Hnext as <- <-. split.
                             ---- apply (assign_inv m' ⟨m', (¬l)⟩ f).
                                  ++++ apply core_with_marks. now apply (jump_core m' n f x l _ w wl ((q, i :: ws) :: rest)).
                                  ++++ intros y. reflexivity.
                                  ++++ simpl. rewrite Hvals'. now apply l_eval_neg_none_iff in Hl.
                             ---- split.
                                  ++++ split.
                                       **** assumption.
                                       **** now apply l_eval_neg_none_iff in Hl.
                                  ++++ split.
                                       **** assumption.
                                       **** split.
                                            ----- assumption.
                                            ----- now apply set_marks_unmarked, set_marks_true_marked_in.
                 (* Fail *)
                 --- injection Hnext as <- <-. now simpl.
Qed.

(* next_state keeps the context consistent: the new state is reached by a transition, so it is well-formed and
   entailed as well. *)
Lemma next_state_inv: forall (s s': State) (x x': SolverContext),
  ContextInv s x -> next_state (s, x) = Some (s', x') -> ContextInv s' x'.
Proof.
  intros [|m f] s' x x' Hinv Hnext.
  - discriminate.
  - assert (Htrans: state m f ==>[DPLL_BJ] s').
    + now apply (next_state_sound m f x s' x').
    + destruct Hinv as [Hcore [Hwf Hentails]]. split.
      * now apply (next_state_core (state m f) s' x x').
      * destruct s' as [|m' f'].
        -- easy.
        -- split.
           ++ now apply (trans_well_formed DPLL_BJ (state m f)).
           ++ now apply (trans_entails DPLL_BJ m m' f f').
Qed.

Lemma next_state_strategy: Strategy DPLL_BJ ContextInv next_state.
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
  mkContext (tmake None) cm (Clause.elements (formula_lits f)) w wl todo [] (tmake 0) (tmake 0) 0 (tmake false) (tmake None)
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
      * split.
        -- intros l. reflexivity.
        -- intros i ls Hi. apply Hsound in Hi as [Hi|Hin].
           ++ now rewrite tget_tmake in Hi.
           ++ assumption.
        -- assumption.
        -- split.
           ++ intros l Hl. simpl in Hl. now rewrite clause_elements_iff, formula_lits_spec in Hl.
           ++ intros l Hl_in_f _. simpl. now rewrite clause_elements_iff, formula_lits_spec.
        -- assumption.
        -- intros i ls w1 w2 Hi Hw. right. left. now apply (Hpending i ls w1 w2).
      * split.
        -- easy.
        -- split.
           ++ reflexivity.
           ++ split.
              ** easy.
              ** intros y. reflexivity.
    + split.
      * apply initial_well_formed.
      * constructor.
Qed.

(* The context after a restart from m: no values, every literal of f to decide on, and every watched clause pending,
   so that unit clauses are found again; the clauses, watches, hints, marks and phases are kept. *)
Definition restart_context (m: PA) (f: CNF) (x: SolverContext): SolverContext :=
match pend_all (wls x) (Clause.elements (formula_lits f)) (todo x) with
| (wl, todo') =>
  mkContext (unassign_all (vals x) m) (cmap x) (Clause.elements (formula_lits f)) (wat x) wl todo' [] (rsn x) (lvl x)
    0 (mrk x) (phs x)
end.

Lemma restart_context_inv: forall (m: PA) (f: CNF) (x: SolverContext),
  ContextInv (state m f) x -> ContextInv (state ⟨⟩ f) (restart_context m f x).
Proof.
  intros m f x [([Hvals Hsound Hcomplete _ Hstruct Hcover] & Hfresh & _ & _ & Hmarks) _]. unfold restart_context.
  destruct (pend_all (wls x) (Clause.elements (formula_lits f)) (todo x)) as [wl todo'] eqn:Hpend. split.
  - split.
    + split.
      * simpl. now apply unassign_all_spec.
      * assumption.
      * assumption.
      * split.
        -- intros l Hl. simpl in Hl. now rewrite clause_elements_iff, formula_lits_spec in Hl.
        -- intros l Hl_in_f _. simpl. now rewrite clause_elements_iff, formula_lits_spec.
      * now apply (pend_all_struct _ _ (Clause.elements (formula_lits f)) (wls x) wl (todo x) todo').
      (* An empty clause was pending already; any other is pending under its first watch, a literal of f *)
      * intros i ls w1 w2 Hi Hw. simpl in Hi, Hw |- *. right. left.
        destruct (Hstruct i ls w1 w2 Hi Hw) as (Hw1 & _ & [[-> <-]|[Hw1_in _]]).
        -- destruct (Hcover i [] w1 w1 Hi Hw) as [Hok|[Hpending|Hpending]].
           ++ destruct Hok as [[[] _]|[[[] _]|([] & _)]].
           ++ now apply (pend_all_pending_old (Clause.elements (formula_lits f)) (wls x) wl (todo x) todo' i w1).
           ++ now apply (pend_all_pending_old (Clause.elements (formula_lits f)) (wls x) wl (todo x) todo' i w1).
        -- apply (pend_all_pending (Clause.elements (formula_lits f)) (wls x) wl (todo x) todo' i w1).
           ++ assumption.
           ++ apply clause_elements_iff, formula_lits_spec. apply Hsound in Hi.
              apply in_clause_lists in Hi as [c [-> Hc_in_f]]. exists c. split.
              ** now apply clause_elements_iff.
              ** assumption.
           ++ assumption.
    + split.
      * easy.
      * split.
        -- reflexivity.
        -- split.
           ++ easy.
           ++ assumption.
  - split.
    + apply initial_well_formed.
    + apply e_nil.
Qed.
