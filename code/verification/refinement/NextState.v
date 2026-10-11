From Stdlib Require Import List.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import State.
From RocqSAT Require Import Trans.
From RocqSAT Require Import Measure.
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
  vals: Values;                                          (* the values of the trail *)
  cmap: ClauseMap;                                       (* the clauses of the formula with their literals, by index *)
  lits: list Lit;                                        (* the literals to decide on, from the first unassigned one *)
  wat: Watches;                                          (* the two watched literals of each clause *)
  wls: WatchLists;                                       (* for each literal, the clauses that watch it *)
  todo: list (Lit * list nat);                           (* false literals with the watchers still to visit *)
  saved: list (Values * Watches * WatchLists * list Lit) (* the values, watches and literals before each decision *)
}.

(* The sizes of the tables for a formula f: room for every atom, and for the key of every literal. *)
Definition value_size (f: CNF): nat := S (max_atom_f f).
Definition key_size (f: CNF): nat := 2 * S (max_atom_f f).

(* The context agrees with the state m f; the saved values and watches are treated separately (SavedOK). *)
Definition CoreInv (m: PA) (f: CNF) (x: SolverContext): Prop :=
  vals x = values (value_size f) m /\
  (forall (i: nat) (c: CNF.elt) (ls: list Lit), tget (cmap x) i = Some (c, ls) -> In c (CNF.elements f)) /\
  (forall (c: CNF.elt), In c (CNF.elements f) -> exists (i: nat) (ls: list Lit), tget (cmap x) i = Some (c, ls)) /\
  Cursor (vals x) f (lits x) /\
  WatchStruct (cmap x) (wat x) (wls x) (todo x) /\
  Covered (vals x) (cmap x) (wat x) (todo x).

(* For every decision l on m, the saved values, watches and literals are those before it, l was unassigned,
   and the watches of every clause were fine. *)
Fixpoint SavedOK (f: CNF) (cm: ClauseMap) (m: PA) (st: list (Values * Watches * WatchLists * list Lit)): Prop :=
match m with
| ⟨⟩     => st = []
| ⟨m, _⟩ => SavedOK f cm m st
| ⟨m; l⟩ =>
  match st with
  | (v, w, wl, ls) :: st' =>
    v = values (value_size f) m /\ lookup v l = None /\ Cursor v f ls /\ WatchStruct cm w wl [] /\
    Covered v cm w [] /\ SavedOK f cm m st'
  | []                    => False
  end
end.

(* The most recent decision on m is the first one saved. *)
Lemma saved_ok_split: forall (f: CNF) (cm: ClauseMap) (m n: PA) (l: Lit)
  (st: list (Values * Watches * WatchLists * list Lit)),
  NoDecisions n ->
  SavedOK f cm ⟨m; l ++ n⟩ st ->
  exists (v: Values) (w: Watches) (wl: WatchLists) (ls: list Lit) (st': list (Values * Watches * WatchLists * list Lit)),
  st = (v, w, wl, ls) :: st' /\
  v = values (value_size f) m /\ lookup v l = None /\ Cursor v f ls /\ WatchStruct cm w wl [] /\
  Covered v cm w [] /\ SavedOK f cm m st'.
Proof.
  intros f cm m n l st. induction n as [|n IH l'|n IH l']; simpl.
  - intros _ Hsaved. destruct st as [|[[[v w] wl] ls] st'].
    + contradiction.
    + now exists v, w, wl, ls, st'.
  - assumption.
  - intros [].
Qed.

Definition ContextInv (s: State) (x: SolverContext): Prop :=
match s with
| fail      => True
| state m f => CoreInv m f x /\ SavedOK f (cmap x) m (saved x)
end.

(* The context after assigning l: ¬l becomes false, so its watchers are taken out of its watch list and become
   pending. *)
Definition assign (x: SolverContext) (l: Lit): SolverContext :=
mkContext (set_value (vals x) l) (cmap x) (lits x) (wat x) (tset (wls x) (lit_key (¬l)) [])
  ((¬l, watching (wls x) (¬l)) :: todo x) (saved x).

(* x with other values, literals to decide on, watches, pending items and saved values. *)
Definition update (x: SolverContext) (v: Values) (ls: list Lit) (w: Watches) (wl: WatchLists)
  (todo: list (Lit * list nat)) (st: list (Values * Watches * WatchLists * list Lit)): SolverContext :=
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
    | None         => None
    | Some (_, ls) =>
      match find (not_false (vals x)) ls with
      (* Unit *)
      | Some u => Some (state ⟨m, u⟩ f, assign (update x (vals x) (lits x) w wl ((q, i :: ws) :: rest) (saved x)) u)
      | None   =>
        match split_last_decision m with
        (* Fail *)
        | None         => Some (fail, x)
        (* Backtrack to the values, watches and literals before the decision l, when all watches were fine,
           so that only the watchers of l need visiting *)
        | Some (m', l) =>
          match saved x with
          | (v', w', wl', ls') :: st => Some (state ⟨m', (¬l)⟩ f, assign (update x v' ls' w' wl' [] st) (¬l))
          | []                       => None
          end
        end
      end
    end
  | (_, _, (_, []) :: _) => None
  | (w, wl, []) =>
  (* Decide the first unassigned literal, saving the values, watches and literals *)
  match skip_assigned (vals x) (lits x) with
  | l :: ls => Some (state ⟨m; l⟩ f,
    assign (update x (vals x) (l :: ls) w wl [] ((vals x, w, wl, l :: ls) :: saved x)) l)
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
  intros m f x w wl todo' (Hvals & Hsound & Hcomplete & Hlits & Hstruct & Hcover) Hprocess.
  destruct (process_spec (vals x) (cmap x) (todo x) (wat x) w (wls x) wl todo' Hstruct Hcover Hprocess)
    as (Hstruct' & Hcover' & Hresult). split.
  - split.
    + assumption.
    + split.
      * assumption.
      * split.
        -- assumption.
        -- split.
          ++ assumption.
          ++ now split.
  - assumption.
Qed.

(* A settled clause is not false. *)
Lemma settled_not_false: forall (sz: nat) (m: PA) (c: Clause), Settled (values sz m) c -> c_eval m c <> Some false.
Proof.
  intros sz m c Hsettled Hc. rewrite c_eval_false_iff in Hc.
  destruct Hsettled as [[l [Hl_in Hl]]|[l1 [_ [Hl1_in [_ [_ [Hl1 _]]]]]]].
  - apply Hc in Hl_in. rewrite lookup_values in Hl. congruence.
  - apply Hc in Hl1_in. rewrite lookup_values in Hl1. congruence.
Qed.

Lemma next_state_sound: forall (m: PA) (f: CNF) (x: SolverContext) (s': State) (x': SolverContext),
  ContextInv (state m f) x -> next_state (state m f, x) = Some (s', x') -> state m f ==> s'.
Proof.
  intros m f x s' x' [Hcore _] Hnext. pose proof Hcore as (Hvals & Hsound & _ & Hlits & _). unfold next_state in Hnext.
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
        -- unfold Undef. now rewrite <- (lookup_values (value_size f)).
  - discriminate.
  - destruct Hresult as [Hnil|(p & i' & ws' & rest' & Heq & (c & ls & w1 & w2 & Hc & Hw & Hrepair))].
    + discriminate.
    + injection Heq as <- <- <- <-. rewrite Hc in Hnext.
      destruct Hcore' as (_ & _ & _ & _ & Hstruct' & _).
      assert (Hunsettled: ~ Settled (vals x) c).
      * now apply (stuck_unsettled (vals x) (cmap x) w wl ((q, i :: ws) :: rest) i c ls w1 w2).
      * destruct (Hstruct' i c ls Hc) as [Hls _]. assert (Hls_iff: forall (l: Lit), In l ls <-> l ∈ c).
        -- intros l. subst ls. apply clause_elements_iff.
        -- assert (Hc_in_f: c ∈ f).
          ++ apply in_cnf_elements. now apply Hsound with i ls.
          ++ destruct (find (not_false (vals x)) ls) as [u|] eqn:Hfind.
            (* Unit *)
            ** injection Hnext as <- _.
               destruct (unsettled_unit (vals x) c ls u Hunsettled Hls_iff Hfind) as (Hu_in & Hu & Hrest).
               rewrite Hvals in Hu, Hrest. apply (t_step Unit).
              --- right. now left.
              --- apply (r_unit m f c u).
                +++ assumption.
                +++ assumption.
                +++ apply c_eval_false_iff. intros l' Hl'_in. apply Clause.remove_spec in Hl'_in as [Hl'_in_c Hneq].
                    rewrite <- (lookup_values (value_size f)). now apply Hrest.
                +++ unfold Undef. now rewrite <- (lookup_values (value_size f)).
            ** assert (Hc_false: c_eval m c = Some false).
              --- apply c_eval_false_iff. intros l Hl_in. rewrite <- (lookup_values (value_size f)), <- Hvals.
                  now apply (unsettled_conflict (vals x) c ls).
              --- destruct (split_last_decision m) as [[m_split l_split]|] eqn:Hsplit.
                (* Backtrack *)
                +++ destruct (saved x) as [|[[[v' w'] wl'] ls'] st].
                  *** discriminate.
                  *** injection Hnext as <- _.
                      apply PA.split_last_decision_some_iff in Hsplit as [n_split [-> Hno_dec]].
                      apply (t_step Backtrack).
                    ---- right. right. right. now left.
                    ---- now apply (r_backtrack m_split n_split f c l_split).
                (* Fail *)
                +++ injection Hnext as <- _. apply (t_step Fail).
                  *** now left.
                  *** apply (r_fail m f c).
                    ---- assumption.
                    ---- assumption.
                    ---- now apply PA.split_last_decision_none_iff.
Qed.

(* next_state only stops at a state without a false clause and without a literal to decide. *)
Lemma next_state_none: forall (m: PA) (f: CNF) (x: SolverContext),
  ContextInv (state m f) x ->
  next_state (state m f, x) = None ->
  (forall (c: Clause), c ∈ f -> c_eval m c <> Some false) /\ (forall (l: Lit), l ∈ f -> ~ Undef m l).
Proof.
  intros m f x [Hcore Hsaved] Hnext. pose proof Hcore as (Hvals & _ & Hcomplete & Hlits & _).
  unfold next_state in Hnext.
  destruct (process (vals x) (cmap x) (wat x) (wls x) (todo x)) as [[w wl] todo'] eqn:Hprocess.
  destruct (process_core m f x w wl todo' Hcore Hprocess) as [Hcore' Hresult].
  destruct Hcore' as (_ & _ & _ & _ & Hstruct' & Hcover').
  destruct Hresult as [->|(p & i & ws & rest & -> & (c & ls & w1 & w2 & Hc & Hw & Hrepair))].
  - destruct (skip_assigned (vals x) (lits x)) as [|l ls] eqn:Hskip.
    + split.
      * intros c Hc_in_f Hc. apply cnf_elements_in in Hc_in_f as [c' [Heq Hin]].
        destruct (Hcomplete c' Hin) as [i [ls Hi]].
        destruct (Hcover' i c' ls Hi) as (w1 & w2 & _ & [Hok|[[ws [[] _]]|[ws [[] _]]]]).
        apply watch_ok_settled in Hok. simpl in Hok. rewrite Hvals in Hok.
        apply (settled_not_false (value_size f) m c') in Hok. apply Hok.
        unfold c_eval. rewrite <- (Clause.c_equal_exists _ c c' Heq), <- (Clause.c_equal_forall _ c c' Heq).
        assumption.
      * intros l Hl_in_f Hundef. apply skip_assigned_cursor in Hlits as [_ Hls]. rewrite Hskip in Hls.
        apply (Hls l).
        -- assumption.
        -- rewrite Hvals, lookup_values. assumption.
    + discriminate.
  - rewrite Hc in Hnext. destruct (find (not_false (vals x)) ls) as [u|].
    + discriminate.
    + destruct (split_last_decision m) as [[m' l]|] eqn:Hsplit.
      * destruct (saved x) as [|[[[v' w'] wl'] ls'] st] eqn:Hsaved_x.
        -- apply PA.split_last_decision_some_iff in Hsplit as [n [-> Hno_dec]].
           destruct (saved_ok_split f (cmap x) m' n l [] Hno_dec Hsaved)
             as (v & w0 & wl0 & ls0 & st & Heq & _).
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
  values (value_size f) m' = set_value (values (value_size f) m) l ->
  lookup (values (value_size f) m) l = None ->
  CoreInv m' f (assign x l).
Proof.
  intros m m' f x l (Hvals & Hsound & Hcomplete & Hlits & Hstruct & Hcover) Hvalues Hl.
  (* Every watcher of a literal stays in its watch list or becomes pending *)
  assert (Hholds: forall (i: nat) (y: Lit), In i (watching (wls x) y) \/ Pending (todo x) i y ->
    In i (watching (tset (wls x) (lit_key (¬l)) []) y) \/
    Pending ((¬l, watching (wls x) (¬l)) :: todo x) i y).
  - intros i y [Hin|Hpend].
    + rewrite watching_add. destruct (Lit.eq_dec (¬l) y) as [<-|Hneq].
      * right. apply pending_cons. left. now split.
      * now left.
    + right. apply pending_cons. now right.
  - split.
    + rewrite Hvalues. simpl. now rewrite Hvals.
    + split.
      * assumption.
      * split.
        -- assumption.
        -- split.
          ++ now apply cursor_set_value.
          ++ split.
            ** intros i c ls Hi. destruct (Hstruct i c ls Hi) as [Hls (w1 & w2 & Hw & Hin1 & Hin2 & Hmembers)].
               split.
              --- assumption.
              --- exists w1, w2. split.
                +++ assumption.
                +++ split.
                  *** now apply Hholds.
                  *** split.
                    ---- now apply Hholds.
                    ---- assumption.
            ** intros i c ls Hi. destruct (Hcover i c ls Hi) as (w1 & w2 & Hw & [Hok|[Hpend1|Hpend2]]).
              --- destruct (Hstruct i c ls Hi) as [_ (w1' & w2' & Hw' & Hin1 & Hin2 & _)]. rewrite Hw in Hw'.
                  injection Hw' as <- <-. exists w1, w2. split.
                +++ assumption.
                +++ destruct (Lit.eq_dec w1 (¬l)) as [->|Hneq1].
                  *** right. left. apply pending_cons. destruct Hin1 as [Hin1|Hpend1].
                    ---- left. now split.
                    ---- now right.
                  *** destruct (Lit.eq_dec w2 (¬l)) as [->|Hneq2].
                    ---- right. right. apply pending_cons. destruct Hin2 as [Hin2|Hpend2].
                      ++++ left. now split.
                      ++++ now right.
                    ---- left. simpl. rewrite Hvals in *. now apply watch_ok_cons.
              --- exists w1, w2. split.
                +++ assumption.
                +++ right. left. apply pending_cons. now right.
              --- exists w1, w2. split.
                +++ assumption.
                +++ right. right. apply pending_cons. now right.
Qed.

(* next_state keeps the context consistent. *)
Lemma next_state_inv: forall (s s': State) (x x': SolverContext),
  ContextInv s x -> next_state (s, x) = Some (s', x') -> ContextInv s' x'.
Proof.
  intros [|m f] s' x x' Hinv Hnext.
  - discriminate.
  - destruct Hinv as [Hcore Hsaved]. pose proof Hcore as (Hvals & Hsound & Hcomplete & Hlits & _).
    unfold next_state in Hnext.
    destruct (process (vals x) (cmap x) (wat x) (wls x) (todo x)) as [[w wl] todo'] eqn:Hprocess.
    destruct (process_core m f x w wl todo' Hcore Hprocess) as [Hcore' Hresult].
    destruct todo' as [|[q [|i ws]] rest].
    (* Decide *)
    + destruct (skip_assigned (vals x) (lits x)) as [|l ls] eqn:Hskip.
      * discriminate.
      * injection Hnext as <- <-. apply skip_assigned_cursor in Hlits. rewrite Hskip in Hlits.
        apply skip_assigned_head in Hskip as Hl. rewrite Hvals in Hl.
        destruct Hcore' as (_ & _ & _ & _ & Hstruct' & Hcover'). split.
        -- apply (assign_inv m ⟨m; l⟩ f (update x (vals x) (l :: ls) w wl [] ((vals x, w, wl, l :: ls) :: saved x)) l).
          ++ split.
            ** assumption.
            ** split.
              --- assumption.
              --- split.
                +++ assumption.
                +++ split.
                  *** assumption.
                  *** now split.
          ++ reflexivity.
          ++ assumption.
        -- simpl. split.
          ++ assumption.
          ++ split.
            ** now rewrite Hvals.
            ** split.
              --- assumption.
              --- split.
                +++ assumption.
                +++ now split.
    + discriminate.
    + destruct Hresult as [Hnil|(p & i' & ws' & rest' & Heq & (c & ls & w1 & w2 & Hc & Hw & Hrepair))].
      * discriminate.
      * injection Heq as <- <- <- <-. rewrite Hc in Hnext. pose proof Hcore' as (_ & _ & _ & _ & Hstruct' & _).
        assert (Hunsettled: ~ Settled (vals x) c).
        -- now apply (stuck_unsettled (vals x) (cmap x) w wl ((q, i :: ws) :: rest) i c ls w1 w2).
        -- destruct (Hstruct' i c ls Hc) as [Hls _]. assert (Hls_iff: forall (l: Lit), In l ls <-> l ∈ c).
          ++ intros l. subst ls. apply clause_elements_iff.
          ++ destruct (find (not_false (vals x)) ls) as [u|] eqn:Hfind.
            (* Unit *)
            ** injection Hnext as <- <-.
               destruct (unsettled_unit (vals x) c ls u Hunsettled Hls_iff Hfind) as (_ & Hu & _).
               rewrite Hvals in Hu. split.
              --- now apply (assign_inv m ⟨m, u⟩ f (update x (vals x) (lits x) w wl ((q, i :: ws) :: rest) (saved x)) u).
              --- assumption.
            ** destruct (split_last_decision m) as [[m' l]|] eqn:Hsplit.
              (* Backtrack *)
              --- apply PA.split_last_decision_some_iff in Hsplit as [n [-> Hno_dec]].
                  destruct (saved_ok_split f (cmap x) m' n l (saved x) Hno_dec Hsaved)
                    as (v' & w' & wl' & ls' & st & Hsaved_x & -> & Hl & Hls' & Hstruct0 & Hcover0 & Hsaved').
                  rewrite Hsaved_x in Hnext. injection Hnext as <- <-. split.
                +++ apply (assign_inv m' ⟨m', (¬l)⟩ f (update x (values (value_size f) m') ls' w' wl' [] st) (¬l)).
                  *** split.
                    ---- reflexivity.
                    ---- split.
                      ++++ assumption.
                      ++++ split.
                        **** assumption.
                        **** split.
                          ----- assumption.
                          ----- now split.
                  *** reflexivity.
                  *** rewrite lookup_values in *. now apply l_eval_neg_none_iff in Hl.
                +++ assumption.
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
let n := length (CNF.elements f) in
match index_clauses 0 (CNF.elements f) (tmake n None) (tmake n None) (tmake (key_size f) []) [] with
| (cm, w, wl, todo) =>
  mkContext (tmake (value_size f) None) cm (Clause.elements (formula_lits f)) w wl todo []
end.

Lemma initial_context_inv: forall (f: CNF), ContextInv (state ⟨⟩ f) (initial_context f).
Proof.
  intros f. unfold initial_context. set (n := length (CNF.elements f)).
  destruct (index_clauses 0 (CNF.elements f) (tmake n None) (tmake n None) (tmake (key_size f) []) [])
    as [[[cm w] wl] todo] eqn:Hindex.
  destruct (index_clauses_spec (CNF.elements f) 0 (tmake n None) cm (tmake n None) w (tmake (key_size f) []) wl
    [] todo) as (Hok & Hpending & Hsound & Hcomplete & _).
  - intros i c ls Hi. now rewrite tget_tmake in Hi.
  - intros i c ls Hi. now rewrite tget_tmake in Hi.
  - intros i c ls Hi. now rewrite tget_tmake in Hi.
  - assumption.
  - split.
    + split.
      * reflexivity.
      * split.
        -- intros i c ls Hi. apply Hsound in Hi as [Hi|Hin].
          ++ now rewrite tget_tmake in Hi.
          ++ assumption.
        -- split.
          ++ assumption.
          ++ split.
            ** split.
              --- intros l Hl. simpl in Hl. now rewrite clause_elements_iff, formula_lits_spec in Hl.
              --- intros l Hl_in_f _. simpl. now rewrite clause_elements_iff, formula_lits_spec.
            ** split.
              --- intros i c ls Hi. destruct (Hok i c ls Hi) as [Hls (w1 & w2 & Hw & Hin1 & Hin2 & Hmembers)].
                  split.
                +++ assumption.
                +++ exists w1, w2. split.
                  *** assumption.
                  *** split.
                    ---- now left.
                    ---- split.
                      ++++ now left.
                      ++++ assumption.
              --- intros i c ls Hi. destruct (Hpending i c ls Hi) as (w1 & w2 & Hw & Hpend). exists w1, w2. split.
                +++ assumption.
                +++ right. now left.
    + reflexivity.
Qed.
