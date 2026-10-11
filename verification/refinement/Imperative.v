(* The solver step on the store (Store.v): the tables are read and written in place, and only the literals to
   decide on, the pending items and the saved literals are kept as values. Each computation is shown to compute
   exactly the corresponding function of Watches.v and NextState.v, so the solver inherits their correctness. *)
From Stdlib Require Import List.
From Stdlib Require Import Bool.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import State.
From RocqSAT Require Import Strategy.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Search.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import NextState.
From RocqSAT.refinement Require Import Store.

Section Literals.
  (* The value of l in the store. *)
  Definition lookupM (l: Lit): M (option bool) :=
  bind (vget (extract l)) (fun (r: option bool) =>
  ret match r with
      | Some b => Some (if is_pos l then b else negb b)
      | None   => None
      end).

  Lemma lookupM_spec: forall (l: Lit) (st: Store), lookupM l st = (lookup (svals st) l, st).
  Proof. reflexivity. Qed.

  Definition lookup_trueM (l: Lit): M bool :=
  bind (lookupM l) (fun (r: option bool) => ret match r with Some true => true | _ => false end).

  Lemma lookup_trueM_spec: forall (l: Lit) (st: Store), lookup_trueM l st = (lookup_true (svals st) l, st).
  Proof. reflexivity. Qed.

  Definition lookup_undefM (l: Lit): M bool :=
  bind (lookupM l) (fun (r: option bool) => ret match r with None => true | _ => false end).

  Lemma lookup_undefM_spec: forall (l: Lit) (st: Store), lookup_undefM l st = (lookup_undef (svals st) l, st).
  Proof. reflexivity. Qed.

  Definition not_falseM (l: Lit): M bool :=
  bind (lookupM l) (fun (r: option bool) => ret match r with Some false => false | _ => true end).

  Lemma not_falseM_spec: forall (l: Lit) (st: Store), not_falseM l st = (not_false (svals st) l, st).
  Proof. reflexivity. Qed.
End Literals.

(* The first literal of ls that is not false, as find (not_false v). *)
Fixpoint find_not_falseM (ls: list Lit): M (option Lit) :=
match ls with
| []       => ret None
| l :: ls' => bind (not_falseM l) (fun (b: bool) => if b then ret (Some l) else find_not_falseM ls')
end.

Lemma find_not_falseM_spec: forall (ls: list Lit) (st: Store), find_not_falseM ls st = (find (not_false (svals st)) ls, st).
Proof.
  intros ls st. induction ls as [|l ls IH]; simpl.
  - reflexivity.
  - rewrite (bind_spec _ _ _ _ _ (not_falseM_spec l st)). destruct (not_false (svals st) l).
    + reflexivity.
    + assumption.
Qed.

(* The literals ls from the first one without a value on. *)
Fixpoint skip_assignedM (ls: list Lit): M (list Lit) :=
match ls with
| []       => ret []
| l :: ls' => bind (lookup_undefM l) (fun (u: bool) => if u then ret ls else skip_assignedM ls')
end.

Lemma skip_assignedM_spec: forall (ls: list Lit) (st: Store), skip_assignedM ls st = (skip_assigned (svals st) ls, st).
Proof.
  intros ls st. induction ls as [|l ls IH]; simpl.
  - reflexivity.
  - rewrite (bind_spec _ _ _ _ _ (lookup_undefM_spec l st)). destruct (lookup_undef (svals st) l).
    + reflexivity.
    + assumption.
Qed.

(* The first literal of ls that is not false and not other, as the search in replace_watch. *)
Fixpoint find_replacementM (other: Lit) (ls: list Lit): M (option Lit) :=
match ls with
| []       => ret None
| r :: ls' =>
  bind (not_falseM r) (fun (b: bool) => if b && negb (r =? other) then ret (Some r) else find_replacementM other ls')
end.

Lemma find_replacementM_spec: forall (other: Lit) (ls: list Lit) (st: Store),
  find_replacementM other ls st = (find (fun (r: Lit) => not_false (svals st) r && negb (r =? other)) ls, st).
Proof.
  intros other ls st. induction ls as [|r ls IH]; simpl.
  - reflexivity.
  - rewrite (bind_spec _ _ _ _ _ (not_falseM_spec r st)). destruct (not_false (svals st) r && negb (r =? other)).
    + reflexivity.
    + assumption.
Qed.

(* A literal of ls other than other to watch instead of w, as replace_watch. *)
Definition replace_watchM (ls: list Lit) (w other: Lit): M (option Lit) :=
bind (not_falseM w) (fun (b: bool) =>
if b && negb (w =? other) then ret (Some w)
else find_replacementM other ls).

Lemma replace_watchM_spec: forall (ls: list Lit) (w other: Lit) (st: Store),
  replace_watchM ls w other st = (replace_watch (svals st) ls w other, st).
Proof.
  intros ls w other st. unfold replace_watchM, replace_watch. rewrite (bind_spec _ _ _ _ _ (not_falseM_spec w st)).
  destruct (not_false (svals st) w && negb (w =? other)).
  - reflexivity.
  - apply find_replacementM_spec.
Qed.

(* New watched literals for a clause with literals ls, as repair. *)
Definition repairM (ls: list Lit) (w1 w2: Lit): M (option (Lit * Lit)) :=
match ls with
| [] => ret None
| _  =>
  bind (lookup_trueM w1) (fun (t1: bool) =>
  bind (lookup_trueM w2) (fun (t2: bool) =>
  if t1 || t2 then ret (Some (w1, w2)) else
  bind (replace_watchM ls w1 w2) (fun (r: option Lit) =>
  match r with
  | None   => ret None
  | Some a =>
    bind (replace_watchM ls w2 a) (fun (r': option Lit) =>
    match r' with
    | Some b => ret (Some (a, b))
    | None   => bind (lookup_trueM a) (fun (ta: bool) => ret (if ta then Some (a, w2) else None))
    end)
  end)))
end.

Lemma repairM_spec: forall (ls: list Lit) (w1 w2: Lit) (st: Store), repairM ls w1 w2 st = (repair (svals st) ls w1 w2, st).
Proof.
  intros ls w1 w2 st. unfold repairM, repair. destruct ls as [|l0 ls'].
  - reflexivity.
  - rewrite (bind_spec _ _ _ _ _ (lookup_trueM_spec w1 st)), (bind_spec _ _ _ _ _ (lookup_trueM_spec w2 st)).
    destruct (lookup_true (svals st) w1 || lookup_true (svals st) w2).
    + reflexivity.
    + rewrite (bind_spec _ _ _ _ _ (replace_watchM_spec (l0 :: ls') w1 w2 st)).
      destruct (replace_watch (svals st) (l0 :: ls') w1 w2) as [a|].
      * rewrite (bind_spec _ _ _ _ _ (replace_watchM_spec (l0 :: ls') w2 a st)).
        destruct (replace_watch (svals st) (l0 :: ls') w2 a) as [b|].
        -- reflexivity.
        -- rewrite (bind_spec _ _ _ _ _ (lookup_trueM_spec a st)). reflexivity.
      * reflexivity.
Qed.

(* Clause i starts watching l, as watch. *)
Definition watchM (l: Lit) (i: nat): M unit :=
bind (lget (lit_key l)) (fun (ws: list nat) => lset (lit_key l) (i :: ws)).

Lemma watchM_spec: forall (l: Lit) (i: nat) (v: Values) (cm: ClauseMap) (w: Watches) (wl: WatchLists),
  watchM l i (mkStore v cm w wl) = (tt, mkStore v cm w (watch wl l i)).
Proof. reflexivity. Qed.

(* Clause i, visited as a watcher of p, now watches x, as add_watch. *)
Definition add_watchM (i: nat) (p w1 w2 x: Lit): M unit :=
if ((x =? w1) || (x =? w2)) && negb (x =? p) then ret tt else watchM x i.

Lemma add_watchM_spec: forall (i: nat) (p w1 w2 x: Lit) (v: Values) (cm: ClauseMap) (w: Watches) (wl: WatchLists),
  add_watchM i p w1 w2 x (mkStore v cm w wl) = (tt, mkStore v cm w (add_watch wl i p w1 w2 x)).
Proof.
  intros i p w1 w2 x v cm w wl. unfold add_watchM, add_watch. destruct (((x =? w1) || (x =? w2)) && negb (x =? p)).
  - reflexivity.
  - reflexivity.
Qed.

(* Visit the clauses ws watching p, as visit. *)
Fixpoint visitM (p: Lit) (ws: list nat): M (list nat) :=
match ws with
| []        => ret []
| i :: rest =>
  bind (cget i) (fun (ci: option (list Lit)) =>
  match ci with
  | Some ls =>
    bind (wget i) (fun (wi: Lit * Lit) =>
    match wi with
    | (w1, w2) =>
      if (w1 =? p) || (w2 =? p) then
        bind (repairM ls w1 w2) (fun (r: option (Lit * Lit)) =>
        match r with
        | Some (a, b) =>
          if (a =? w1) && (b =? w2) then bind (watchM p i) (fun _ => visitM p rest)
          else
          bind (wset i (a, b)) (fun _ =>
          bind (add_watchM i p w1 w2 a) (fun _ =>
          bind (add_watchM i p w1 w2 b) (fun _ =>
          visitM p rest)))
        | None        => ret ws
        end)
      else visitM p rest
    end)
  | None    => visitM p rest
  end)
end.

Lemma visitM_spec: forall (p: Lit) (ws: list nat) (v: Values) (cm: ClauseMap) (w: Watches) (wl: WatchLists),
  visitM p ws (mkStore v cm w wl) = let '(w', wl', ws') := visit v cm p w wl ws in (ws', mkStore v cm w' wl').
Proof.
  intros p ws. induction ws as [|i rest IH]; intros v cm w wl; simpl.
  - reflexivity.
  - rewrite (bind_spec _ _ _ _ _ (cget_spec i _)). simpl. destruct (tget cm i) as [ls|].
    + rewrite (bind_spec _ _ _ _ _ (wget_spec i _)). simpl. destruct (tget w i) as [w1 w2].
      destruct ((w1 =? p) || (w2 =? p)).
      * rewrite (bind_spec _ _ _ _ _ (repairM_spec ls w1 w2 _)). simpl.
        destruct (repair v ls w1 w2) as [[a b]|].
        -- destruct ((a =? w1) && (b =? w2)).
          ++ rewrite (bind_spec _ _ _ _ _ (watchM_spec p i _ _ _ _)). apply IH.
          ++ rewrite (bind_spec _ _ _ _ _ (wset_spec i (a, b) _)). simpl.
             rewrite (bind_spec _ _ _ _ _ (add_watchM_spec i p w1 w2 a _ _ _ _)).
             rewrite (bind_spec _ _ _ _ _ (add_watchM_spec i p w1 w2 b _ _ _ _)).
             apply IH.
        -- reflexivity.
      * apply IH.
    + apply IH.
Qed.

(* Visit the pending items in turn, as process. *)
Fixpoint processM (todo: list (Lit * list nat)): M (list (Lit * list nat)) :=
match todo with
| []              => ret []
| (p, ws) :: rest =>
  bind (visitM p ws) (fun (ws': list nat) =>
  match ws' with
  | [] => processM rest
  | _  => ret ((p, ws') :: rest)
  end)
end.

Lemma processM_spec: forall (todo: list (Lit * list nat)) (v: Values) (cm: ClauseMap) (w: Watches) (wl: WatchLists),
  processM todo (mkStore v cm w wl) =
  let '(w', wl', todo') := process v cm w wl todo in (todo', mkStore v cm w' wl').
Proof.
  intros todo. induction todo as [|[p ws] rest IH]; intros v cm w wl; simpl.
  - reflexivity.
  - assert (Hvisit := visitM_spec p ws v cm w wl).
    destruct (visit v cm p w wl ws) as [[w' wl'] ws'].
    rewrite (bind_spec _ _ _ _ _ Hvisit). destruct ws' as [|i ws'].
    + apply IH.
    + reflexivity.
Qed.

(* Put the pending clauses back into the watch lists, as unpend. *)
Fixpoint unpendM (todo: list (Lit * list nat)): M unit :=
match todo with
| []              => ret tt
| (p, ws) :: rest =>
  bind (lget (lit_key p)) (fun (l: list nat) =>
  bind (lset (lit_key p) (ws ++ l)) (fun _ => unpendM rest))
end.

Lemma unpendM_spec: forall (todo: list (Lit * list nat)) (v: Values) (cm: ClauseMap) (w: Watches) (wl: WatchLists),
  unpendM todo (mkStore v cm w wl) = (tt, mkStore v cm w (unpend wl todo)).
Proof.
  intros todo. induction todo as [|[p ws] rest IH]; intros v cm w wl; simpl.
  - reflexivity.
  - rewrite (bind_spec _ _ _ _ _ (lget_spec (lit_key p) _)), (bind_spec _ _ _ _ _ (lset_spec (lit_key p) _ _)).
    apply IH.
Qed.

(* Remove the values of the last decision level of m, as unassign_level. *)
Fixpoint unassignM (m: PA): M unit :=
match m with
| ⟨⟩     => ret tt
| ⟨m, l⟩ => bind (vset (extract l) None) (fun _ => unassignM m)
| ⟨m; l⟩ => vset (extract l) None
end.

Lemma unassignM_spec: forall (m: PA) (v: Values) (cm: ClauseMap) (w: Watches) (wl: WatchLists),
  unassignM m (mkStore v cm w wl) = (tt, mkStore (unassign_level v m) cm w wl).
Proof.
  intros m. induction m as [|m IH l|m IH l]; intros v cm w wl; simpl.
  - reflexivity.
  - rewrite (bind_spec _ _ _ _ _ (vset_spec (extract l) None _)). apply IH.
  - reflexivity.
Qed.

(* The part of the solver context outside the store. *)
Record Frame: Type := mkFrame {
  flits: list Lit;               (* the literals to decide on, from the first unassigned one *)
  ftodo: list (Lit * list nat);  (* false literals with the watchers still to visit *)
  fsaved: list (list Lit)        (* the literals to decide on before each decision *)
}.

(* The solver context made of a frame and a store. *)
Definition combine (y: Frame) (st: Store): SolverContext :=
mkContext (svals st) (scmap st) (flits y) (swat st) (swls st) (ftodo y) (fsaved y).

(* Assign l, as assign. *)
Definition assignM (y: Frame) (l: Lit): M Frame :=
bind (vset (extract l) (Some (is_pos l))) (fun _ =>
bind (lget (lit_key (¬l))) (fun (ws: list nat) =>
bind (lset (lit_key (¬l)) []) (fun _ =>
ret (mkFrame (flits y) ((¬l, ws) :: ftodo y) (fsaved y))))).

Lemma assignM_spec: forall (y: Frame) (l: Lit) (v: Values) (cm: ClauseMap) (w: Watches) (wl: WatchLists),
  assignM y l (mkStore v cm w wl) =
  (mkFrame (flits y) ((¬l, watching wl (¬l)) :: ftodo y) (fsaved y),
   mkStore (set_value v l) cm w (tset wl (lit_key (¬l)) [])).
Proof. reflexivity. Qed.

(* One solver step on the store, as next_state. *)
Definition next_stateM (s: State) (y: Frame): M (option (State * Frame)) :=
match s with
| fail      => ret None
| state m f =>
  bind (processM (ftodo y)) (fun (todo': list (Lit * list nat)) =>
  match todo' with
  | (q, i :: ws) :: rest =>
    bind (cget i) (fun (ci: option (list Lit)) =>
    match ci with
    | None    => ret None
    | Some ls =>
      bind (find_not_falseM ls) (fun (r: option Lit) =>
      match r with
      (* Unit *)
      | Some u =>
        bind (assignM (mkFrame (flits y) todo' (fsaved y)) u) (fun (y': Frame) => ret (Some (state ⟨m, u⟩ f, y')))
      | None   =>
        match split_last_decision m with
        (* Fail *)
        | None         => ret (Some (fail, mkFrame (flits y) todo' (fsaved y)))
        (* Backtrack *)
        | Some (m', l) =>
          match fsaved y with
          | ls' :: st =>
            bind (unassignM m) (fun _ =>
            bind (unpendM todo') (fun _ =>
            bind (assignM (mkFrame ls' [] st) (¬l)) (fun (y': Frame) => ret (Some (state ⟨m', (¬l)⟩ f, y')))))
          | []        => ret None
          end
        end
      end)
    end)
  | (_, []) :: _ => ret None
  (* Decide *)
  | [] =>
    bind (skip_assignedM (flits y)) (fun (ls: list Lit) =>
    match ls with
    | l :: ls' =>
      bind (assignM (mkFrame (l :: ls') [] ((l :: ls') :: fsaved y)) l) (fun (y': Frame) => ret (Some (state ⟨m; l⟩ f, y')))
    | []       => ret None
    end)
  end)
end.

(* The step on the store computes next_state on the context made of the frame and the store. *)
Lemma next_stateM_spec: forall (s: State) (y: Frame) (st st': Store) (r: option (State * Frame)),
  next_stateM s y st = (r, st') ->
  next_state (s, combine y st) = option_map (fun (p: State * Frame) => (fst p, combine (snd p) st')) r.
Proof.
  intros [|m f] y [v cm w wl] st' r Hstep; simpl in Hstep.
  - injection Hstep as <- _. reflexivity.
  - unfold next_state, combine. simpl. assert (Hprocess := processM_spec (ftodo y) v cm w wl).
    destruct (process v cm w wl (ftodo y)) as [[w' wl'] todo'].
    rewrite (bind_spec _ _ _ _ _ Hprocess) in Hstep. destruct todo' as [|[q [|i ws]] rest].
    (* Decide *)
    + rewrite (bind_spec _ _ _ _ _ (skip_assignedM_spec (flits y) _)) in Hstep. simpl in Hstep.
      destruct (skip_assigned v (flits y)) as [|l ls].
      * now injection Hstep as <- _.
      * rewrite (bind_spec _ _ _ _ _ (assignM_spec _ l v cm w' wl')) in Hstep. now injection Hstep as <- <-.
    + now injection Hstep as <- _.
    + rewrite (bind_spec _ _ _ _ _ (cget_spec i _)) in Hstep. simpl in Hstep. destruct (tget cm i) as [ls|].
      * rewrite (bind_spec _ _ _ _ _ (find_not_falseM_spec ls _)) in Hstep. simpl in Hstep.
        destruct (find (not_false v) ls) as [u|].
        (* Unit *)
        -- rewrite (bind_spec _ _ _ _ _ (assignM_spec _ u v cm w' wl')) in Hstep. now injection Hstep as <- <-.
        -- destruct (split_last_decision m) as [[m' l]|].
          (* Backtrack *)
          ++ destruct (fsaved y) as [|ls' st].
            ** now injection Hstep as <- _.
            ** rewrite (bind_spec _ _ _ _ _ (unassignM_spec m v cm w' wl')) in Hstep.
               rewrite (bind_spec _ _ _ _ _ (unpendM_spec ((q, i :: ws) :: rest) _ _ _ _)) in Hstep.
               rewrite (bind_spec _ _ _ _ _ (assignM_spec _ (¬l) _ _ _ _)) in Hstep. now injection Hstep as <- <-.
          (* Fail *)
          ++ now injection Hstep as <- <-.
      * now injection Hstep as <- _.
Qed.

(* One solver step on a frame and a store. *)
Definition next_impl (p: State * (Frame * Store)): option (State * (Frame * Store)) :=
match p with
| (s, (y, st)) =>
  match runM (next_stateM s y) st with
  | (Some (s', y'), st') => Some (s', (y', st'))
  | (None, _)            => None
  end
end.

(* The frame and the store make a consistent context. *)
Definition ImpInv (s: State) (c: Frame * Store): Prop := ContextInv s (combine (fst c) (snd c)).

Lemma next_impl_strategy: Strategy ImpInv next_impl.
Proof.
  destruct next_state_strategy as (Hfail & Hnone & Hstep). split.
  - intros [y st]. reflexivity.
  - split.
    + intros s [y st] Hinv Hnext. apply Hnone with (combine y st).
      * assumption.
      * unfold next_impl, runM in Hnext. destruct (next_stateM s y st) as [[[s' y']|] st'] eqn:Hstate.
        -- discriminate.
        -- now apply next_stateM_spec in Hstate.
    + intros s s' [y st] [y' st'] Hinv Hnext. unfold next_impl, runM in Hnext.
      destruct (next_stateM s y st) as [[[s'' y'']|] st''] eqn:Hstate.
      * injection Hnext as <- <- <-. apply next_stateM_spec in Hstate. simpl in Hstate.
        now apply (Hstep s s'' (combine y st) (combine y'' st'')).
      * discriminate.
Qed.

(* Index the clauses with literals lss from k on, as index_clauses. *)
Fixpoint index_clausesM (k: nat) (lss: list (list Lit)) (todo: list (Lit * list nat)): M (list (Lit * list nat)) :=
match lss with
| []        => ret todo
| ls :: lss =>
  bind (cset k (Some ls)) (fun _ =>
  bind (wset k (first_watches ls)) (fun _ =>
  bind (watchM (fst (first_watches ls)) k) (fun _ =>
  bind (watchM (snd (first_watches ls)) k) (fun _ =>
  index_clausesM (S k) lss ((fst (first_watches ls), [k]) :: todo)))))
end.

Lemma index_clausesM_spec: forall (lss: list (list Lit)) (k: nat) (todo: list (Lit * list nat)) (v: Values) (cm: ClauseMap)
  (w: Watches) (wl: WatchLists),
  index_clausesM k lss todo (mkStore v cm w wl) =
  let '(cm', w', wl', todo') := index_clauses k lss cm w wl todo in (todo', mkStore v cm' w' wl').
Proof.
  intros lss. induction lss as [|ls lss IH]; intros k todo v cm w wl; simpl.
  - reflexivity.
  - apply IH.
Qed.

(* The frame and store of the initial state. *)
Definition initial_impl (f: CNF): Frame * Store :=
match runM (index_clausesM 0 (clause_lists f) []) (mkStore (tmake None) (tmake None) (tmake (Pos 0, Pos 0)) (tmake [])) with
| (todo, st) => (mkFrame (Clause.elements (formula_lits f)) todo [], st)
end.

Lemma initial_impl_inv: forall (f: CNF), ImpInv (state ⟨⟩ f) (initial_impl f).
Proof.
  intros f. assert (Hinv := initial_context_inv f). unfold initial_impl, runM.
  rewrite index_clausesM_spec. unfold initial_context in Hinv.
  destruct (index_clauses 0 (clause_lists f) (tmake None) (tmake (Pos 0, Pos 0)) (tmake []) []) as [[[cm w] wl] todo].
  assumption.
Qed.
