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
From RocqSAT Require Import Trans.
From RocqSAT Require Import Strategy.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Search.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import Analysis.
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

  (* The tests below read the value of the atom directly instead of going through lookupM, so that the extracted
     code does not allocate the value of the literal. *)
  Definition lookup_trueM (l: Lit): M bool :=
  bind (vget (extract l)) (fun (r: option bool) =>
  ret match r with
      | Some b => if is_pos l then b else negb b
      | None   => false
      end).

  Lemma lookup_trueM_spec: forall (l: Lit) (st: Store), lookup_trueM l st = (lookup_true (svals st) l, st).
  Proof.
    intros l st. unfold lookup_trueM, lookup_true, lookup. rewrite (bind_spec _ _ _ _ _ (vget_spec (extract l) st)).
    destruct (tget (svals st) (extract l)) as [[|]|]; destruct (is_pos l); reflexivity.
  Qed.

  Definition lookup_undefM (l: Lit): M bool :=
  bind (vget (extract l)) (fun (r: option bool) =>
  ret match r with
      | Some _ => false
      | None   => true
      end).

  Lemma lookup_undefM_spec: forall (l: Lit) (st: Store), lookup_undefM l st = (lookup_undef (svals st) l, st).
  Proof.
    intros l st. unfold lookup_undefM, lookup_undef, lookup. rewrite (bind_spec _ _ _ _ _ (vget_spec (extract l) st)).
    now destruct (tget (svals st) (extract l)).
  Qed.

  Definition not_falseM (l: Lit): M bool :=
  bind (vget (extract l)) (fun (r: option bool) =>
  ret match r with
      | Some b => if is_pos l then b else negb b
      | None   => true
      end).

  Lemma not_falseM_spec: forall (l: Lit) (st: Store), not_falseM l st = (not_false (svals st) l, st).
  Proof.
    intros l st. unfold not_falseM, not_false, lookup. rewrite (bind_spec _ _ _ _ _ (vget_spec (extract l) st)).
    destruct (tget (svals st) (extract l)) as [[|]|]; destruct (is_pos l); reflexivity.
  Qed.
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

Lemma watchM_spec: forall (l: Lit) (i: nat) (v: Values) (cm: ClauseMap) (w: Watches) (wl: WatchLists)
  (rs lv: Table nat) (mk: Table bool) (ph: Values),
  watchM l i (mkStore v cm w wl rs lv mk ph) = (tt, mkStore v cm w (watch wl l i) rs lv mk ph).
Proof. reflexivity. Qed.

(* Clause i, visited as a watcher of p, now watches x, as add_watch. *)
Definition add_watchM (i: nat) (p w1 w2 x: Lit): M unit :=
if ((x =? w1) || (x =? w2)) && negb (x =? p) then ret tt else watchM x i.

Lemma add_watchM_spec: forall (i: nat) (p w1 w2 x: Lit) (v: Values) (cm: ClauseMap) (w: Watches) (wl: WatchLists)
  (rs lv: Table nat) (mk: Table bool) (ph: Values),
  add_watchM i p w1 w2 x (mkStore v cm w wl rs lv mk ph) = (tt, mkStore v cm w (add_watch wl i p w1 w2 x) rs lv mk ph).
Proof.
  intros i p w1 w2 x v cm w wl rs lv mk ph. unfold add_watchM, add_watch. destruct (((x =? w1) || (x =? w2)) && negb (x =? p)).
  - reflexivity.
  - reflexivity.
Qed.

(* Visit the clauses ws watching p, as visit. *)
Fixpoint visitM (p: Lit) (ws: list nat): M (list nat) :=
match ws with
| []        => ret []
| i :: rest =>
  bind (wget i) (fun (wi: Lit * Lit) =>
  match wi with
  | (w1, w2) =>
    if (w1 =? p) || (w2 =? p) then
      let o := if w1 =? p then w2 else w1 in
      bind (lookup_trueM o) (fun (t: bool) =>
      if negb (o =? p) && t then bind (watchM p i) (fun _ => visitM p rest) else
      bind (cget i) (fun (ci: option (list Lit)) =>
      match ci with
      | Some ls =>
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
      | None    => visitM p rest
      end))
    else visitM p rest
  end)
end.

Lemma visitM_spec: forall (p: Lit) (ws: list nat) (v: Values) (cm: ClauseMap) (w: Watches) (wl: WatchLists)
  (rs lv: Table nat) (mk: Table bool) (ph: Values),
  visitM p ws (mkStore v cm w wl rs lv mk ph) = let '(w', wl', ws') := visit v cm p w wl ws in (ws', mkStore v cm w' wl' rs lv mk ph).
Proof.
  intros p ws. induction ws as [|i rest IH]; intros v cm w wl rs lv mk ph; simpl.
  - reflexivity.
  - rewrite (bind_spec _ _ _ _ _ (wget_spec i _)). simpl. destruct (tget w i) as [w1 w2].
    destruct ((w1 =? p) || (w2 =? p)).
    + rewrite (bind_spec _ _ _ _ _ (lookup_trueM_spec _ _)). simpl.
      destruct (negb ((if w1 =? p then w2 else w1) =? p) && lookup_true v (if w1 =? p then w2 else w1)).
      * rewrite (bind_spec _ _ _ _ _ (watchM_spec p i _ _ _ _ _ _ _ _)). apply IH.
      * rewrite (bind_spec _ _ _ _ _ (cget_spec i _)). simpl. destruct (tget cm i) as [ls|].
        -- rewrite (bind_spec _ _ _ _ _ (repairM_spec ls w1 w2 _)). simpl.
           destruct (repair v ls w1 w2) as [[a b]|].
          ++ destruct ((a =? w1) && (b =? w2)).
            ** rewrite (bind_spec _ _ _ _ _ (watchM_spec p i _ _ _ _ _ _ _ _)). apply IH.
            ** rewrite (bind_spec _ _ _ _ _ (wset_spec i (a, b) _)). simpl.
               rewrite (bind_spec _ _ _ _ _ (add_watchM_spec i p w1 w2 a _ _ _ _ _ _ _ _)).
               rewrite (bind_spec _ _ _ _ _ (add_watchM_spec i p w1 w2 b _ _ _ _ _ _ _ _)).
               apply IH.
          ++ reflexivity.
        -- apply IH.
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

Lemma processM_spec: forall (todo: list (Lit * list nat)) (v: Values) (cm: ClauseMap) (w: Watches) (wl: WatchLists)
  (rs lv: Table nat) (mk: Table bool) (ph: Values),
  processM todo (mkStore v cm w wl rs lv mk ph) =
  let '(w', wl', todo') := process v cm w wl todo in (todo', mkStore v cm w' wl' rs lv mk ph).
Proof.
  intros todo. induction todo as [|[p ws] rest IH]; intros v cm w wl rs lv mk ph; simpl.
  - reflexivity.
  - assert (Hvisit := visitM_spec p ws v cm w wl rs lv mk ph).
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

Lemma unpendM_spec: forall (todo: list (Lit * list nat)) (v: Values) (cm: ClauseMap) (w: Watches) (wl: WatchLists)
  (rs lv: Table nat) (mk: Table bool) (ph: Values),
  unpendM todo (mkStore v cm w wl rs lv mk ph) = (tt, mkStore v cm w (unpend wl todo) rs lv mk ph).
Proof.
  intros todo. induction todo as [|[p ws] rest IH]; intros v cm w wl rs lv mk ph; simpl.
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

Lemma unassignM_spec: forall (m: PA) (v: Values) (cm: ClauseMap) (w: Watches) (wl: WatchLists)
  (rs lv: Table nat) (mk: Table bool) (ph: Values),
  unassignM m (mkStore v cm w wl rs lv mk ph) = (tt, mkStore (unassign_level v m) cm w wl rs lv mk ph).
Proof.
  intros m. induction m as [|m IH l|m IH l]; intros v cm w wl rs lv mk ph; simpl.
  - reflexivity.
  - rewrite (bind_spec _ _ _ _ _ (vset_spec (extract l) None _)). apply IH.
  - reflexivity.
Qed.

(* Remove the values of the literals of n and then d, as unassign_segment. *)
Fixpoint unassign_segmentM (d: Lit) (n: PA): M unit :=
match n with
| ⟨⟩     => vset (extract d) None
| ⟨n, x⟩ => bind (vset (extract x) None) (fun _ => unassign_segmentM d n)
| ⟨n; x⟩ => bind (vset (extract x) None) (fun _ => unassign_segmentM d n)
end.

Lemma unassign_segmentM_spec: forall (d: Lit) (n: PA) (v: Values) (cm: ClauseMap) (w: Watches) (wl: WatchLists)
  (rs lv: Table nat) (mk: Table bool) (ph: Values),
  unassign_segmentM d n (mkStore v cm w wl rs lv mk ph) = (tt, mkStore (unassign_segment v d n) cm w wl rs lv mk ph).
Proof.
  intros d n. induction n as [|n IH x|n IH x]; intros v cm w wl rs lv mk ph; simpl.
  - reflexivity.
  - rewrite (bind_spec _ _ _ _ _ (vset_spec (extract x) None _)). apply IH.
  - rewrite (bind_spec _ _ _ _ _ (vset_spec (extract x) None _)). apply IH.
Qed.

Section Analysis.
  (* The number of literals of c at level d, as count_level. *)
  Fixpoint count_levelM (d: nat) (c: list Lit): M nat :=
  match c with
  | []      => ret 0
  | y :: c' =>
    bind (dget (extract y)) (fun (k: nat) =>
    bind (count_levelM d c') (fun (n: nat) => ret (if Nat.eqb k d then S n else n)))
  end.

  Lemma count_levelM_spec: forall (d: nat) (c: list Lit) (st: Store),
    count_levelM d c st = (count_level (slvl st) d c, st).
  Proof.
    intros d c st. induction c as [|y c IH]; simpl.
    - reflexivity.
    - rewrite (bind_spec _ _ _ _ _ (dget_spec (extract y) st)), (bind_spec _ _ _ _ _ IH). unfold count_level. simpl.
      destruct (Nat.eqb (tget (slvl st) (extract y)) d).
      + reflexivity.
      + reflexivity.
  Qed.

  (* Mark the literals of c as b, as set_marks. *)
  Fixpoint set_marksM (c: list Lit) (b: bool): M unit :=
  match c with
  | []      => ret tt
  | y :: c' => bind (mset (lit_key y) b) (fun _ => set_marksM c' b)
  end.

  Lemma set_marksM_spec: forall (c: list Lit) (b: bool) (v: Values) (cm: ClauseMap) (w: Watches) (wl: WatchLists)
    (rs lv: Table nat) (mk: Table bool) (ph: Values),
    set_marksM c b (mkStore v cm w wl rs lv mk ph) = (tt, mkStore v cm w wl rs lv (set_marks mk c b) ph).
  Proof.
    intros c b. induction c as [|y c IH]; intros v cm w wl rs lv mk ph; simpl.
    - reflexivity.
    - rewrite (bind_spec _ _ _ _ _ (mset_spec (lit_key y) b _)). apply IH.
  Qed.

  (* Add the unmarked literals of r other than x to c, as add_unmarked. *)
  Fixpoint add_unmarkedM (d: nat) (x: Lit) (r c: list Lit) (k: nat): M (list Lit * nat) :=
  match r with
  | []      => ret (c, k)
  | y :: r' =>
    bind (mget (lit_key y)) (fun (b: bool) =>
    if (y =? x) || b then add_unmarkedM d x r' c k
    else
    bind (mset (lit_key y) true) (fun _ =>
    bind (dget (extract y)) (fun (ky: nat) =>
    add_unmarkedM d x r' (y :: c) (if Nat.eqb ky d then S k else k))))
  end.

  Lemma add_unmarkedM_spec: forall (d: nat) (x: Lit) (r c: list Lit) (k: nat) (v: Values) (cm: ClauseMap) (w: Watches)
    (wl: WatchLists) (rs lv: Table nat) (mk: Table bool) (ph: Values),
    add_unmarkedM d x r c k (mkStore v cm w wl rs lv mk ph) =
    let '(c', mk', k') := add_unmarked lv d mk x r c k in ((c', k'), mkStore v cm w wl rs lv mk' ph).
  Proof.
    intros d x r. induction r as [|y r IH]; intros c k v cm w wl rs lv mk ph; simpl.
    - reflexivity.
    - rewrite (bind_spec _ _ _ _ _ (mget_spec (lit_key y) _)). simpl. destruct ((y =? x) || tget mk (lit_key y)).
      + apply IH.
      + rewrite (bind_spec _ _ _ _ _ (mset_spec (lit_key y) true _)), (bind_spec _ _ _ _ _ (dget_spec (extract y) _)).
        apply IH.
  Qed.

  (* Resolve c with r on x using the marks, as resolve_marked. *)
  Definition resolve_markedM (d: nat) (c r: list Lit) (x: Lit) (k: nat): M (list Lit * nat) :=
  let nx := ¬x in
  bind (mset (lit_key nx) false) (fun _ => add_unmarkedM d x r (filter (fun (y: Lit) => negb (y =? nx)) c) (k - 1)).

  Lemma resolve_markedM_spec: forall (d: nat) (c r: list Lit) (x: Lit) (k: nat) (v: Values) (cm: ClauseMap)
    (w: Watches) (wl: WatchLists) (rs lv: Table nat) (mk: Table bool) (ph: Values),
    resolve_markedM d c r x k (mkStore v cm w wl rs lv mk ph) =
    let '(c', mk', k') := resolve_marked lv d mk c r x k in ((c', k'), mkStore v cm w wl rs lv mk' ph).
  Proof.
    intros d c r x k v cm w wl rs lv mk ph. unfold resolve_markedM, resolve_marked. cbv zeta.
    rewrite (bind_spec _ _ _ _ _ (mset_spec (lit_key (¬x)) false _)). apply add_unmarkedM_spec.
  Qed.

  (* Resolve c with the reasons of the literals of the last decision level of m, as analyze. *)
  Fixpoint analyzeM (d: nat) (m: PA) (c: list Lit) (k: nat): M (list Lit) :=
  match m with
  | ⟨m', t⟩ =>
    if Nat.leb k 1 then ret c
    else
    bind (mget (lit_key (¬t))) (fun (b: bool) =>
    if b then
      bind (rget (extract t)) (fun (j: nat) =>
      match j with
      | 0   => ret c
      | S i =>
        bind (cget i) (fun (ci: option (list Lit)) =>
        match ci with
        | Some r => bind (resolve_markedM d c r t k) (fun (p: list Lit * nat) => analyzeM d m' (fst p) (snd p))
        | None   => ret c
        end)
      end)
    else analyzeM d m' c k)
  | _ => ret c
  end.

  Lemma analyzeM_spec: forall (d: nat) (m: PA) (c: list Lit) (k: nat) (v: Values) (cm: ClauseMap) (w: Watches)
    (wl: WatchLists) (rs lv: Table nat) (mk: Table bool) (ph: Values),
    analyzeM d m c k (mkStore v cm w wl rs lv mk ph) =
    let '(c', mk') := analyze cm rs lv d m mk c k in (c', mkStore v cm w wl rs lv mk' ph).
  Proof.
    intros d m. induction m as [|m IH t|m IH t]; intros c k v cm w wl rs lv mk ph; simpl.
    - reflexivity.
    - destruct (Nat.leb k 1).
      + reflexivity.
      + rewrite (bind_spec _ _ _ _ _ (mget_spec (lit_key (¬t)) _)). simpl. destruct (tget mk (lit_key (¬t))).
        * rewrite (bind_spec _ _ _ _ _ (rget_spec (extract t) _)). simpl. destruct (tget rs (extract t)) as [|i].
          -- reflexivity.
          -- rewrite (bind_spec _ _ _ _ _ (cget_spec i _)). simpl. destruct (tget cm i) as [r|].
             ++ assert (Hres := resolve_markedM_spec d c r t k v cm w wl rs lv mk ph).
                destruct (resolve_marked lv d mk c r t k) as [[c1 mk1] k1].
                rewrite (bind_spec _ _ _ _ _ Hres). apply IH.
             ++ reflexivity.
        * apply IH.
    - reflexivity.
  Qed.

  (* The first literal of c at level d, as the search in plan. *)
  Fixpoint find_levelM (d: nat) (c: list Lit): M (option Lit) :=
  match c with
  | []      => ret None
  | y :: c' => bind (dget (extract y)) (fun (k: nat) => if Nat.eqb k d then ret (Some y) else find_levelM d c')
  end.

  Lemma find_levelM_spec: forall (d: nat) (c: list Lit) (st: Store),
    find_levelM d c st = (find (fun (y: Lit) => Nat.eqb (tget (slvl st) (extract y)) d) c, st).
  Proof.
    intros d c st. induction c as [|y c IH]; simpl.
    - reflexivity.
    - rewrite (bind_spec _ _ _ _ _ (dget_spec (extract y) st)). destruct (Nat.eqb (tget (slvl st) (extract y)) d).
      + reflexivity.
      + apply IH.
  Qed.

  (* The levels of the literals of c. *)
  Fixpoint levelsM (c: list Lit): M (list nat) :=
  match c with
  | []      => ret []
  | y :: c' => bind (dget (extract y)) (fun (k: nat) => bind (levelsM c') (fun (ks: list nat) => ret (k :: ks)))
  end.

  Lemma levelsM_spec: forall (c: list Lit) (st: Store),
    levelsM c st = (map (fun (y: Lit) => tget (slvl st) (extract y)) c, st).
  Proof.
    intros c st. induction c as [|y c IH]; simpl.
    - reflexivity.
    - now rewrite (bind_spec _ _ _ _ _ (dget_spec (extract y) st)), (bind_spec _ _ _ _ _ IH).
  Qed.

  (* Whether every literal of c is false. *)
  Fixpoint all_falseM (c: list Lit): M bool :=
  match c with
  | []      => ret true
  | y :: c' => bind (not_falseM y) (fun (b: bool) => if b then ret false else all_falseM c')
  end.

  Lemma all_falseM_spec: forall (c: list Lit) (st: Store),
    all_falseM c st = (forallb (fun (y: Lit) => negb (not_false (svals st) y)) c, st).
  Proof.
    intros c st. induction c as [|y c IH]; simpl.
    - reflexivity.
    - rewrite (bind_spec _ _ _ _ _ (not_falseM_spec y st)). destruct (not_false (svals st) y).
      + reflexivity.
      + apply IH.
  Qed.

  (* Whether a literal of n other than nu has its negation marked, as marked_neg. *)
  Fixpoint marked_negM (nu: Lit) (n: PA): M bool :=
  match n with
  | ⟨⟩     => ret false
  | ⟨n, x⟩ => bind (mget (neg_key x)) (fun (b: bool) => if b && negb (x =? nu) then ret true else marked_negM nu n)
  | ⟨n; x⟩ => bind (mget (neg_key x)) (fun (b: bool) => if b && negb (x =? nu) then ret true else marked_negM nu n)
  end.

  Lemma marked_negM_spec: forall (nu: Lit) (n: PA) (st: Store), marked_negM nu n st = (marked_neg (smrk st) nu n, st).
  Proof.
    intros nu n st. induction n as [|n IH x|n IH x]; simpl.
    - reflexivity.
    - rewrite (bind_spec _ _ _ _ _ (mget_spec (neg_key x) st)). now destruct (tget (smrk st) (neg_key x) && negb (x =? nu)).
    - rewrite (bind_spec _ _ _ _ _ (mget_spec (neg_key x) st)). now destruct (tget (smrk st) (neg_key x) && negb (x =? nu)).
  Qed.

  (* The backjump for c, as plan. *)
  Definition planM (d: nat) (m: PA) (c: list Lit): M (option (Lit * (PA * Lit * PA))) :=
  bind (find_levelM d c) (fun (r: option Lit) =>
  match r with
  | None   => ret None
  | Some u =>
    let rest := filter (fun (y: Lit) => negb (y =? u)) c in
    bind (levelsM rest) (fun (ks: list nat) =>
    match split_levels (d - S (list_max ks)) m with
    | None             => ret None
    | Some (mt, d', n) =>
      let nu := ¬u in
      bind (all_falseM c) (fun (b: bool) =>
      bind (marked_negM nu ⟨∅; d'⟩) (fun (b_d: bool) =>
      bind (marked_negM nu n) (fun (b_n: bool) =>
      ret (if b && ((d' =? nu) || in_trail nu n) && negb (b_d || b_n)
           then Some (u, (mt, d', n))
           else None))))
    end)
  end).

  Lemma planM_spec: forall (d: nat) (m: PA) (c: list Lit) (st: Store),
    planM d m c st = (plan (svals st) (slvl st) d m (smrk st) c, st).
  Proof.
    intros d m c st. unfold planM, plan. rewrite (bind_spec _ _ _ _ _ (find_levelM_spec d c st)).
    destruct (find (fun (y: Lit) => Nat.eqb (tget (slvl st) (extract y)) d) c) as [u|].
    - cbv zeta. rewrite (bind_spec _ _ _ _ _ (levelsM_spec _ st)).
      destruct (split_levels _ m) as [[[mt d'] n]|].
      + cbv zeta. rewrite (bind_spec _ _ _ _ _ (all_falseM_spec c st)), (bind_spec _ _ _ _ _ (marked_negM_spec _ _ st)).
        now rewrite (bind_spec _ _ _ _ _ (marked_negM_spec _ _ st)).
      + reflexivity.
    - reflexivity.
  Qed.
End Analysis.

(* The part of the solver context outside the store. *)
Record Frame: Type := mkFrame {
  flits: list Lit;               (* the literals to decide on, from the first unassigned one *)
  ftodo: list (Lit * list nat);  (* false literals with the watchers still to visit *)
  fsaved: list (list Lit);       (* the literals to decide on before each decision *)
  fdl: nat                       (* hint: the current decision level *)
}.

(* The solver context made of a frame and a store. *)
Definition combine (y: Frame) (st: Store): SolverContext :=
mkContext (svals st) (scmap st) (flits y) (swat st) (swls st) (ftodo y) (fsaved y) (srsn st) (slvl st) (fdl y)
  (smrk st) (sphs st).

(* Assign l with reason r, as assign. *)
Definition assignM (y: Frame) (l: Lit) (r: nat): M Frame :=
bind (vset (extract l) (match l with Pos _ => Some true | Neg _ => Some false end)) (fun _ =>
bind (rset (extract l) r) (fun _ =>
bind (dset (extract l) (fdl y)) (fun _ =>
bind (pset (extract l) (match l with Pos _ => Some true | Neg _ => Some false end)) (fun _ =>
bind (lget (lit_key (¬l))) (fun (ws: list nat) =>
bind (lset (lit_key (¬l)) []) (fun _ =>
ret (mkFrame (flits y) ((¬l, ws) :: ftodo y) (fsaved y) (fdl y)))))))).

Lemma assignM_spec: forall (y: Frame) (l: Lit) (r: nat) (v: Values) (cm: ClauseMap) (w: Watches) (wl: WatchLists)
  (rs lv: Table nat) (mk: Table bool) (ph: Values),
  assignM y l r (mkStore v cm w wl rs lv mk ph) =
  (mkFrame (flits y) ((¬l, watching wl (¬l)) :: ftodo y) (fsaved y) (fdl y),
   mkStore (set_value v l) cm w (tset wl (lit_key (¬l)) []) (tset rs (extract l) r) (tset lv (extract l) (fdl y)) mk
     (set_value ph l)).
Proof. intros y l r v cm w wl rs lv mk ph. unfold assignM, set_value. now destruct l. Qed.

(* The phase of l, as phase. *)
Definition phaseM (l: Lit): M Lit :=
bind (pget (extract l)) (fun (o: option bool) =>
match o with
| Some true  => ret (Pos (extract l))
| Some false => ret (Neg (extract l))
| None       => ret l
end).

Lemma phaseM_spec: forall (l: Lit) (st: Store), phaseM l st = (phase (sphs st) l, st).
Proof.
  intros l st. unfold phaseM, phase. rewrite (bind_spec _ _ _ _ _ (pget_spec _ _)).
  now destruct (tget (sphs st) (extract l)) as [[|]|].
Qed.

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
        bind (assignM (mkFrame (flits y) todo' (fsaved y) (fdl y)) u (S i)) (fun (y': Frame) =>
        ret (Some (state ⟨m, u⟩ f, y')))
      | None   =>
        match split_last_decision m with
        (* Fail *)
        | None         => ret (Some (fail, mkFrame (flits y) todo' (fsaved y) (fdl y)))
        | Some (m', l) =>
          bind (set_marksM ls true) (fun _ =>
          bind (count_levelM (fdl y) ls) (fun (k: nat) =>
          bind (analyzeM (fdl y) m ls k) (fun (c: list Lit) =>
          bind (set_marksM c true) (fun _ =>
          bind (planM (fdl y) m c) (fun (p: option (Lit * (PA * Lit * PA))) =>
          bind (set_marksM c false) (fun _ =>
          match p with
          (* Backjump *)
          | Some (u, (mt, d, n)) =>
            match skipn (decisions n) (fsaved y) with
            | ls' :: st =>
              bind (unassign_segmentM d n) (fun _ =>
              bind (unpendM todo') (fun _ =>
              bind (assignM (mkFrame ls' [] st (fdl y - S (decisions n))) u 0) (fun (y': Frame) =>
              ret (Some (state ⟨mt, u⟩ f, y')))))
            | []        => ret None
            end
          (* Backtrack *)
          | None =>
            match fsaved y with
            | ls' :: st =>
              bind (unassignM m) (fun _ =>
              bind (unpendM todo') (fun _ =>
              bind (assignM (mkFrame ls' [] st (fdl y - 1)) (¬l) 0) (fun (y': Frame) =>
              ret (Some (state ⟨m', (¬l)⟩ f, y')))))
            | []        => ret None
            end
          end))))))
        end
      end)
    end)
  | (_, []) :: _ => ret None
  (* Decide *)
  | [] =>
    bind (skip_assignedM (flits y)) (fun (ls: list Lit) =>
    match ls with
    | l :: ls' =>
      bind (phaseM l) (fun (l': Lit) =>
      bind (assignM (mkFrame (l :: ls') [] ((l :: ls') :: fsaved y) (S (fdl y))) l' 0) (fun (y': Frame) =>
      ret (Some (state ⟨m; l'⟩ f, y'))))
    | []       => ret None
    end)
  end)
end.

(* The step on the store computes next_state on the context made of the frame and the store. *)
Lemma next_stateM_spec: forall (s: State) (y: Frame) (st st': Store) (r: option (State * Frame)),
  next_stateM s y st = (r, st') ->
  next_state (s, combine y st) = option_map (fun (p: State * Frame) => (fst p, combine (snd p) st')) r.
Proof.
  intros [|m f] y [v cm w wl rs lv mk ph] st' r Hstep; simpl in Hstep.
  - injection Hstep as <- _. reflexivity.
  - unfold next_state, combine. simpl. assert (Hprocess := processM_spec (ftodo y) v cm w wl rs lv mk ph).
    destruct (process v cm w wl (ftodo y)) as [[w' wl'] todo'].
    rewrite (bind_spec _ _ _ _ _ Hprocess) in Hstep. destruct todo' as [|[q [|i ws]] rest].
    (* Decide *)
    + rewrite (bind_spec _ _ _ _ _ (skip_assignedM_spec (flits y) _)) in Hstep. simpl in Hstep.
      destruct (skip_assigned v (flits y)) as [|l ls].
      * now injection Hstep as <- _.
      * rewrite (bind_spec _ _ _ _ _ (phaseM_spec l _)) in Hstep. simpl in Hstep.
        rewrite (bind_spec _ _ _ _ _ (assignM_spec _ (phase ph l) 0 v cm w' wl' rs lv mk ph)) in Hstep.
        now injection Hstep as <- <-.
    + now injection Hstep as <- _.
    + rewrite (bind_spec _ _ _ _ _ (cget_spec i _)) in Hstep. simpl in Hstep. destruct (tget cm i) as [ls|].
      * rewrite (bind_spec _ _ _ _ _ (find_not_falseM_spec ls _)) in Hstep. simpl in Hstep.
        destruct (find (not_false v) ls) as [u|].
        (* Unit *)
        -- rewrite (bind_spec _ _ _ _ _ (assignM_spec _ u (S i) v cm w' wl' rs lv mk ph)) in Hstep.
           now injection Hstep as <- <-.
        -- destruct (split_last_decision m) as [[m' l]|].
           ++ rewrite (bind_spec _ _ _ _ _ (set_marksM_spec ls true v cm w' wl' rs lv mk ph)) in Hstep.
              rewrite (bind_spec _ _ _ _ _ (count_levelM_spec (fdl y) ls _)) in Hstep. simpl in Hstep.
              assert (Hanalyze := analyzeM_spec (fdl y) m ls (count_level lv (fdl y) ls) v cm w' wl' rs lv
                (set_marks mk ls true) ph).
              destruct (analyze cm rs lv (fdl y) m (set_marks mk ls true) ls (count_level lv (fdl y) ls)) as [c mk'].
              rewrite (bind_spec _ _ _ _ _ Hanalyze) in Hstep.
              rewrite (bind_spec _ _ _ _ _ (set_marksM_spec c true v cm w' wl' rs lv mk' ph)) in Hstep.
              rewrite (bind_spec _ _ _ _ _ (planM_spec (fdl y) m _ _)) in Hstep. simpl in Hstep.
              rewrite (bind_spec _ _ _ _ _ (set_marksM_spec c false v cm w' wl' rs lv _ ph)) in Hstep.
              destruct (plan v lv (fdl y) m (set_marks mk' c true) c) as [[u [[mt d] n]]|].
              (* Backjump *)
              ** destruct (skipn (decisions n) (fsaved y)) as [|ls' st].
                 --- now injection Hstep as <- _.
                 --- rewrite (bind_spec _ _ _ _ _ (unassign_segmentM_spec d n v cm w' wl' rs lv _ _)) in Hstep.
                     rewrite (bind_spec _ _ _ _ _ (unpendM_spec ((q, i :: ws) :: rest) _ _ _ _ _ _ _ _)) in Hstep.
                     rewrite (bind_spec _ _ _ _ _ (assignM_spec _ u 0 _ _ _ _ _ _ _ _)) in Hstep.
                     now injection Hstep as <- <-.
              (* Backtrack *)
              ** destruct (fsaved y) as [|ls' st].
                 --- now injection Hstep as <- _.
                 --- rewrite (bind_spec _ _ _ _ _ (unassignM_spec m v cm w' wl' rs lv _ _)) in Hstep.
                     rewrite (bind_spec _ _ _ _ _ (unpendM_spec ((q, i :: ws) :: rest) _ _ _ _ _ _ _ _)) in Hstep.
                     rewrite (bind_spec _ _ _ _ _ (assignM_spec _ (¬l) 0 _ _ _ _ _ _ _ _)) in Hstep.
                     now injection Hstep as <- <-.
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

Lemma next_impl_strategy: Strategy DPLL_BJ ImpInv next_impl.
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
  (w: Watches) (wl: WatchLists) (rs lv: Table nat) (mk: Table bool) (ph: Values),
  index_clausesM k lss todo (mkStore v cm w wl rs lv mk ph) =
  let '(cm', w', wl', todo') := index_clauses k lss cm w wl todo in (todo', mkStore v cm' w' wl' rs lv mk ph).
Proof.
  intros lss. induction lss as [|ls lss IH]; intros k todo v cm w wl rs lv mk ph; simpl.
  - reflexivity.
  - apply IH.
Qed.

(* The frame and store of the initial state. *)
Definition initial_impl (f: CNF): Frame * Store :=
match runM (index_clausesM 0 (clause_lists f) []) (mkStore (tmake None) (tmake None) (tmake (Pos 0, Pos 0)) (tmake []) (tmake 0) (tmake 0) (tmake false) (tmake None)) with
| (todo, st) => (mkFrame (Clause.elements (formula_lits f)) todo [] 0, st)
end.

Lemma initial_impl_inv: forall (f: CNF), ImpInv (state ⟨⟩ f) (initial_impl f).
Proof.
  intros f. assert (Hinv := initial_context_inv f). unfold initial_impl, runM.
  rewrite index_clausesM_spec. unfold initial_context in Hinv.
  destruct (index_clauses 0 (clause_lists f) (tmake None) (tmake (Pos 0, Pos 0)) (tmake []) []) as [[[cm w] wl] todo].
  assumption.
Qed.
