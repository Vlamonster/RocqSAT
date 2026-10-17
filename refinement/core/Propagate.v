From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Relations.
From Stdlib Require Import Permutation.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import State.
From RocqSAT Require Import Trans.
From RocqSAT.rules Require Import Unit.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import Measure.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Search.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import Heur.

(* Unit propagation with a propagation queue, as in MiniSat: the trail is a table, and the watchers of the
   negations of the trail literals from qhead on are still to be visited. *)

(* The literals of m, oldest first. *)
Fixpoint trail_lits (m: PA): list Lit :=
match m with
| ⟨⟩     => []
| ⟨m, l⟩ => trail_lits m ++ [l]
| ⟨m; l⟩ => trail_lits m ++ [l]
end.

(* The table tr holds the literals of m in its first tlen entries. *)
Definition TrailOf (tr: Table Lit) (tlen: nat) (m: PA): Prop :=
  tlen = length (trail_lits m) /\ forall (j: nat), j < tlen -> tget tr j = nth j (trail_lits m) (Pos 0).

(* l is on the trail from position q on, so the watchers of ¬l are still to be visited. *)
Definition Queued (tr: Table Lit) (q tlen: nat) (l: Lit): Prop := exists (j: nat), q <= j < tlen /\ tget tr j = l.

(* Some literal of ls is true. *)
Definition SomeTrue (v: Values) (ls: list Lit): Prop := exists (y: Lit), In y ls /\
  lookup v y = Some true.

(* The watches of the clause ls, its first two literals, are fine up to the queue Q: a
   false watch has its negation queued, or a literal of the clause is true. *)
Definition WatchQ (v: Values) (Q: Lit -> Prop) (ls: list Lit): Prop :=
  forall (w: Lit), In w (firstn 2 ls) -> lookup v w = Some false -> Q (¬w) \/
    SomeTrue v ls.

(* The watches of every clause are fine up to the queue Q. *)
Definition AllWatchQ (v: Values) (Q: Lit -> Prop) (cm: ClauseMap): Prop :=
  forall (i: nat) (ls: list Lit), tget cm i = Some ls -> WatchQ v Q ls.

(* Every clause has a watcher in the watch lists of its watches. *)
Definition Listed (cm: ClauseMap) (wl: WatchLists): Prop :=
  forall (i: nat) (ls: list Lit) (w: Lit), tget cm i = Some ls -> In w (firstn 2 ls) ->
  HasWatcher (watching wl w) i.

(* The blockers of the watchers ws are literals of their clauses, so a true blocker makes
   its clause true. *)
Definition BlockersIn (cm: ClauseMap) (ws: list Watcher): Prop :=
  forall (i: nat) (b: Lit) (ls: list Lit), In (i, b) ws -> tget cm i = Some ls -> In b ls.

(* The blockers of all watch lists are literals of their clauses. *)
Definition Blocked (cm: ClauseMap) (wl: WatchLists): Prop :=
  forall (l: Lit), BlockersIn cm (watching wl l).

(* cm' holds the clauses of cm, the literals of each in some order. *)
Definition Reordered (cm cm': ClauseMap): Prop :=
  forall (i: nat), (tget cm i = None /\ tget cm' i = None) \/
  exists (ls ls': list Lit), tget cm i = Some ls /\ tget cm' i = Some ls' /\
    Permutation ls ls'.

(* Why a literal is on the trail: by no clause (a decision, or a literal asserted without
   a stored clause), by input clause i, or by reason clause j, the clause a backjump
   asserted it with. *)
Inductive Reason: Type :=
| no_reason
| input (i: nat)
| learnt (j: nat).

(* The context of the solver. *)
Record Ctx: Type := mkCtx {
  vals: Values;      (* the values of the trail *)
  cmap: ClauseMap;
    (* the clauses of the formula with their literals, by index, watches first *)
  wls: WatchLists;   (* for each literal, the watchers of the clauses that watch it *)
  tr: Table Lit;     (* the trail, oldest first *)
  tlen: nat;         (* the length of the trail *)
  qhead: nat;        (* the watchers of the negations of the trail literals from qhead on are still to be visited *)
  shorts: list nat;  (* the clauses with fewer than two literals, still to be checked *)
  alls: Table Lit;   (* the literals to decide on, in order *)
  nlits: nat;        (* the number of literals to decide on *)
  cur: nat;          (* the literals to decide on before cur are assigned *)
  saved: list nat;   (* the cursor before each decision, newest first *)
  rsn: Table Reason; (* the reason of each atom on the trail *)
  lvl: Table nat;    (* the level at which each atom on the trail was assigned *)
  dl: nat;           (* the current decision level: the number of decisions *)
  mrk: Table bool;   (* marks of literals by lit_key, used by the analysis and cleared after it *)
  phs: Values;       (* hint: the value each atom last had, used to decide *)
  nvars: nat;        (* a bound on the trail length, which bounds the propagation loop *)
  rcl: Table (list Lit); (* the reason clauses, a stack *)
  rps: Table nat;    (* reason clause j asserted the literal at trail position rps j *)
  nr: nat;           (* the number of reason clauses *)
  rcap: nat;         (* the room for the literals of the reason clauses *)
  hr: Heur           (* hint: the decision heuristic (Heur.v) *)
}.

(* Assign l with reason r at the current level, appending it to the trail. *)
Definition assign (x: Ctx) (l: Lit) (r: Reason): Ctx :=
mkCtx (set_value (vals x) l) (cmap x) (wls x) (tset (tr x) (tlen x) l) (S (tlen x))
  (qhead x) (shorts x) (alls x) (nlits x) (cur x) (saved x) (tset (rsn x) (extract l) r)
  (tset (lvl x) (extract l) (dl x)) (dl x) (mrk x) (set_value (phs x) l) (nvars x)
  (rcl x) (rps x) (nr x) (rcap x) (hr x).

(* Clause i now has the literals ls. *)
Definition set_clause (x: Ctx) (i: nat) (ls: list Lit): Ctx :=
mkCtx (vals x) (tset (cmap x) i (Some ls)) (wls x) (tr x) (tlen x) (qhead x) (shorts x)
  (alls x) (nlits x) (cur x) (saved x) (rsn x) (lvl x) (dl x) (mrk x) (phs x) (nvars x)
  (rcl x) (rps x) (nr x) (rcap x) (hr x).

(* Clause i now has the literals ls, and a watcher of it with blocker b is appended to the
   watch list of l. *)
Definition move_watch (x: Ctx) (i: nat) (ls: list Lit) (l b: Lit): Ctx :=
mkCtx (vals x) (tset (cmap x) i (Some ls))
  (tset (wls x) (lit_key l) (watching (wls x) l ++ [(i, b)])) (tr x) (tlen x) (qhead x)
  (shorts x) (alls x) (nlits x) (cur x) (saved x) (rsn x) (lvl x) (dl x) (mrk x) (phs x)
  (nvars x) (rcl x) (rps x) (nr x) (rcap x) (hr x).

(* The watch list of l becomes ws. *)
Definition set_watching (x: Ctx) (l: Lit) (ws: list Watcher): Ctx :=
mkCtx (vals x) (cmap x) (tset (wls x) (lit_key l) ws) (tr x) (tlen x) (qhead x) (shorts x)
  (alls x) (nlits x) (cur x) (saved x) (rsn x) (lvl x) (dl x) (mrk x) (phs x) (nvars x)
  (rcl x) (rps x) (nr x) (rcap x) (hr x).

(* The queue moves past one literal. *)
Definition advance (x: Ctx): Ctx :=
mkCtx (vals x) (cmap x) (wls x) (tr x) (tlen x) (S (qhead x)) (shorts x) (alls x)
  (nlits x) (cur x) (saved x) (rsn x) (lvl x) (dl x) (mrk x) (phs x) (nvars x)
  (rcl x) (rps x) (nr x) (rcap x) (hr x).

(* The first literal of ls that is not false, and ls with p in its place. *)
Fixpoint swap_watch (v: Values) (p: Lit) (ls: list Lit): option (Lit * list Lit) :=
match ls with
| []       => None
| y :: ls' =>
  if not_false v y then Some (y, p :: ls') else
  match swap_watch v p ls' with
  | Some (r, ls'') => Some (r, y :: ls'')
  | None           => None
  end
end.

(* Visit the watchers ws of the false literal p, keeping kept (newest first) in the watch
   list of p. A watcher whose blocker is true is kept without looking at its clause. A
   clause watching p is put in the form o :: p :: ls, with o its other watch, and kept
   with blocker o if o is true; otherwise the watch moves from p to a literal of ls that
   is not false, which changes places with p; otherwise all literals but o are false, so o
   is propagated if it is unassigned, and the visit stops at the conflict clause if o is
   false. The unit clause [p] is false too. The watchers of other clauses are dropped. *)
Fixpoint visit (p: Lit) (ws kept: list Watcher) (m: PA) (x: Ctx): PA * Ctx * option nat :=
match ws with
| []             => (m, set_watching x p (rev kept), None)
| (i, b) :: rest =>
  if lookup_true (vals x) b then visit p rest ((i, b) :: kept) m x else
  match tget (cmap x) i with
  | Some [a]              =>
    if a =? p then
      (m, set_watching x p (rev_append kept ws), Some i) else visit p rest kept m x
  | Some (c0 :: c1 :: ls) =>
    if (c0 =? p) || (c1 =? p) then
      let o := if c0 =? p then c1 else c0 in
      let x1 := set_clause x i (o :: p :: ls) in
      if lookup_true (vals x1) o then visit p rest ((i, o) :: kept) m x1 else
      match swap_watch (vals x1) p ls with
      | Some (r, ls') => visit p rest kept m (move_watch x1 i (o :: r :: ls') r o)
      | None          =>
        if lookup_undef (vals x1) o then visit p rest ((i, o) :: kept) ⟨m, o⟩
          (assign x1 o (input i))
        else (m, set_watching x1 p (rev_append kept ws), Some i)
      end
    else visit p rest kept m x
  | _                     => visit p rest kept m x
  end
end.

(* Visit the watchers of the queued literals, at most fuel of them, until a conflict. *)
Fixpoint propagate (fuel: nat) (m: PA) (x: Ctx): PA * Ctx * option nat :=
match fuel with
| 0       => (m, x, None)
| S fuel' =>
  if qhead x <? tlen x then
    let p := ¬(tget (tr x) (qhead x)) in
    match visit p (watching (wls x) p) [] m x with
    | (m', x', Some i) => (m', x', Some i)
    | (m', x', None)   => propagate fuel' m' (advance x')
    end
  else (m, x, None)
end.

(* Check the clauses ss with fewer than two literals: propagate the unassigned ones, until a conflict. *)
Fixpoint check_shorts (ss: list nat) (m: PA) (x: Ctx): PA * Ctx * option nat :=
match ss with
| []       => (m, x, None)
| i :: ss' =>
  match tget (cmap x) i with
  | Some (a :: _) =>
    match lookup (vals x) a with
    | Some true  => check_shorts ss' m x
    | Some false => (m, x, Some i)
    | None       => check_shorts ss' ⟨m, a⟩ (assign x a (input i))
    end
  | Some []       => (m, x, Some i)
  | None          => check_shorts ss' m x
  end
end.

(* The number of decisions on m. *)
Fixpoint decisions (m: PA): nat :=
match m with
| ⟨⟩     => 0
| ⟨m, _⟩ => decisions m
| ⟨m; _⟩ => S (decisions m)
end.

(* A trail without decisions has none. *)
Lemma no_decisions_zero: forall (m: PA), NoDecisions m -> decisions m = 0.
Proof.
  intros m. induction m as [|m IH l|m IH l]; simpl.
  - reflexivity.
  - assumption.
  - intros [].
Qed.

(* The decisions of two trails one after the other. *)
Lemma decisions_app: forall (m n: PA), decisions ⟨m ++ n⟩ = decisions m + decisions n.
Proof.
  intros m n. induction n as [|n IH l|n IH l]; simpl.
  - lia.
  - assumption.
  - rewrite IH. lia.
Qed.

(* The literals ls justify t after the trail m: t is one of them, and the others are
   false in m. *)
Definition Justifies (m: PA) (t: Lit) (ls: list Lit): Prop :=
  In t ls /\ forall (y: Lit), In y ls -> y <> t -> l_eval m y = Some false.

(* The reason r justifies t after the trail m, with the clauses cm and the reason clauses
   rcl (nr of them, clause j for the literal at trail position rps j). *)
Definition ReasonOk (cm: ClauseMap) (rcl: Table (list Lit)) (rps: Table nat) (nr: nat)
  (m: PA) (t: Lit) (r: Reason): Prop :=
match r with
| no_reason => True
| input i   => exists (ls: list Lit), tget cm i = Some ls /\ Justifies m t ls
| learnt j  => j < nr /\ tget rps j = PA.length m /\ Justifies m t (tget rcl j)
end.

(* Every literal of m has as level the number of decisions up to it, and every
   propagated literal a reason that justifies it. *)
Fixpoint TraceOk (cm: ClauseMap) (rsn: Table Reason) (lv: Table nat)
  (rcl: Table (list Lit)) (rps: Table nat) (nr: nat) (m: PA): Prop :=
match m with
| ⟨⟩      => True
| ⟨m', t⟩ =>
  tget lv (extract t) = decisions m' /\
  ReasonOk cm rcl rps nr m' t (tget rsn (extract t)) /\ TraceOk cm rsn lv rcl rps nr m'
| ⟨m'; t⟩ => tget lv (extract t) = S (decisions m') /\ TraceOk cm rsn lv rcl rps nr m'
end.

(* What propagation keeps: the context agrees with the trail m, its clauses are clauses
   of f without duplicate literals, and its levels and reasons are those of m. *)
Record Core (m: PA) (f: CNF) (x: Ctx): Prop := {
  core_vals: ValuesOf (vals x) m;
  core_fresh: Fresh m;
  core_trail: TrailOf (tr x) (tlen x) m;
  core_sound: forall (i: nat) (ls: list Lit), tget (cmap x) i = Some ls -> ClauseOf f ls;
  core_nodup: forall (i: nat) (ls: list Lit), tget (cmap x) i = Some ls -> NoDup ls;
  core_dl: dl x = decisions m;
  core_traced: TraceOk (cmap x) (rsn x) (lvl x) (rcl x) (rps x) (nr x) m
}.

Section Trail.
  Lemma trail_lits_length: forall (m: PA), length (trail_lits m) = PA.length m.
  Proof.
    intros m. induction m as [|m IH l|m IH l]; simpl.
    - reflexivity.
    - rewrite length_app, IH. simpl. lia.
    - rewrite length_app, IH. simpl. lia.
  Qed.

  (* Appending a literal to the trail table. *)
  Lemma trail_of_cons: forall (tr: Table Lit) (tlen: nat) (m: PA) (l: Lit),
    TrailOf tr tlen m -> TrailOf (tset tr tlen l) (S tlen) ⟨m, l⟩.
  Proof.
    intros tr tlen m l [Hlen Hnth]. split.
    - simpl. rewrite length_app, <- Hlen. simpl. lia.
    - intros j Hj. simpl. rewrite tget_tset. destruct (Nat.eq_dec tlen j) as [<-|Hneq].
      + rewrite app_nth2.
        * now rewrite <- Hlen, Nat.sub_diag.
        * lia.
      + rewrite app_nth1.
        * apply Hnth. lia.
        * lia.
  Qed.

  (* The literals queued from q on stay queued when the trail grows. *)
  Lemma queued_cons: forall (tr: Table Lit) (q tlen: nat) (l y: Lit),
    Queued tr q tlen y -> Queued (tset tr tlen l) q (S tlen) y.
  Proof.
    intros tr q tlen l y [j [Hj Hy]]. exists j. split.
    - lia.
    - rewrite tget_tset_other.
      + assumption.
      + lia.
  Qed.

  Lemma queued_new: forall (tr: Table Lit) (q tlen: nat) (l: Lit), q <= tlen -> Queued (tset tr tlen l) q (S tlen) l.
  Proof. intros tr q tlen l Hq. exists tlen. split.
    - lia.
    - apply tget_tset_same.
  Qed.

  (* The literals of m are those on it. *)
  Lemma in_trail_lits: forall (m: PA) (y: Lit), In y (trail_lits m) -> y ∈ m.
  Proof.
    intros m y. induction m as [|m IH l|m IH l]; simpl.
    - intros [].
    - intros Hin. apply in_app_or in Hin as [Hin|[<-|[]]].
      + right. now apply IH.
      + now left.
    - intros Hin. apply in_app_or in Hin as [Hin|[<-|[]]].
      + right. now apply IH.
      + now left.
  Qed.

  (* A literal on the trail table is on the trail. *)
  Lemma trail_of_in: forall (tr: Table Lit) (tlen: nat) (m: PA) (j: nat),
    TrailOf tr tlen m -> j < tlen -> tget tr j ∈ m.
  Proof.
    intros tr tlen m j [Hlen Hnth] Hj. rewrite Hnth.
    - apply in_trail_lits, nth_In. lia.
    - assumption.
  Qed.
  (* The literals of two trails one after the other. *)
  Lemma trail_lits_app: forall (m n: PA),
    trail_lits ⟨m ++ n⟩ = trail_lits m ++ trail_lits n.
  Proof.
    intros m n. induction n as [|n IH l|n IH l]; simpl.
    - now rewrite app_nil_r.
    - now rewrite IH, app_assoc.
    - now rewrite IH, app_assoc.
  Qed.

  (* The trail table holds any prefix of its trail. *)
  Lemma trail_of_prefix: forall (tr: Table Lit) (tlen: nat) (m n: PA),
    TrailOf tr tlen ⟨m ++ n⟩ -> TrailOf tr (PA.length m) m.
  Proof.
    intros tr tlen m n [Hlen Hnth]. rewrite trail_lits_app, length_app in Hlen. split.
    - now rewrite trail_lits_length.
    - intros j Hj. rewrite Hnth.
      + rewrite trail_lits_app, app_nth1.
        * reflexivity.
        * now rewrite trail_lits_length.
      + rewrite trail_lits_length in Hlen. lia.
  Qed.

  (* The trail before the decision l of ⟨m; l ++ n⟩ is fresh, and l was unassigned in
     it. *)
  Lemma fresh_split: forall (m n: PA) (l: Lit),
    Fresh ⟨m; l ++ n⟩ -> Fresh m /\ l_eval m l = None.
  Proof.
    intros m n l. induction n as [|n IH l'|n IH l']; simpl.
    - intros Hfresh. assumption.
    - intros [Hfresh _]. now apply IH.
    - intros [Hfresh _]. now apply IH.
  Qed.

  (* The length of two trails one after the other. *)
  Lemma pa_length_app: forall (m n: PA),
    PA.length ⟨m ++ n⟩ = PA.length m + PA.length n.
  Proof.
    intros m n. induction n as [|n IH l|n IH l]; simpl.
    - lia.
    - rewrite IH. lia.
    - rewrite IH. lia.
  Qed.

  (* The last literal of a trail is at the end of its table. *)
  Lemma trail_of_snoc: forall (tr: Table Lit) (tlen: nat) (m m': PA) (t: Lit),
    trail_lits m' = trail_lits m ++ [t] ->
    TrailOf tr tlen m' ->
    tlen = S (PA.length m) /\ tget tr (PA.length m) = t /\ TrailOf tr (PA.length m) m.
  Proof.
    intros tr tlen m m' t Hlits [Hlen Hnth].
    rewrite Hlits, length_app, trail_lits_length in Hlen. simpl in Hlen.
    split.
    - lia.
    - split.
      + rewrite Hnth.
        * rewrite Hlits, app_nth2.
          -- now rewrite trail_lits_length, Nat.sub_diag.
          -- rewrite trail_lits_length. lia.
        * lia.
      + split.
        * now rewrite trail_lits_length.
        * intros j Hj. rewrite Hnth.
          -- rewrite Hlits, app_nth1.
             ++ reflexivity.
             ++ now rewrite trail_lits_length.
          -- lia.
  Qed.
End Trail.

(* At every decision of m, the watches are fine up to an empty queue with respect to the
   values before it, so a backjump can keep them. *)
Fixpoint SavedQ (cm: ClauseMap) (m: PA): Prop :=
match m with
| ⟨⟩     => True
| ⟨m, _⟩ => SavedQ cm m
| ⟨m; _⟩ => AllWatchQ (values m) (fun (_: Lit) => False) cm /\ SavedQ cm m
end.

(* The parts of the context that propagation does not change, but for the order of the
   literals of clauses. *)
Definition SameRest (x x': Ctx): Prop :=
  Reordered (cmap x) (cmap x') /\ qhead x' = qhead x /\ shorts x' = shorts x /\
    alls x' = alls x /\
  nlits x' = nlits x /\ cur x' = cur x /\ saved x' = saved x /\ dl x' = dl x /\
    mrk x' = mrk x /\
  nvars x' = nvars x /\ rcl x' = rcl x /\ rps x' = rps x /\ nr x' = nr x /\
    rcap x' = rcap x /\ hr x' = hr x.

Section Reorder.
  Lemma reordered_refl: forall (cm: ClauseMap), Reordered cm cm.
  Proof.
    intros cm i. destruct (tget cm i) as [ls|].
    - right. exists ls, ls. now repeat split.
    - now left.
  Qed.

  Lemma reordered_trans: forall (cm1 cm2 cm3: ClauseMap),
    Reordered cm1 cm2 -> Reordered cm2 cm3 -> Reordered cm1 cm3.
  Proof.
    intros cm1 cm2 cm3 H12 H23 i.
    destruct (H12 i) as [[H1 H2]|(ls1 & ls2 & H1 & H2 & Hp12)].
    - destruct (H23 i) as [[_ H3]|(ls2 & ls3 & H2' & _)].
      + now left.
      + congruence.
    - destruct (H23 i) as [[H2' _]|(ls2' & ls3 & H2' & H3 & Hp23)].
      + congruence.
      + rewrite H2 in H2'. injection H2' as <-. right. exists ls1, ls3. split.
        * assumption.
        * split.
          -- assumption.
          -- now apply Permutation_trans with ls2.
  Qed.

  (* Reordering the literals of clause i. *)
  Lemma reordered_set: forall (cm: ClauseMap) (i: nat) (ls ls': list Lit),
    tget cm i = Some ls -> Permutation ls ls' -> Reordered cm (tset cm i (Some ls')).
  Proof.
    intros cm i ls ls' Hi Hperm j. rewrite tget_tset.
    destruct (Nat.eq_dec i j) as [<-|Hne].
    - right. now exists ls, ls'.
    - apply reordered_refl.
  Qed.

  (* A clause of cm' is a reordered clause of cm, and the other way around. *)
  Lemma reordered_some_l: forall (cm cm': ClauseMap) (i: nat) (ls': list Lit),
    Reordered cm cm' -> tget cm' i = Some ls' ->
      exists (ls: list Lit), tget cm i = Some ls /\ Permutation ls ls'.
  Proof.
    intros cm cm' i ls' Hre Hi.
    destruct (Hre i) as [[_ Hnone]|(ls & ls'' & H & H' & Hperm)].
    - congruence.
    - rewrite Hi in H'. injection H' as <-. now exists ls.
  Qed.

  Lemma reordered_some_r: forall (cm cm': ClauseMap) (i: nat) (ls: list Lit),
    Reordered cm cm' -> tget cm i = Some ls ->
      exists (ls': list Lit), tget cm' i = Some ls' /\ Permutation ls ls'.
  Proof.
    intros cm cm' i ls Hre Hi.
    destruct (Hre i) as [[Hnone _]|(ls'' & ls' & H & H' & Hperm)].
    - congruence.
    - rewrite Hi in H. injection H as <-. now exists ls'.
  Qed.

  (* Reordering keeps the empty clauses, and the clauses with at most one literal. *)
  Lemma reordered_empty: forall (cm cm': ClauseMap) (i: nat),
    Reordered cm cm' -> tget cm' i = Some [] -> tget cm i = Some [].
  Proof.
    intros cm cm' i Hre Hi.
    destruct (reordered_some_l cm cm' i [] Hre Hi) as [ls [Hls Hperm]].
    apply Permutation_sym, Permutation_nil in Hperm. now rewrite <- Hperm.
  Qed.

  Lemma reordered_length: forall (cm cm': ClauseMap) (i: nat) (ls': list Lit),
    Reordered cm cm' -> tget cm' i = Some ls' ->
      exists (ls: list Lit), tget cm i = Some ls /\ length ls' = length ls.
  Proof.
    intros cm cm' i ls' Hre Hi.
    destruct (reordered_some_l cm cm' i ls' Hre Hi) as [ls [Hls Hperm]].
    exists ls. split.
    - assumption.
    - symmetry. now apply Permutation_length.
  Qed.

  (* Reordering keeps a clause of f a clause of f. *)
  Lemma clause_of_perm: forall (f: CNF) (ls ls': list Lit), ClauseOf f ls ->
    Permutation ls ls' -> ClauseOf f ls'.
  Proof.
    intros f ls ls' [c [Hc_in_f Hiff]] Hperm. exists c. split.
    - assumption.
    - intros l. rewrite <- Hiff. split.
      + apply Permutation_in. now apply Permutation_sym.
      + now apply Permutation_in.
  Qed.

  (* A true literal stays true when literals are reordered or assigned. *)
  Lemma some_true_perm: forall (v: Values) (ls ls': list Lit), SomeTrue v ls ->
    Permutation ls ls' -> SomeTrue v ls'.
  Proof.
    intros v ls ls' [y [Hy Ht]] Hperm. exists y. split.
    - now apply Permutation_in with ls.
    - assumption.
  Qed.

  Lemma some_true_incl: forall (v v': Values) (ls: list Lit), SomeTrue v ls ->
    Incl v v' -> SomeTrue v' ls.
  Proof.
    intros v v' ls [y [Hy Ht]] Hincl. exists y. split.
    - assumption.
    - now apply Hincl.
  Qed.

  (* The watches of a reordered clause are fine if each of them was a watch, or is not
     false. *)
  Lemma watch_q_reorder: forall (v: Values) (Q: Lit -> Prop) (ls ls': list Lit),
    WatchQ v Q ls -> Permutation ls ls' ->
    (forall (w: Lit), In w (firstn 2 ls') -> In w (firstn 2 ls) \/
      lookup v w <> Some false) ->
    WatchQ v Q ls'.
  Proof.
    intros v Q ls ls' Hwq Hperm Hnew w Hw Hf. destruct (Hnew w Hw) as [Hold|Hnf].
    - destruct (Hwq w Hold Hf) as [Hq|Ht].
      + now left.
      + right. now apply some_true_perm with ls.
    - contradiction.
  Qed.

  Lemma all_watch_q_reorder: forall (v: Values) (Q: Lit -> Prop) (cm: ClauseMap) (i: nat)
    (ls ls': list Lit),
    AllWatchQ v Q cm -> tget cm i = Some ls -> Permutation ls ls' ->
    (forall (w: Lit), In w (firstn 2 ls') -> In w (firstn 2 ls) \/
      lookup v w <> Some false) ->
    AllWatchQ v Q (tset cm i (Some ls')).
  Proof.
    intros v Q cm i ls ls' Hall Hi Hperm Hnew j ls'' Hj. rewrite tget_tset in Hj.
    destruct (Nat.eq_dec i j) as [<-|Hne].
    - injection Hj as <-. apply watch_q_reorder with ls.
      + now apply (Hall i).
      + assumption.
      + assumption.
    - now apply (Hall j).
  Qed.

  (* After setting clause i to ls', clause j is ls' if j is i, and as before otherwise. *)
  Lemma tget_set_clause: forall (cm: ClauseMap) (i j: nat) (ls' ls'': list Lit),
    tget (tset cm i (Some ls')) j = Some ls'' ->
    (j = i /\ ls'' = ls') \/ (j <> i /\ tget cm j = Some ls'').
  Proof.
    intros cm i j ls' ls'' Hj. rewrite tget_tset in Hj. destruct (Nat.eq_dec i j) as [<-|Hne].
    - left. now injection Hj as <-.
    - right. split.
      + intros Heq. now apply Hne.
      + assumption.
  Qed.
End Reorder.

Lemma same_rest_refl: forall (x: Ctx), SameRest x x.
Proof. intros x. split.
  - apply reordered_refl.
  - now repeat split.
Qed.

Lemma same_rest_trans: forall (x1 x2 x3: Ctx), SameRest x1 x2 -> SameRest x2 x3 -> SameRest x1 x3.
Proof.
  intros x1 x2 x3
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15)
    (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15).
  split.
  - now apply reordered_trans with (cmap x2).
  - repeat split; congruence.
Qed.

Section Values.
  (* Assigning an unassigned literal keeps the values of the others. *)
  Lemma lookup_set_defined: forall (v: Values) (l y: Lit) (b: bool),
    lookup v y = Some b -> lookup v l = None -> lookup (set_value v l) y = Some b.
  Proof. intros v l y b Hy Hl. apply (incl_set_value v v l).
    - apply incl_refl.
    - assumption.
    - assumption.
  Qed.

  (* The values before the last literal of a fresh trail are included in its values. *)
  Lemma incl_values_cons: forall (m: PA) (l: Lit), l_eval m l = None -> Incl (values m) (set_value (values m) l).
  Proof.
    intros m l Hl. apply incl_set_value.
    - apply incl_refl.
    - now rewrite lookup_values.
  Qed.

  (* A literal on a fresh trail is true, and its negation false. *)
  Lemma values_in_true: forall (v: Values) (m: PA) (l: Lit), ValuesOf v m -> Fresh m -> l ∈ m -> lookup v l = Some true.
  Proof. intros v m l Hv Hfresh Hin. rewrite Hv. now apply fresh_in_true. Qed.

  Lemma values_neg_in_false: forall (v: Values) (m: PA) (l: Lit),
    ValuesOf v m -> Fresh m -> ¬l ∈ m -> lookup v l = Some false.
  Proof.
    intros v m l Hv Hfresh Hin. apply (values_in_true v) in Hin.
    - rewrite lookup_neg in Hin. destruct (lookup v l) as [[|]|]; easy.
    - assumption.
    - assumption.
  Qed.
End Values.

Section Saved.
  (* Reordering clause i of the context with values v of m, so that each watch was a watch
     or is not false, keeps the watches fine at every decision of m. *)
  Lemma saved_q_reorder: forall (cm: ClauseMap) (m: PA) (v: Values) (i: nat)
    (ls ls': list Lit),
    SavedQ cm m ->
    Incl (values m) v ->
    Fresh m ->
    tget cm i = Some ls ->
    Permutation ls ls' ->
    (forall (w: Lit), In w (firstn 2 ls') -> In w (firstn 2 ls) \/
      lookup v w <> Some false) ->
    SavedQ (tset cm i (Some ls')) m.
  Proof.
    intros cm m.
    induction m as
      [|m IH l|m IH l]; intros v i ls ls' Hsaved Hincl Hfresh Hi Hperm Hnew; simpl in *.
    - easy.
    - destruct Hfresh as [Hfresh Hl]. apply (IH v i ls).
      + assumption.
      + apply incl_trans with (set_value (values m) l).
        * now apply incl_values_cons.
        * assumption.
      + assumption.
      + assumption.
      + assumption.
      + assumption.
    - destruct Hfresh as [Hfresh Hl]. destruct Hsaved as [Hall Hsaved].
      assert (Hincl': Incl (values m) v).
      + apply incl_trans with (set_value (values m) l).
        * now apply incl_values_cons.
        * assumption.
      + split.
        * apply (all_watch_q_reorder _ _ cm i ls).
          -- assumption.
          -- assumption.
          -- assumption.
          -- intros w Hw. destruct (Hnew w Hw) as [Hold|Hnf].
             ++ now left.
             ++ right. intros Hf. now apply Hnf, Hincl'.
        * now apply (IH v i ls).
  Qed.
End Saved.

(* Clause i watching z has a watcher in the watch list of z, or, if z is p, in kept or ws.
   *)
Definition WatchedV (wl: WatchLists) (p: Lit) (kept ws: list Watcher) (i: nat)
  (z: Lit): Prop :=
  (z <> p -> HasWatcher (watching wl z) i) /\ (z = p -> HasWatcher (kept ++ ws) i).

(* During the visit of the watchers of the false literal p, the first queued literal: the
   clauses watching p have their watchers in kept or ws instead of the watch list of p,
   the clauses of kept have a true literal, and all blockers outside the watch list of p
   are literals of their clauses. *)
Record VisitInv (p: Lit) (kept ws: list Watcher) (m: PA) (f: CNF) (x: Ctx): Prop := {
  vi_core: Core m f x;
  vi_qhead: qhead x < tlen x;
  vi_head: tget (tr x) (qhead x) = ¬p;
  vi_watch: AllWatchQ (vals x) (Queued (tr x) (qhead x) (tlen x)) (cmap x);
  vi_saved: SavedQ (cmap x) m;
  vi_listed: forall (i: nat) (ls: list Lit) (z: Lit), tget (cmap x) i = Some ls ->
    In z (firstn 2 ls) ->
    WatchedV (wls x) p kept ws i z;
  vi_blocked: forall (l: Lit), l <> p -> BlockersIn (cmap x) (watching (wls x) l);
  vi_blockers: BlockersIn (cmap x) (kept ++ ws);
  vi_kept: forall (i: nat) (b: Lit) (ls: list Lit), In (i, b) kept ->
    tget (cmap x) i = Some ls ->
    SomeTrue (vals x) ls
}.

(* The visited literal p is false. *)
Lemma visit_p_false: forall (p: Lit) (kept ws: list Watcher) (m: PA) (f: CNF) (x: Ctx),
  VisitInv p kept ws m f x -> lookup (vals x) p = Some false.
Proof.
  intros p kept ws m f x [[Hvals Hfresh Htrail _ _] Hq Hhead _ _ _ _ _ _].
  apply (values_neg_in_false _ m).
  - assumption.
  - assumption.
  - rewrite <- Hhead. now apply (trail_of_in _ (tlen x)).
Qed.

Section Traces.
  (* The atom of an unassigned literal is none of the atoms on the trail. *)
  Lemma undef_atom: forall (m: PA) (l y: Lit),
    Fresh m -> l_eval m l = None -> y ∈ m -> extract y <> extract l.
  Proof.
    intros m l y Hfresh Hl Hy Heq. symmetry in Heq.
    apply Neg.extract_eq in Heq as [-> | ->].
    - rewrite fresh_in_true in Hl by assumption. discriminate.
    - apply l_eval_neg_none_iff in Hl. rewrite fresh_in_true in Hl by assumption.
      discriminate.
  Qed.

  (* The levels and reasons of the atoms on the trail do not change when those of
     another atom do. *)
  Lemma trace_other: forall (cm: ClauseMap) (rsn: Table Reason) (lv: Table nat)
    (rcl: Table (list Lit)) (rps: Table nat) (nr: nat) (m: PA) (a: nat) (r: Reason)
    (k: nat),
    (forall (y: Lit), y ∈ m -> extract y <> a) ->
    TraceOk cm rsn lv rcl rps nr m ->
    TraceOk cm (tset rsn a r) (tset lv a k) rcl rps nr m.
  Proof.
    intros cm rsn lv rcl rps nr m a r k.
    induction m as [|m IH t|m IH t]; intros Hother Htrace.
    - constructor.
    - destruct Htrace as (Hlv & Hrsn & Htrace). cbn [TraceOk].
      assert (Ht: a <> extract t).
      { intros Heq. apply (Hother t).
        - now left.
        - now symmetry. }
      rewrite !tget_tset_other by assumption. split.
      + assumption.
      + split.
        * assumption.
        * apply IH.
          -- intros y Hy. apply Hother. now right.
          -- assumption.
    - destruct Htrace as (Hlv & Htrace). cbn [TraceOk].
      assert (Ht: a <> extract t).
      { intros Heq. apply (Hother t).
        - now left.
        - now symmetry. }
      rewrite tget_tset_other by assumption. split.
      + assumption.
      + apply IH.
        * intros y Hy. apply Hother. now right.
        * assumption.
  Qed.

  (* Justification only depends on the literals, not on their order. *)
  Lemma justifies_perm: forall (m: PA) (t: Lit) (ls ls': list Lit),
    Permutation ls ls' -> Justifies m t ls -> Justifies m t ls'.
  Proof.
    intros m t ls ls' Hperm [Hin Hrest]. split.
    - now apply (Permutation_in t Hperm).
    - intros y Hy Hne. apply Hrest.
      + apply (Permutation_in y (Permutation_sym Hperm)). assumption.
      + assumption.
  Qed.

  (* Reordering the literals of a clause keeps the reasons. *)
  Lemma trace_reorder: forall (cm: ClauseMap) (rsn: Table Reason) (lv: Table nat)
    (rcl: Table (list Lit)) (rps: Table nat) (nr: nat) (m: PA) (i: nat)
    (ls ls': list Lit),
    tget cm i = Some ls -> Permutation ls ls' ->
    TraceOk cm rsn lv rcl rps nr m -> TraceOk (tset cm i (Some ls')) rsn lv rcl rps nr m.
  Proof.
    intros cm rsn lv rcl rps nr m i ls ls' Hi Hperm.
    induction m as [|m IH t|m IH t]; intros Htrace.
    - constructor.
    - destruct Htrace as (Hlv & Hrsn & Htrace). cbn [TraceOk]. split.
      + assumption.
      + split.
        * destruct (tget rsn (extract t)) as [|j|j]; cbn [ReasonOk] in Hrsn |- *.
          -- constructor.
          -- destruct Hrsn as (ls0 & Hj & Hjust). rewrite tget_tset.
             destruct (Nat.eq_dec i j) as [<- | Hne].
             ++ exists ls'. split.
                ** reflexivity.
                ** rewrite Hi in Hj. injection Hj as <-.
                   now apply (justifies_perm m t ls).
             ++ now exists ls0.
          -- assumption.
        * now apply IH.
    - destruct Htrace as (Hlv & Htrace). cbn [TraceOk]. split.
      + assumption.
      + now apply IH.
  Qed.
End Traces.

(* Core only looks at the values, the trail, the clauses and the levels and reasons. *)
Lemma core_ext: forall (m: PA) (f: CNF) (x x': Ctx),
  Core m f x -> vals x' = vals x -> tr x' = tr x -> tlen x' = tlen x ->
    cmap x' = cmap x -> rsn x' = rsn x -> lvl x' = lvl x -> dl x' = dl x ->
    rcl x' = rcl x -> rps x' = rps x -> nr x' = nr x -> Core m f x'.
Proof.
  intros m f x x' [Hvals Hfresh Htrail Hsound Hnodup Hdl Htrace] Hv Htr Hlen Hcm Hrsn Hlv
    Hd Hrcl Hrps Hnr. split.
  - now rewrite Hv.
  - assumption.
  - now rewrite Htr, Hlen.
  - now rewrite Hcm.
  - now rewrite Hcm.
  - now rewrite Hd.
  - now rewrite Hcm, Hrsn, Hlv, Hrcl, Hrps, Hnr.
Qed.

(* Assigning an unassigned literal with a reason that justifies it appends it to the
   trail. *)
Lemma core_assign: forall (m: PA) (f: CNF) (x: Ctx) (l: Lit) (r: Reason),
  Core m f x -> lookup (vals x) l = None ->
  ReasonOk (cmap x) (rcl x) (rps x) (nr x) m l r -> Core ⟨m, l⟩ f (assign x l r).
Proof.
  intros m f x l r [Hvals Hfresh Htrail Hsound Hnodup Hdl Htrace] Hl Hr.
  assert (Hundef: l_eval m l = None) by now rewrite <- Hvals.
  split.
  - intros y. simpl. now rewrite lookup_add, Hvals.
  - split.
    + assumption.
    + assumption.
  - now apply trail_of_cons.
  - assumption.
  - assumption.
  - assumption.
  - cbn [assign cmap rsn lvl rcl rps nr dl TraceOk]. rewrite !tget_tset_same. split.
    + assumption.
    + split.
      * assumption.
      * apply trace_other.
        -- intros y Hy. now apply (undef_atom m l y).
        -- assumption.
Qed.

(* An input clause whose other literals are false justifies l. *)
Lemma reason_input: forall (m: PA) (f: CNF) (x: Ctx) (i: nat) (ls: list Lit) (l: Lit),
  Core m f x -> tget (cmap x) i = Some ls -> In l ls ->
  (forall (y: Lit), In y ls -> y <> l -> lookup (vals x) y = Some false) ->
  ReasonOk (cmap x) (rcl x) (rps x) (nr x) m l (input i).
Proof.
  intros m f x i ls l Hcore Hi Hl Hothers. exists ls. split.
  - assumption.
  - split.
    + assumption.
    + intros y Hy Hne. rewrite <- (core_vals m f x Hcore). now apply Hothers.
Qed.

(* Reordering the literals of a clause keeps it a clause of f without duplicates. *)
Lemma core_reorder: forall (m: PA) (f: CNF) (x: Ctx) (i: nat) (ls ls': list Lit),
  Core m f x -> tget (cmap x) i = Some ls -> Permutation ls ls' ->
    Core m f (set_clause x i ls').
Proof.
  intros m f x i ls ls' [Hvals Hfresh Htrail Hsound Hnodup Hdl Htrace] Hi Hperm.
  split; simpl.
  - assumption.
  - assumption.
  - assumption.
  - intros j ls'' Hj. rewrite tget_tset in Hj. destruct (Nat.eq_dec i j) as [<-|Hne].
    + injection Hj as <-. apply clause_of_perm with ls.
      * now apply (Hsound i).
      * assumption.
    + now apply (Hsound j).
  - intros j ls'' Hj. rewrite tget_tset in Hj. destruct (Nat.eq_dec i j) as [<-|Hne].
    + injection Hj as <-. apply Permutation_NoDup with ls.
      * assumption.
      * now apply (Hnodup i).
    + now apply (Hnodup j).
  - assumption.
  - now apply (trace_reorder (cmap x) _ _ _ _ _ m i ls).
Qed.

Section VisitSteps.
  (* The values of a trail are included in any values of it. *)
  Lemma values_of_incl: forall (v: Values) (m: PA), ValuesOf v m -> Incl (values m) v.
  Proof. intros v m Hv l b Hl. now rewrite Hv, <- lookup_values. Qed.

  (* A literal false after assigning the unassigned l is ¬l, or was false before. *)
  Lemma lookup_set_false: forall (v: Values) (l y: Lit),
    lookup (set_value v l) y = Some false -> lookup v l = None -> y = ¬l \/ lookup v y = Some false.
  Proof.
    intros v l y Hy Hl. rewrite lookup_add in Hy. unfold l_eval_step in Hy.
    destruct (y =? l) eqn:Hyl.
    - discriminate.
    - destruct (y =? ¬l) eqn:Hynl.
      + left. now apply Lit.eqb_eq.
      + now right.
  Qed.

  (* Assigning an unassigned literal l and queueing it keeps watches fine. *)
  Lemma watch_q_assign: forall (v: Values) (Q Q': Lit -> Prop) (l: Lit) (ls: list Lit),
    WatchQ v Q ls -> lookup v l = None -> (forall (y: Lit), Q y -> Q' y) -> Q' l ->
    WatchQ (set_value v l) Q' ls.
  Proof.
    intros v Q Q' l ls Hwq Hl HQ Hl' w Hw Hf. apply lookup_set_false in Hf as [->|Hf].
    - left. now rewrite Neg.involutive.
    - destruct (Hwq w Hw Hf) as [Hq|Ht].
      + left. now apply HQ.
      + right. apply some_true_incl with v.
        * assumption.
        * apply incl_set_value.
          -- apply incl_refl.
          -- assumption.
    - assumption.
  Qed.

  (* Moving a watcher of clause i from ws to the front of kept. *)
  Lemma in_shift: forall (e w: Watcher) (kept ws: list Watcher), In e
    ((w :: kept) ++ ws) <-> In e (kept ++ w :: ws).
  Proof.
    intros e w kept ws. simpl. rewrite !in_app_iff. simpl. split.
    - intros [<-|[Hin|Hin]].
      + right. now left.
      + now left.
      + right. now right.
    - intros [Hin|[<-|Hin]].
      + right. now left.
      + now left.
      + right. now right.
  Qed.

  (* A watcher of a clause other than i is in kept or rest if it is in kept or (i, b) ::
     rest. *)
  Lemma has_watcher_drop: forall (i j: nat) (b: Lit) (kept rest: list Watcher),
    j <> i -> HasWatcher (kept ++ (i, b) :: rest) j -> HasWatcher (kept ++ rest) j.
  Proof.
    intros i j b kept rest Hne [b' Hin]. exists b'.
    apply in_app_iff in Hin as [Hin|[Heq|Hin]].
    - apply in_app_iff. now left.
    - injection Heq as Heq _. now subst.
    - apply in_app_iff. now right.
  Qed.

  (* A clause whose blocker b is a true literal of it is kept, with blocker b. *)
  Lemma visit_inv_keep: forall (p: Lit) (i: nat) (b b': Lit) (rest kept: list Watcher)
    (m: PA) (f: CNF) (x: Ctx),
    VisitInv p kept ((i, b) :: rest) m f x ->
    (forall (ls: list Lit), tget (cmap x) i = Some ls -> In b' ls) ->
    lookup (vals x) b' = Some true ->
    VisitInv p ((i, b') :: kept) rest m f x.
  Proof.
    intros p i b b' rest kept m f x
      [Hcore Hq Hhead Hwatch Hsaved Hlisted Hblocked Hblockers Hkept] Hb'_in Hb'.
    split; try assumption.
    - intros j ls z Hj Hz. destruct (Hlisted j ls z Hj Hz) as [Hother Hp]. split.
      + assumption.
      + intros Hzp. destruct (Nat.eq_dec j i) as [->|Hne].
        * exists b'. now left.
        * destruct (has_watcher_drop i j b kept rest Hne (Hp Hzp)) as [b'' Hin].
          exists b''.
          simpl. now right.
    - intros j c ls Hin Hj. destruct Hin as [Heq|Hin].
      + injection Heq as -> ->. now apply Hb'_in.
      + apply (Hblockers j c ls).
        * apply in_app_iff. apply in_app_iff in Hin as [Hin|Hin].
          -- now left.
          -- right. now right.
        * assumption.
    - intros j c ls [Heq|Hin] Hj.
      + injection Heq as <- <-. exists b'. split.
        * now apply Hb'_in.
        * assumption.
      + now apply (Hkept j c).
  Qed.

  (* The watcher of a clause that does not watch p is dropped. *)
  Lemma visit_inv_drop: forall (p: Lit) (i: nat) (b: Lit) (rest kept: list Watcher)
    (m: PA) (f: CNF) (x: Ctx),
    VisitInv p kept ((i, b) :: rest) m f x ->
    (forall (ls: list Lit), tget (cmap x) i = Some ls -> ~ In p (firstn 2 ls)) ->
    VisitInv p kept rest m f x.
  Proof.
    intros p i b rest kept m f x
      [Hcore Hq Hhead Hwatch Hsaved Hlisted Hblocked Hblockers Hkept] Hnot.
    split; try assumption.
    - intros j ls z Hj Hz. destruct (Hlisted j ls z Hj Hz) as [Hother Hp]. split.
      + assumption.
      + intros ->. destruct (Nat.eq_dec j i) as [->|Hne].
        * exfalso. now apply (Hnot ls).
        * apply (has_watcher_drop i j b).
          -- assumption.
          -- now apply Hp.
    - intros j c ls Hin Hj. apply (Hblockers j c ls).
      + apply in_app_iff. apply in_app_iff in Hin as [Hin|Hin].
        * now left.
        * right. now right.
      + assumption.
  Qed.

  (* Reordering clause i so that it keeps its watches. *)
  Lemma visit_inv_reorder: forall (p: Lit) (i: nat) (ws kept: list Watcher) (m: PA)
    (f: CNF) (x: Ctx)
    (ls ls': list Lit),
    VisitInv p kept ws m f x ->
    tget (cmap x) i = Some ls ->
    Permutation ls ls' ->
    (forall (z: Lit), In z (firstn 2 ls') <-> In z (firstn 2 ls)) ->
    VisitInv p kept ws m f (set_clause x i ls').
  Proof.
    intros p i ws kept m f x ls ls'
      [Hcore Hq Hhead Hwatch Hsaved Hlisted Hblocked Hblockers Hkept] Hi Hperm Hsame.
    pose proof Hcore as [Hvals Hfresh Htrail Hsound Hnodup Hdl Htrace].
    assert (Hclause: forall (j: nat) (ls'': list Lit), tget
      (tset (cmap x) i (Some ls')) j = Some ls'' ->
      (j = i /\ ls'' = ls') \/ (j <> i /\ tget (cmap x) j = Some ls'')).
    - intros j ls'' Hj. rewrite tget_tset in Hj. destruct (Nat.eq_dec i j) as [<-|Hne].
      + left. now injection Hj as <-.
      + right. now split.
    - split; simpl.
      + now apply (core_reorder m f x i ls).
      + assumption.
      + assumption.
      + apply (all_watch_q_reorder _ _ _ i ls).
        * assumption.
        * assumption.
        * assumption.
        * intros w Hw. left. now apply Hsame.
      + apply (saved_q_reorder _ m (vals x) i ls).
        * assumption.
        * now apply values_of_incl.
        * assumption.
        * assumption.
        * assumption.
        * intros w Hw. left. now apply Hsame.
      + intros j ls'' z Hj Hz. destruct (Hclause j ls'' Hj) as [[-> ->]|[_ Hj']].
        * apply (Hlisted i ls z Hi). now apply Hsame.
        * now apply (Hlisted j ls'').
      + intros l Hl j c ls'' Hin Hj. destruct (Hclause j ls'' Hj) as [[-> ->]|[_ Hj']].
        * apply Permutation_in with ls.
          -- assumption.
          -- now apply (Hblocked l Hl i c).
        * now apply (Hblocked l Hl j c).
      + intros j c ls'' Hin Hj. destruct (Hclause j ls'' Hj) as [[-> ->]|[_ Hj']].
        * apply Permutation_in with ls.
          -- assumption.
          -- now apply (Hblockers i c).
        * now apply (Hblockers j c).
      + intros j c ls'' Hin Hj. destruct (Hclause j ls'' Hj) as [[-> ->]|[_ Hj']].
        * apply some_true_perm with ls.
          -- now apply (Hkept i c).
          -- assumption.
        * now apply (Hkept j c).
  Qed.
End VisitSteps.



Section Swap.
  (* swap_watch finds a literal of ls that is not false, and replaces it by p. *)
  Lemma swap_watch_some: forall (v: Values) (p r: Lit) (ls ls': list Lit),
    swap_watch v p ls = Some (r, ls') ->
    In r ls /\ lookup v r <> Some false /\ Permutation (r :: ls') (p :: ls).
  Proof.
    intros v p r ls. induction ls as [|y ls IH]; intros ls' Hswap; simpl in Hswap.
    - discriminate.
    - destruct (not_false v y) eqn:Hy.
      + injection Hswap as <- <-. split.
        * now left.
        * split.
          -- unfold not_false in Hy. destruct (lookup v y) as [[|]|]; easy.
          -- apply perm_swap.
      + destruct (swap_watch v p ls) as [[r' ls1]|] eqn:Hrest.
        * injection Hswap as <- <-. destruct (IH ls1 eq_refl) as (Hin & Hnf & Hperm).
          split.
          -- now right.
          -- split.
             ++ assumption.
             ++ apply perm_trans with (y :: r' :: ls1).
                ** apply perm_swap.
                ** apply perm_trans with (y :: p :: ls).
                   --- now apply perm_skip.
                   --- apply perm_swap.
        * discriminate.
  Qed.

  Lemma swap_watch_none: forall (v: Values) (p: Lit) (ls: list Lit),
    swap_watch v p ls = None -> forall (y: Lit), In y ls -> lookup v y = Some false.
  Proof.
    intros v p ls. induction ls as [|y' ls IH]; intros Hswap y Hy; simpl in Hswap.
    - destruct Hy.
    - destruct (not_false v y') eqn:Hy'.
      + discriminate.
      + destruct Hy as [->|Hy].
        * unfold not_false in Hy'. destruct (lookup v y) as [[|]|]; easy.
        * destruct (swap_watch v p ls) as [[r ls1]|].
          -- discriminate.
          -- now apply IH.
  Qed.
End Swap.

Section VisitSteps2.
  (* A watcher stays in a watch list that grows by one watcher. *)
  Lemma watching_push: forall (wl: WatchLists) (l z: Lit) (e w: Watcher),
    In e (watching wl z) ->
      In e (watching (tset wl (lit_key l) (watching wl l ++ [w])) z).
  Proof.
    intros wl l z e w He. rewrite watching_add. destruct (Lit.eq_dec l z) as [<-|_].
    - apply in_or_app. now left.
    - assumption.
  Qed.

  Lemma watching_push_new: forall (wl: WatchLists) (l: Lit) (w: Watcher),
    In w (watching (tset wl (lit_key l) (watching wl l ++ [w])) l).
  Proof.
    intros wl l w. rewrite watching_add.
    destruct (Lit.eq_dec l l) as [_|]; [|contradiction].
    apply in_or_app. right. now left.
  Qed.

  (* Moving the watch p of clause o :: p :: ls to a literal r of ls that is not false,
     which changes places with p. *)
  (* The watches o and p and a literal r of the rest of a clause without duplicates
     differ. *)
  Lemma nodup_watches: forall (o p r: Lit) (ls: list Lit),
    NoDup (o :: p :: ls) -> In r ls -> o <> p /\ r <> o /\ r <> p.
  Proof.
    intros o p r ls Hnodup Hr. inversion Hnodup as [|? ? Hnotin Hnodup'].
    inversion Hnodup' as [|? ? Hnotin' _]. split.
    - intros ->. apply Hnotin. now left.
    - split.
      + intros ->. apply Hnotin. now right.
      + intros ->. contradiction.
  Qed.

  (* Moving a watch reorders the clause, which keeps it a clause of f. *)
  Lemma core_move: forall (m: PA) (f: CNF) (x: Ctx) (i: nat) (ls ls': list Lit) (l b: Lit),
    Core m f x -> tget (cmap x) i = Some ls -> Permutation ls ls' ->
    Core m f (move_watch x i ls' l b).
  Proof.
    intros m f x i ls ls' l b Hcore Hi Hperm.
    apply (core_ext m f (set_clause x i ls')).
    - now apply (core_reorder m f x i ls).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  (* Moving the watch p of clause o :: p :: ls to a literal r of ls that is not false,
     which changes places with p. *)
  Lemma visit_inv_move: forall (p: Lit) (i: nat) (b: Lit) (rest kept: list Watcher)
    (m: PA) (f: CNF) (x: Ctx) (o r: Lit) (ls ls': list Lit),
    VisitInv p kept ((i, b) :: rest) m f x ->
    tget (cmap x) i = Some (o :: p :: ls) ->
    In r ls ->
    lookup (vals x) r <> Some false ->
    Permutation (r :: ls') (p :: ls) ->
    VisitInv p kept rest m f (move_watch x i (o :: r :: ls') r o).
  Proof.
    intros p i b rest kept m f x o r ls ls' Hinv Hi Hr_in Hr Hperm.
    pose proof (core_nodup m f x (vi_core _ _ _ _ _ _ Hinv) i _ Hi) as Hnodup.
    destruct (nodup_watches o p r ls Hnodup Hr_in) as (Hop & Hro & Hrp).
    assert (Hperm': Permutation (o :: p :: ls) (o :: r :: ls')).
    - apply perm_skip. now apply Permutation_sym.
    - (* The new watches: o was a watch, r is not false *)
      assert (Hnew: forall (w: Lit), In w (firstn 2 (o :: r :: ls')) ->
        In w (firstn 2 (o :: p :: ls)) \/ lookup (vals x) w <> Some false).
      + intros w [<-|[<-|[]]].
        * left. now left.
        * now right.
      + pose proof (core_move m f x i _ _ r o (vi_core _ _ _ _ _ _ Hinv) Hi Hperm') as Hcore'.
        destruct Hinv as [Hcore Hq Hhead Hwatch Hsaved Hlisted Hblocked Hblockers Hkept].
        split; simpl.
        * assumption.
        * assumption.
        * assumption.
        * apply (all_watch_q_reorder _ _ _ i (o :: p :: ls)).
          -- assumption.
          -- assumption.
          -- assumption.
          -- assumption.
        * apply (saved_q_reorder _ m (vals x) i (o :: p :: ls)).
          -- assumption.
          -- now apply values_of_incl, Hcore.
          -- apply Hcore.
          -- assumption.
          -- assumption.
          -- assumption.
        (* The watch lists: o still has its watcher, r gets the new one *)
        * intros j ls'' z Hj Hz. apply tget_set_clause in Hj as [[-> ->]|[Hne Hj]].
          -- destruct Hz as [<-|[<-|[]]].
             ++ split.
                ** intros _. destruct (Hlisted i (o :: p :: ls) o Hi) as [Ho _].
                   --- now left.
                   --- destruct (Ho Hop) as [c Hc]. exists c. now apply watching_push.
                ** intros Heq. contradiction.
             ++ split.
                ** intros _. exists o. apply watching_push_new.
                ** intros Heq. contradiction.
          -- destruct (Hlisted j ls'' z Hj Hz) as [Hother Hp]. split.
             ++ intros Hzp. destruct (Hother Hzp) as [c Hc]. exists c.
                now apply watching_push.
             ++ intros Hzp. apply (has_watcher_drop i j b).
                ** assumption.
                ** now apply Hp.
        (* The blockers: the new watcher has blocker o *)
        * intros l Hl j c ls'' Hin Hj. rewrite watching_add in Hin.
          destruct (Lit.eq_dec r l) as [<-|Hne].
          -- apply in_app_iff in Hin as [Hin|[Heq|[]]].
             ++ apply tget_set_clause in Hj as [[-> ->]|[_ Hj]].
                ** apply Permutation_in with (o :: p :: ls).
                   --- assumption.
                   --- now apply (Hblocked r Hrp i c).
                ** now apply (Hblocked r Hrp j c).
             ++ injection Heq as -> ->. apply tget_set_clause in Hj as [[_ ->]|[Hne _]].
                ** now left.
                ** contradiction.
          -- apply tget_set_clause in Hj as [[-> ->]|[_ Hj]].
             ++ apply Permutation_in with (o :: p :: ls).
                ** assumption.
                ** now apply (Hblocked l Hl i c).
             ++ now apply (Hblocked l Hl j c).
        * intros j c ls'' Hin Hj. assert (Hin': In (j, c) (kept ++ (i, b) :: rest)).
          -- apply in_app_iff. apply in_app_iff in Hin as [Hin|Hin].
             ++ now left.
             ++ right. now right.
          -- apply tget_set_clause in Hj as [[-> ->]|[_ Hj]].
             ++ apply Permutation_in with (o :: p :: ls).
                ** assumption.
                ** now apply (Hblockers i c).
             ++ now apply (Hblockers j c).
        * intros j c ls'' Hin Hj. apply tget_set_clause in Hj as [[-> ->]|[_ Hj]].
          -- apply some_true_perm with (o :: p :: ls).
             ++ now apply (Hkept i c).
             ++ assumption.
          -- now apply (Hkept j c).
  Qed.

  (* Assigning an unassigned literal, which is queued. *)
  Lemma visit_inv_assign: forall (p: Lit) (ws kept: list Watcher) (m: PA) (f: CNF)
    (x: Ctx) (l: Lit) (r: Reason),
    VisitInv p kept ws m f x -> lookup (vals x) l = None ->
    ReasonOk (cmap x) (rcl x) (rps x) (nr x) m l r ->
      VisitInv p kept ws ⟨m, l⟩ f (assign x l r).
  Proof.
    intros p ws kept m f x l r
      [Hcore Hq Hhead Hwatch Hsaved Hlisted Hblocked Hblockers Hkept] Hl Hr.
    split; simpl.
    - now apply core_assign.
    - lia.
    - rewrite tget_tset_other.
      + assumption.
      + lia.
    - intros j ls Hj. apply (watch_q_assign (vals x) (Queued (tr x) (qhead x) (tlen x))).
      + now apply (Hwatch j).
      + assumption.
      + intros y. apply queued_cons.
      + apply queued_new. lia.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - intros j c ls Hin Hj. apply some_true_incl with (vals x).
      + now apply (Hkept j c).
      + apply incl_set_value.
        * apply incl_refl.
        * assumption.
  Qed.

  (* Assigning the unassigned o, all other literals of its clause being false, is a Unit
     step. *)
  Lemma visit_unit_step: forall (m: PA) (f: CNF) (x: Ctx) (i: nat) (ls: list Lit) (o: Lit),
    Core m f x ->
    tget (cmap x) i = Some ls ->
    In o ls ->
    (forall (y: Lit), In y ls -> y <> o -> lookup (vals x) y = Some false) ->
    lookup (vals x) o = None ->
    state m f ==>[DPLL_BJ] state ⟨m, o⟩ f.
  Proof.
    intros m f x i ls o [Hvals _ _ Hsound _] Hi Ho_in Hrest Ho. apply Hsound in Hi as [c [Hc_in_f Hiff]].
    apply (t_step Unit).
    - right. now left.
    - apply (r_unit m f c o).
      + now apply Hiff.
      + assumption.
      + apply c_eval_false_iff. intros y Hy. apply Clause.remove_spec in Hy as [Hy Hneq]. rewrite <- Hvals.
        apply Hrest.
        * now apply Hiff.
        * assumption.
      + unfold Undef. now rewrite <- Hvals.
  Qed.
End VisitSteps2.

(* The result of visiting the watchers of the false literal p from m and x: Unit steps
   lead to m', and in x' the watch lists are complete again; either every clause watching
   p has a true literal, or clause r is false. *)
Record VisitOut (p: Lit) (m: PA) (f: CNF) (x: Ctx) (m': PA) (x': Ctx)
  (r: option nat): Prop := {
  vo_steps: state m f ==>*[DPLL_BJ] state m' f;
  vo_rest: SameRest x x';
  vo_incl: Incl (vals x) (vals x');
  vo_core: Core m' f x';
  vo_qhead: qhead x' < tlen x';
  vo_head: tget (tr x') (qhead x') = ¬p;
  vo_watch: AllWatchQ (vals x') (Queued (tr x') (qhead x') (tlen x')) (cmap x');
  vo_saved: SavedQ (cmap x') m';
  vo_listed: Listed (cmap x') (wls x');
  vo_blocked: Blocked (cmap x') (wls x');
  vo_done: r = None -> forall (i: nat) (ls: list Lit), tget (cmap x') i = Some ls ->
    In p (firstn 2 ls) ->
    SomeTrue (vals x') ls;
  vo_conflict: forall (i: nat), r = Some i ->
    exists (ls: list Lit), tget (cmap x') i = Some ls /\ forall (y: Lit), In y ls ->
      lookup (vals x') y = Some false
}.

(* A visit from m1 and x1 is one from m and x, if m1 follows from m and x1 from x by
   propagation. *)
Lemma visit_out_before: forall (p: Lit) (m m1 m': PA) (f: CNF) (x x1 x': Ctx)
  (r: option nat),
  state m f ==>*[DPLL_BJ] state m1 f -> SameRest x x1 -> Incl (vals x) (vals x1) ->
  VisitOut p m1 f x1 m' x' r -> VisitOut p m f x m' x' r.
Proof.
  intros p m m1 m' f x x1 x' r Hsteps Hrest Hincl
    [Hsteps' Hrest' Hincl' Hcore Hq Hhead Hwatch Hsaved Hlisted
    Hblocked Hdone Hconflict]. split; try assumption.
  - now apply rt_trans with (state m1 f).
  - now apply same_rest_trans with x1.
  - now apply incl_trans with (vals x1).
Qed.

(* The visit ends by putting kept and the unvisited watchers ws back into the watch list
   of p: at the end of the watchers, or at a false clause. *)
Lemma visit_out_end: forall (p: Lit) (kept ws: list Watcher) (m: PA) (f: CNF) (x: Ctx)
  (r: option nat),
  VisitInv p kept ws m f x ->
  (r = None -> ws = []) ->
  (forall (i: nat), r = Some i ->
    exists (ls: list Lit), tget (cmap x) i = Some ls /\ forall (y: Lit), In y ls ->
      lookup (vals x) y = Some false) ->
  VisitOut p m f x m (set_watching x p (rev_append kept ws)) r.
Proof.
  intros p kept ws m f x r
    [Hcore Hq Hhead Hwatch Hsaved Hlisted Hblocked Hblockers Hkept] Hend Hconflict.
  assert (Hback: forall (e: Watcher), In e (kept ++ ws) -> In e (rev_append kept ws)).
  - intros e He. rewrite rev_append_rev. apply in_app_iff.
    apply in_app_iff in He as [He|He].
    + left. now apply in_rev in He.
    + now right.
  - split; simpl.
    + apply rt_refl.
    + split.
      * apply reordered_refl.
      * now repeat split.
    + apply incl_refl.
    + now apply (core_ext m f x).
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + intros i ls z Hi Hz. destruct (Hlisted i ls z Hi Hz) as [Hother Hp].
      rewrite watching_add.
      destruct (Lit.eq_dec p z) as [<-|Hne].
      * destruct (Hp eq_refl) as [c Hc]. exists c. now apply Hback.
      * apply Hother. intros Heq. now apply Hne.
    + intros l i c ls Hin Hi. rewrite watching_add in Hin.
      destruct (Lit.eq_dec p l) as [<-|Hne].
      * apply (Hblockers i c).
        -- rewrite rev_append_rev in Hin. apply in_app_iff.
           apply in_app_iff in Hin as [Hin|Hin].
           ++ left. now apply in_rev.
           ++ now right.
        -- assumption.
      * assert (Hl: l <> p).
        -- intros Heq. now apply Hne.
        -- now apply (Hblocked l Hl i c).
    + intros Hr i ls Hi Hp. destruct (Hlisted i ls p Hi Hp) as [_ Hwatched].
      destruct (Hwatched eq_refl) as [c Hc]. rewrite (Hend Hr), app_nil_r in Hc.
      now apply (Hkept i c).
    + assumption.
Qed.

(* Reordering a clause, moving a watch and assigning keep the rest of the context. *)
Lemma same_rest_set_clause: forall (x: Ctx) (i: nat) (ls ls': list Lit),
  tget (cmap x) i = Some ls -> Permutation ls ls' -> SameRest x (set_clause x i ls').
Proof.
  intros x i ls ls' Hi Hperm. split.
  - now apply (reordered_set (cmap x) i ls).
  - now repeat split.
Qed.

Lemma same_rest_move: forall (x: Ctx) (i: nat) (ls ls': list Lit) (l b: Lit),
  tget (cmap x) i = Some ls -> Permutation ls ls' -> SameRest x (move_watch x i ls' l b).
Proof.
  intros x i ls ls' l b Hi Hperm. split.
  - now apply (reordered_set (cmap x) i ls).
  - now repeat split.
Qed.

(* Assigning a literal keeps the rest of the context. *)
Lemma same_rest_assign: forall (x: Ctx) (l: Lit) (r: Reason), SameRest x (assign x l r).
Proof.
  intros x l r. split.
  - apply reordered_refl.
  - now repeat split.
Qed.

(* A clause c0 :: c1 :: ls watching p is put in the form o :: p :: ls, o its other watch:
   the same literals, and the same watches. *)
Lemma put_second: forall (p c0 c1: Lit) (ls: list Lit),
  (c0 =? p) || (c1 =? p) = true ->
  Permutation (c0 :: c1 :: ls) ((if c0 =? p then c1 else c0) :: p :: ls) /\
  forall (z: Lit), In z (firstn 2 ((if c0 =? p then c1 else c0) :: p :: ls)) <->
    In z (firstn 2 (c0 :: c1 :: ls)).
Proof.
  intros p c0 c1 ls Hwatching. destruct (c0 =? p) eqn:Hc0.
  - apply Lit.eqb_eq in Hc0 as ->. split.
    + apply perm_swap.
    + intros z. simpl. split.
      * intros [<-|[<-|[]]].
        -- right. now left.
        -- now left.
      * intros [<-|[<-|[]]].
        -- right. now left.
        -- now left.
  - simpl in Hwatching. apply Lit.eqb_eq in Hwatching as ->. split.
    + apply Permutation_refl.
    + intros z. reflexivity.
Qed.

(* The visit of a watcher of the clause o :: p :: ls, the rest of ws being visited as IH
   says: keep it with blocker o if o is true, move the watch from p, propagate o, or stop
   at a conflict. *)
Lemma visit_watched_spec: forall (p: Lit) (i: nat) (b: Lit) (rest kept: list Watcher)
  (m m': PA) (f: CNF) (x1 x': Ctx) (r: option nat) (o: Lit) (ls: list Lit),
  VisitInv p kept ((i, b) :: rest) m f x1 -> tget (cmap x1) i = Some (o :: p :: ls) ->
  (forall (kept': list Watcher) (m0 m0': PA) (x0 x0': Ctx) (r0: option nat),
     VisitInv p kept' rest m0 f x0 -> visit p rest kept' m0 x0 = (m0', x0', r0) ->
     VisitOut p m0 f x0 m0' x0' r0) ->
  (if lookup_true (vals x1) o then visit p rest ((i, o) :: kept) m x1 else
   match swap_watch (vals x1) p ls with
   | Some (r', ls') => visit p rest kept m (move_watch x1 i (o :: r' :: ls') r' o)
   | None           =>
     if lookup_undef (vals x1) o then
       visit p rest ((i, o) :: kept) ⟨m, o⟩ (assign x1 o (input i))
     else (m, set_watching x1 p (rev_append kept ((i, b) :: rest)), Some i)
   end) = (m', x', r) ->
  VisitOut p m f x1 m' x' r.
Proof.
  intros p i b rest kept m m' f x1 x' r o ls Hinv Hi IH Hvisit.
  pose proof (visit_p_false p kept ((i, b) :: rest) m f x1 Hinv) as Hp.
  destruct (lookup_true (vals x1) o) eqn:Ho.
  (* The other watch is true: keep the watcher, with blocker o *)
  - apply (IH ((i, o) :: kept) m m' x1 x' r).
    + apply visit_inv_keep with b.
      * assumption.
      * intros ls' Hi'. rewrite Hi in Hi'. injection Hi' as <-. now left.
      * unfold lookup_true in Ho. destruct (lookup (vals x1) o) as [[|]|]; easy.
    + assumption.
  - destruct (swap_watch (vals x1) p ls) as [[r' ls']|] eqn:Hswap.
    (* Move the watch from p to r' *)
    + apply swap_watch_some in Hswap as (Hr_in & Hr & Hperm).
      apply (visit_out_before p m m m' f x1 (move_watch x1 i (o :: r' :: ls') r' o) x' r).
      * apply rt_refl.
      * apply (same_rest_move x1 i (o :: p :: ls)).
        -- assumption.
        -- apply perm_skip. now apply Permutation_sym.
      * apply incl_refl.
      * apply (IH kept m m' _ x' r).
        -- now apply (visit_inv_move p i b rest kept m f x1 o r' ls ls').
        -- assumption.
    + pose proof (swap_watch_none (vals x1) p ls Hswap) as Hfalse.
      destruct (lookup_undef (vals x1) o) eqn:Hu.
      (* Unit: propagate o *)
      * assert (Hu': lookup (vals x1) o = None)
          by (unfold lookup_undef in Hu; destruct (lookup (vals x1) o); easy).
        assert (Hothers: forall (y: Lit), In y (o :: p :: ls) -> y <> o ->
                           lookup (vals x1) y = Some false).
        { intros y [<-|[<-|Hy]] Hyo.
          - contradiction.
          - assumption.
          - now apply Hfalse. }
        apply (visit_out_before p m ⟨m, o⟩ m' f x1 (assign x1 o (input i)) x' r).
        -- apply rt_step. apply (visit_unit_step m f x1 i (o :: p :: ls) o).
           ++ apply Hinv.
           ++ assumption.
           ++ now left.
           ++ assumption.
           ++ assumption.
        -- apply same_rest_assign.
        -- apply incl_set_value.
           ++ apply incl_refl.
           ++ assumption.
        -- apply (IH ((i, o) :: kept) ⟨m, o⟩ m' _ x' r).
           ++ apply visit_inv_keep with b.
              ** apply visit_inv_assign.
                 --- assumption.
                 --- assumption.
                 --- apply (reason_input m f x1 i (o :: p :: ls) o).
                     +++ apply Hinv.
                     +++ assumption.
                     +++ now left.
                     +++ assumption.
              ** intros ls' Hi'. simpl in Hi'. rewrite Hi in Hi'. injection Hi' as <-.
                 now left.
              ** apply lookup_add_self.
           ++ assumption.
      (* Conflict: o is false too *)
      * injection Hvisit as <- <- <-. apply visit_out_end.
        -- assumption.
        -- intros Heq. discriminate.
        -- intros j Heq. injection Heq as <-. exists (o :: p :: ls). split.
           ++ assumption.
           ++ intros y [<-|[<-|Hy]].
              ** unfold lookup_true in Ho. unfold lookup_undef in Hu.
                 destruct (lookup (vals x1) o) as [[|]|]; easy.
              ** assumption.
              ** now apply Hfalse.
Qed.

(* The result of a visit. *)
Lemma visit_spec: forall (p: Lit) (ws kept: list Watcher) (m m': PA) (f: CNF) (x x': Ctx)
  (r: option nat),
  VisitInv p kept ws m f x -> visit p ws kept m x = (m', x', r) ->
    VisitOut p m f x m' x' r.
Proof.
  intros p ws.
  induction ws as
    [|[i b] rest IH]; intros kept m m' f x x' r Hinv Hvisit; simpl in Hvisit.
  (* All visited: the kept watchers go back into the watch list of p *)
  - injection Hvisit as <- <- <-. replace (rev kept) with (rev_append kept []).
    + apply visit_out_end.
      * assumption.
      * now intros _.
      * intros i Heq. discriminate.
    + now rewrite rev_append_rev, app_nil_r.
  - pose proof (visit_p_false p kept ((i, b) :: rest) m f x Hinv) as Hp.
    destruct (lookup_true (vals x) b) eqn:Hb.
    (* The blocker is true: keep the watcher *)
    + apply (IH ((i, b) :: kept) m m' f x x' r).
      * apply visit_inv_keep with b.
        -- assumption.
        -- intros ls Hi. apply (vi_blockers _ _ _ _ _ _ Hinv i b ls).
           ++ apply in_app_iff. right. now left.
           ++ assumption.
        -- unfold lookup_true in Hb. destruct (lookup (vals x) b) as [[|]|]; easy.
      * assumption.
    + destruct (tget (cmap x) i) as [[|c0 [|c1 ls]]|] eqn:Hi.
      (* The empty clause watches nothing *)
      * apply (IH kept m m' f x x' r).
        -- apply (visit_inv_drop p i b).
           ++ assumption.
           ++ intros ls Hi'. rewrite Hi in Hi'. injection Hi' as <-. intros [].
        -- assumption.
      (* A unit clause: false if it is [p] *)
      * destruct (c0 =? p) eqn:Hc0.
        -- injection Hvisit as <- <- <-. apply visit_out_end.
           ++ assumption.
           ++ intros Heq. discriminate.
           ++ intros j Heq. injection Heq as <-. exists [c0]. split.
              ** assumption.
              ** apply Lit.eqb_eq in Hc0 as ->. intros y [<-|[]]. assumption.
        -- apply (IH kept m m' f x x' r).
           ++ apply (visit_inv_drop p i b).
              ** assumption.
              ** intros ls Hi'. rewrite Hi in Hi'. injection Hi' as <-. intros [Heq|[]].
                 apply Lit.eqb_neq in Hc0. contradiction.
           ++ assumption.
      * destruct ((c0 =? p) || (c1 =? p)) eqn:Hwatching.
        (* The clause watches p: put it in the form o :: p :: ls *)
        -- destruct (put_second p c0 c1 ls Hwatching) as [Hperm Hsame].
           apply (visit_out_before p m m m' f x
                    (set_clause x i ((if c0 =? p then c1 else c0) :: p :: ls)) x' r).
           ++ apply rt_refl.
           ++ now apply (same_rest_set_clause x i (c0 :: c1 :: ls)).
           ++ apply incl_refl.
           ++ apply (visit_watched_spec p i b rest kept m m' f _ x' r
                       (if c0 =? p then c1 else c0) ls).
              ** now apply (visit_inv_reorder p i _ kept m f x (c0 :: c1 :: ls)).
              ** apply tget_tset_same.
              ** intros kept' m0 m0' x0 x0' r0 Hinv0 Hvisit0.
                 now apply (IH kept' m0 m0' f x0 x0' r0).
              ** assumption.
        (* The clause does not watch p *)
        -- apply (IH kept m m' f x x' r).
           ++ apply (visit_inv_drop p i b).
              ** assumption.
              ** intros ls' Hi'. rewrite Hi in Hi'. injection Hi' as <-.
                 apply orb_false_iff in Hwatching as [H0 H1]. apply Lit.eqb_neq in H0, H1.
                 intros [Heq|[Heq|[]]].
                 --- now apply H0.
                 --- now apply H1.
           ++ assumption.
      (* Not a clause *)
      * apply (IH kept m m' f x x' r).
        -- apply (visit_inv_drop p i b).
           ++ assumption.
           ++ intros ls Hi'. congruence.
        -- assumption.
Qed.

(* Between visits: the watches are fine up to the queue from qhead on, and the watch lists
   are complete, with blockers from their clauses. *)
Record PropInv (m: PA) (f: CNF) (x: Ctx): Prop := {
  pi_core: Core m f x;
  pi_qhead: qhead x <= tlen x;
  pi_watch: AllWatchQ (vals x) (Queued (tr x) (qhead x) (tlen x)) (cmap x);
  pi_saved: SavedQ (cmap x) m;
  pi_listed: Listed (cmap x) (wls x);
  pi_blocked: Blocked (cmap x) (wls x)
}.

(* The parts of the context that propagation does not change, but for the order of the
   literals of clauses. *)
Definition SameFixed (x x': Ctx): Prop :=
  Reordered (cmap x) (cmap x') /\ shorts x' = shorts x /\ alls x' = alls x /\
    nlits x' = nlits x /\
  cur x' = cur x /\ saved x' = saved x /\ dl x' = dl x /\ mrk x' = mrk x /\
    nvars x' = nvars x /\ rcl x' = rcl x /\ rps x' = rps x /\ nr x' = nr x /\
  rcap x' = rcap x /\ hr x' = hr x.

Lemma same_fixed_trans: forall (x1 x2 x3: Ctx), SameFixed x1 x2 -> SameFixed x2 x3 -> SameFixed x1 x3.
Proof.
  intros x1 x2 x3
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14)
    (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
  split.
  - now apply reordered_trans with (cmap x2).
  - repeat split; congruence.
Qed.

Lemma same_rest_fixed: forall (x x': Ctx), SameRest x x' -> SameFixed x x'.
Proof.
  intros x x'
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15).
  now repeat split.
Qed.

(* The trail of a context is at most nvars long. *)
Lemma trail_bound: forall (m: PA) (f: CNF) (x: Ctx),
  Core m f x -> WellFormed (state m f) -> S (max_atom_f f) <= nvars x -> tlen x <= nvars x.
Proof.
  intros m f x [_ _ [Hlen _] _ _ _ _] Hwf Hbound. rewrite Hlen, trail_lits_length.
  apply well_formed_length_le in Hwf.
  lia.
Qed.

(* The visit of the watchers of the first queued literal starts with nothing kept. *)
Lemma visit_inv_start: forall (m: PA) (f: CNF) (x: Ctx),
  PropInv m f x -> qhead x < tlen x ->
  VisitInv (¬(tget (tr x) (qhead x))) []
    (watching (wls x) (¬(tget (tr x) (qhead x)))) m f x.
Proof.
  intros m f x [Hcore Hq Hwatch Hsaved Hlisted Hblocked] Hlt. split.
  - assumption.
  - assumption.
  - now rewrite Neg.involutive.
  - assumption.
  - assumption.
  - intros i ls z Hi Hz. split.
    + intros _. now apply (Hlisted i ls).
    + intros ->. simpl. now apply (Hlisted i ls).
  - intros l _. apply Hblocked.
  - simpl. apply Hblocked.
  - intros i b ls [].
Qed.

(* After a visit of the watchers of p without conflict, ¬p leaves the queue. *)
Lemma prop_inv_advance: forall (p: Lit) (m0 m: PA) (f: CNF) (x0 x: Ctx),
  VisitOut p m0 f x0 m x None -> PropInv m f (advance x).
Proof.
  intros p m0 m f x0 x [_ _ _ Hcore Hq Hhead Hwatch Hsaved Hlisted Hblocked Hdone _].
  split; simpl.
  - now apply (core_ext m f x).
  - lia.
  - intros i ls Hi w Hw Hf. destruct (Hwatch i ls Hi w Hw Hf) as [[k [Hk Hy]]|Ht].
    + destruct (Nat.eq_dec k (qhead x)) as [->|Hne].
      (* The literal leaving the queue is ¬p: the clause watches p, so it has a true
         literal *)
      * right. apply (Hdone eq_refl i).
        -- assumption.
        -- rewrite Hhead in Hy.
           rewrite <- (Neg.involutive w), <- Hy, Neg.involutive in Hw. assumption.
      * left. exists k. split.
        -- lia.
        -- assumption.
    + now right.
  - assumption.
  - assumption.
  - assumption.
Qed.

(* Propagation takes Unit steps until the queue is empty, or stops at a false clause. *)
Lemma propagate_spec: forall (fuel: nat) (m m': PA) (f: CNF) (x x': Ctx) (r: option nat),
  PropInv m f x ->
  WellFormed (state m f) ->
  S (max_atom_f f) <= nvars x ->
  nvars x - qhead x < fuel ->
  propagate fuel m x = (m', x', r) ->
  state m f ==>*[DPLL_BJ] state m' f /\ SameFixed x x' /\ Incl (vals x) (vals x') /\ PropInv m' f x' /\
  (r = None -> qhead x' = tlen x') /\
  (forall (i: nat), r = Some i ->
    exists (ls: list Lit), tget (cmap x') i = Some ls /\ forall (y: Lit), In y ls -> lookup (vals x') y = Some false).
Proof.
  intros fuel. induction fuel as [|fuel IH]; intros m m' f x x' r Hinv Hwf Hbound Hfuel Hprop.
  - lia.
  - simpl in Hprop. destruct (qhead x <? tlen x) eqn:Hlt.
    + apply Nat.ltb_lt in Hlt. set (p := ¬(tget (tr x) (qhead x))) in Hprop.
      destruct (visit p (watching (wls x) p) [] m x) as [[m1 x1] r1] eqn:Hvisit.
      assert (Hout: VisitOut p m f x m1 x1 r1).
      * apply (visit_spec p (watching (wls x) p) []).
        -- now apply visit_inv_start.
        -- assumption.
      * destruct r1 as [i|].
        (* A conflict *)
        -- injection Hprop as <- <- <-. split.
           ++ apply Hout.
           ++ split.
              ** apply same_rest_fixed, Hout.
              ** split.
                 --- apply Hout.
                 --- split.
                     +++ split.
                         *** apply Hout.
                         *** pose proof (vo_qhead _ _ _ _ _ _ _ Hout). lia.
                         *** apply Hout.
                         *** apply Hout.
                         *** apply Hout.
                         *** apply Hout.
                     +++ split.
                         *** intros Heq. discriminate.
                         *** apply Hout.
        (* The watchers of p are done: move on *)
        -- pose proof (vo_rest _ _ _ _ _ _ _ Hout) as
             (_ & Hqh & _ & _ & _ & _ & _ & _ & _ & Hnv & _).
           assert (Hwf1: WellFormed (state m1 f)).
           ++ apply (derivation_well_formed DPLL_BJ m m1 f f).
              ** apply Hout.
              ** assumption.
           ++ destruct (IH m1 m' f (advance x1) x' r) as (Hder' & Hfixed' & Hincl' & Hres').
              ** now apply (prop_inv_advance p m m1 f x x1).
              ** assumption.
              ** simpl. now rewrite Hnv.
              ** simpl. rewrite Hnv.
                 pose proof
                   (trail_bound m1 f x1 (vo_core _ _ _ _ _ _ _ Hout) Hwf1) as Hbound1.
                 rewrite Hnv in Hbound1. specialize (Hbound1 Hbound).
                 pose proof (vo_qhead _ _ _ _ _ _ _ Hout). lia.
              ** assumption.
              ** split.
                 --- apply rt_trans with (state m1 f).
                     +++ apply Hout.
                     +++ assumption.
                 --- split.
                     +++ apply (same_fixed_trans _ x1).
                         *** apply same_rest_fixed, Hout.
                         *** apply (same_fixed_trans _ (advance x1)).
                             ---- split.
                                  ++++ apply reordered_refl.
                                  ++++ now repeat split.
                             ---- assumption.
                     +++ split.
                         *** apply incl_trans with (vals x1).
                             ---- apply Hout.
                             ---- assumption.
                         *** assumption.
    + injection Hprop as <- <- <-. apply Nat.ltb_ge in Hlt. split.
      * apply rt_refl.
      * split.
        -- split.
           ++ apply reordered_refl.
           ++ now repeat split.
        -- split.
           ++ apply incl_refl.
           ++ split.
              ** assumption.
              ** split.
                 --- intros _. destruct Hinv as [_ Hq _ _ _ _]. lia.
                 --- intros i Heq. discriminate.
Qed.

(* Assigning an unassigned literal keeps propagation consistent: it is queued. *)
Lemma prop_inv_assign: forall (m: PA) (f: CNF) (x: Ctx) (l: Lit) (r: Reason),
  PropInv m f x -> lookup (vals x) l = None ->
  ReasonOk (cmap x) (rcl x) (rps x) (nr x) m l r -> PropInv ⟨m, l⟩ f (assign x l r).
Proof.
  intros m f x l r [Hcore Hq Hwatch Hsaved Hlisted Hblocked] Hl Hr. split.
  - now apply core_assign.
  - simpl. lia.
  - intros j ls Hj. simpl in Hj |- *.
    apply (watch_q_assign (vals x) (Queued (tr x) (qhead x) (tlen x))).
    + now apply (Hwatch j).
    + assumption.
    + intros y. apply queued_cons.
    + now apply queued_new.
  - assumption.
  - assumption.
  - assumption.
Qed.

(* A clause that is not empty is not empty after reordering. *)
Lemma reordered_not_empty: forall (cm cm': ClauseMap) (i: nat) (ls ls': list Lit),
  Reordered cm cm' -> tget cm i = Some ls -> tget cm' i = Some ls' -> ls <> [] ->
    ls' <> [].
Proof.
  intros cm cm' i ls ls' Hre Hi Hi' Hne ->. apply (reordered_empty cm cm' i Hre) in Hi'.
  congruence.
Qed.

(* Checking the short clauses ss takes Unit steps for their unassigned literals, or stops at a false one. *)
Lemma check_shorts_spec: forall (ss: list nat) (m m': PA) (f: CNF) (x x': Ctx) (r: option nat),
  PropInv m f x ->
  (forall (i: nat) (ls: list Lit), In i ss -> tget (cmap x) i = Some ls -> length ls <= 1) ->
  check_shorts ss m x = (m', x', r) ->
  state m f ==>*[DPLL_BJ] state m' f /\ SameRest x x' /\ Incl (vals x) (vals x') /\ PropInv m' f x' /\
  (r = None -> forall (i: nat) (ls: list Lit), In i ss -> tget (cmap x') i = Some ls -> ls <> []) /\
  (forall (i: nat), r = Some i ->
    exists (ls: list Lit), tget (cmap x') i = Some ls /\ forall (y: Lit), In y ls -> lookup (vals x') y = Some false).
Proof.
  intros ss. induction ss as [|i ss IH]; intros m m' f x x' r Hinv Hshort Hcheck; simpl in Hcheck.
  - injection Hcheck as <- <- <-. split.
    + apply rt_refl.
    + split.
      * apply same_rest_refl.
      * split.
        -- apply incl_refl.
        -- split.
           ++ assumption.
           ++ split.
              ** intros _ j ls [].
              ** intros j Heq. discriminate.
  - destruct (tget (cmap x) i) as [[|a ls]|] eqn:Hi.
    (* The empty clause *)
    + injection Hcheck as <- <- <-. split.
      * apply rt_refl.
      * split.
        -- apply same_rest_refl.
        -- split.
           ++ apply incl_refl.
           ++ split.
              ** assumption.
              ** split.
                 --- intros Heq. discriminate.
                 --- intros j Heq. injection Heq as <-. exists []. split.
                     +++ assumption.
                     +++ intros y [].
    + assert (Hls: ls = []).
      * destruct ls as [|b ls].
        -- reflexivity.
        -- specialize (Hshort i (a :: b :: ls) (or_introl eq_refl) Hi). simpl in Hshort. lia.
      * subst ls. destruct (lookup (vals x) a) as [[|]|] eqn:Ha.
        (* Satisfied *)
        -- destruct (IH m m' f x x' r) as (Hder & Hrest & Hincl & Hinv' & Hnone & Hsome).
           ++ assumption.
           ++ intros j ls Hj. apply Hshort. now right.
           ++ assumption.
           ++ repeat (split; try assumption). intros Hr j ls [<-|Hj] Hj'.
              ** apply (reordered_not_empty (cmap x) (cmap x') i [a] ls).
                 --- apply Hrest.
                 --- assumption.
                 --- assumption.
                 --- discriminate.
              ** now apply (Hnone Hr j).
        (* False *)
        -- injection Hcheck as <- <- <-. split.
           ++ apply rt_refl.
           ++ split.
              ** apply same_rest_refl.
              ** split.
                 --- apply incl_refl.
                 --- split.
                     +++ assumption.
                     +++ split.
                         *** intros Heq. discriminate.
                         *** intros j Heq. injection Heq as <-. exists [a]. split.
                             ---- assumption.
                             ---- intros y [<-|[]]. assumption.
        (* Unassigned: propagate it *)
        -- destruct (IH ⟨m, a⟩ m' f (assign x a (input i)) x' r)
             as (Hder & Hrest & Hincl & Hinv' & Hnone & Hsome).
           ++ apply prop_inv_assign.
              ** assumption.
              ** assumption.
              ** apply (reason_input m f x i [a] a).
                 --- apply Hinv.
                 --- assumption.
                 --- now left.
                 --- intros y [<-|[]] Hne. contradiction.
           ++ intros j ls Hj. apply Hshort. now right.
           ++ assumption.
           ++ split.
              ** apply rt_trans with (state ⟨m, a⟩ f).
                 --- apply rt_step. apply (visit_unit_step m f x i [a] a).
                     +++ apply Hinv.
                     +++ assumption.
                     +++ now left.
                     +++ intros y [<-|[]] Hneq. contradiction.
                     +++ assumption.
                 --- assumption.
              ** split.
                 --- apply (same_rest_trans _ (assign x a (input i))).
                     +++ split.
                         *** apply reordered_refl.
                         *** now repeat split.
                     +++ assumption.
                 --- split.
                     +++ apply incl_trans with (vals (assign x a (input i))).
                         *** apply incl_set_value.
                             ---- apply incl_refl.
                             ---- assumption.
                         *** assumption.
                     +++ repeat (split; try assumption). intros Hr j ls [<-|Hj] Hj'.
                         *** apply (reordered_not_empty (cmap (assign x a (input i)))
                               (cmap x') i [a] ls).
                             ---- apply Hrest.
                             ---- assumption.
                             ---- assumption.
                             ---- discriminate.
                         *** now apply (Hnone Hr j).
    (* Not a clause *)
    + destruct (IH m m' f x x' r) as (Hder & Hrest & Hincl & Hinv' & Hnone & Hsome).
      * assumption.
      * intros j ls Hj. apply Hshort. now right.
      * assumption.
      * repeat (split; try assumption). intros Hr j ls [<-|Hj] Hj'.
        -- destruct (reordered_some_l (cmap x) (cmap x') i ls) as [ls0 [Hi0 _]].
           ++ apply Hrest.
           ++ assumption.
           ++ congruence.
        -- now apply (Hnone Hr j).
Qed.
(* m' is m followed by propagations only. *)
Definition Extends (m m': PA): Prop := exists (n: PA), m' = ⟨m ++ n⟩ /\ NoDecisions n.

Lemma extends_refl: forall (m: PA), Extends m m.
Proof. intros m. now exists ⟨⟩. Qed.

Lemma extends_cons: forall (m m': PA) (l: Lit), Extends ⟨m, l⟩ m' -> Extends m m'.
Proof.
  intros m m' l [n [-> Hn]]. exists (PA.app ⟨, l⟩ n). split.
  - symmetry. apply (PA.app_assoc m ⟨, l⟩ n).
  - clear m. induction n as [|n IH l'|n IH l']; simpl in *.
    + easy.
    + now apply IH.
    + destruct Hn.
Qed.

Lemma extends_trans: forall (m1 m2 m3: PA), Extends m1 m2 -> Extends m2 m3 -> Extends m1 m3.
Proof.
  intros m1 m2 m3 [n [-> Hn]] [k [-> Hk]]. exists ⟨n ++ k⟩. split.
  - symmetry. apply PA.app_assoc.
  - induction k as [|k IH l|k IH l]; simpl in *.
    + assumption.
    + now apply IH.
    + destruct Hk.
Qed.

(* Visits, propagation and checking the short clauses only extend the trail by
   propagations. *)

(* Visits, propagation and checking the short clauses only extend the trail by propagations. *)
Lemma visit_extends: forall (p: Lit) (ws kept: list Watcher) (m m': PA) (x x': Ctx)
  (r: option nat),
  visit p ws kept m x = (m', x', r) -> Extends m m'.
Proof.
  intros p ws.
  induction ws as [|[i b] rest IH]; intros kept m m' x x' r Hvisit; simpl in Hvisit.
  - injection Hvisit as <- _ _. apply extends_refl.
  - destruct (lookup_true (vals x) b).
    + now apply IH in Hvisit.
    + destruct (tget (cmap x) i) as [[|c0 [|c1 ls]]|].
      * now apply IH in Hvisit.
      * destruct (c0 =? p).
        -- injection Hvisit as <- _ _. apply extends_refl.
        -- now apply IH in Hvisit.
      * destruct ((c0 =? p) || (c1 =? p)).
        -- destruct (lookup_true _ (if c0 =? p then c1 else c0)).
           ++ now apply IH in Hvisit.
           ++ destruct (swap_watch _ p ls) as [[r' ls']|].
              ** now apply IH in Hvisit.
              ** destruct (lookup_undef _ (if c0 =? p then c1 else c0)).
                 --- apply (extends_cons m m' (if c0 =? p then c1 else c0)).
                     now apply IH in Hvisit.
                 --- injection Hvisit as <- _ _. apply extends_refl.
        -- now apply IH in Hvisit.
      * now apply IH in Hvisit.
Qed.

Lemma propagate_extends: forall (fuel: nat) (m m': PA) (x x': Ctx) (r: option nat),
  propagate fuel m x = (m', x', r) -> Extends m m'.
Proof.
  intros fuel. induction fuel as [|fuel IH]; intros m m' x x' r Hprop; simpl in Hprop.
  - injection Hprop as <- _ _. apply extends_refl.
  - destruct (qhead x <? tlen x).
    + destruct (visit _ _ [] m x) as [[m1 x1] [i|]] eqn:Hvisit.
      * injection Hprop as <- _ _. now apply visit_extends in Hvisit.
      * apply extends_trans with m1.
        -- now apply visit_extends in Hvisit.
        -- now apply (IH m1 m' (advance x1) x' r).
    + injection Hprop as <- _ _. apply extends_refl.
Qed.

Lemma check_shorts_extends: forall (ss: list nat) (m m': PA) (x x': Ctx) (r: option nat),
  check_shorts ss m x = (m', x', r) -> Extends m m'.
Proof.
  intros ss. induction ss as [|i ss IH]; intros m m' x x' r Hcheck; simpl in Hcheck.
  - injection Hcheck as <- _ _. apply extends_refl.
  - destruct (tget (cmap x) i) as [[|a ls]|].
    + injection Hcheck as <- _ _. apply extends_refl.
    + destruct (lookup (vals x) a) as [[|]|].
      * now apply IH in Hcheck.
      * injection Hcheck as <- _ _. apply extends_refl.
      * apply (extends_cons m m' a). now apply IH in Hcheck.
    + now apply IH in Hcheck.
Qed.
