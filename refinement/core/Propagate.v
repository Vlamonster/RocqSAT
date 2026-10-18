From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Permutation.
From Stdlib Require Import Relations.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import State.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import Measure.
From RocqSAT Require Import Trans.
From RocqSAT.rules Require Import Unit.
From RocqSAT.refinement Require Import Tactics.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Search.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import Heur.
From RocqSAT.refinement Require Export Ctx.

(* Unit propagation with a propagation queue, as in MiniSat: the trail is a table, and
   the watchers of the negations of the trail literals from qhead on are still to be
   visited. *)

(* The literals of m, oldest first. *)
Fixpoint trail_lits (m: PA): list Lit :=
match m with
| ⟨⟩     => []
| ⟨m, l⟩ => trail_lits m ++ [l]
| ⟨m; l⟩ => trail_lits m ++ [l]
end.

(* The table tr holds the literals of m in its first tlen entries. *)
Definition TrailOf (tr: Table Lit) (tlen: nat) (m: PA): Prop :=
  tlen = length (trail_lits m) /\
  forall (j: nat), j < tlen -> tget tr j = nth j (trail_lits m) (Pos 0).

(* l is on the trail from position q on, so the watchers of ¬l are still to be visited. *)
Definition Queued (tr: Table Lit) (q tlen: nat) (l: Lit): Prop :=
  exists (j: nat), q <= j < tlen /\ tget tr j = l.

(* Some literal of ls is true. *)
Definition SomeTrue (v: Values) (ls: list Lit): Prop :=
  exists (y: Lit), In y ls /\ lookup v y = Some true.

(* The watches of the clause ls, its first two literals, are fine up to the queue Q: a
   false watch has its negation queued, or a literal of the clause is true. *)
Definition WatchQ (v: Values) (Q: Lit -> Prop) (ls: list Lit): Prop :=
  forall (w: Lit), In w (firstn 2 ls) -> lookup v w = Some false ->
  Q (¬w) \/ SomeTrue v ls.

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

(* Assign l with reason r at the current level, appending it to the trail. *)
Definition assign (x: Ctx) (l: Lit) (r: Reason): Ctx :=
mkCtx (set_value (vals x) l) (cmap x) (wls x) (tset (tr x) (tlen x) l) (S (tlen x))
  (qhead x) (shorts x) (alls x) (nlits x) (cur x) (saved x) (lims x)
  (tset (rsn x) (extract l) r) (tset (lvl x) (extract l) (dl x)) (dl x) (mrk x) (lower x)
  (set_value (phs x) l) (nvars x) (rcl x) (rps x) (nr x) (rcap x) (hr x).

(* Clause i now has the literals ls. *)
Definition set_clause (x: Ctx) (i: nat) (ls: list Lit): Ctx :=
mkCtx (vals x) (tset (cmap x) i (Some ls)) (wls x) (tr x) (tlen x) (qhead x) (shorts x)
  (alls x) (nlits x) (cur x) (saved x) (lims x) (rsn x) (lvl x) (dl x) (mrk x) (lower x)
  (phs x) (nvars x) (rcl x) (rps x) (nr x) (rcap x) (hr x).

(* Clause i now has the literals ls, and a watcher of it with blocker b is appended to the
   watch list of l. *)
Definition move_watch (x: Ctx) (i: nat) (ls: list Lit) (l b: Lit): Ctx :=
mkCtx (vals x) (tset (cmap x) i (Some ls))
  (tset (wls x) (lit_key l) (watching (wls x) l ++ [(i, b)])) (tr x) (tlen x) (qhead x)
  (shorts x) (alls x) (nlits x) (cur x) (saved x) (lims x) (rsn x) (lvl x) (dl x) (mrk x)
  (lower x) (phs x) (nvars x) (rcl x) (rps x) (nr x) (rcap x) (hr x).

(* The watch list of l becomes ws. *)
Definition set_watching (x: Ctx) (l: Lit) (ws: list Watcher): Ctx :=
mkCtx (vals x) (cmap x) (tset (wls x) (lit_key l) ws) (tr x) (tlen x) (qhead x) (shorts x)
  (alls x) (nlits x) (cur x) (saved x) (lims x) (rsn x) (lvl x) (dl x) (mrk x) (lower x)
  (phs x) (nvars x) (rcl x) (rps x) (nr x) (rcap x) (hr x).

(* The queue moves past one literal. *)
Definition advance (x: Ctx): Ctx :=
mkCtx (vals x) (cmap x) (wls x) (tr x) (tlen x) (S (qhead x)) (shorts x) (alls x)
  (nlits x) (cur x) (saved x) (lims x) (rsn x) (lvl x) (dl x) (mrk x) (lower x) (phs x)
  (nvars x) (rcl x) (rps x) (nr x) (rcap x) (hr x).

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
Fixpoint visit (p: Lit) (ws kept: list Watcher) (x: Ctx): Ctx * option nat :=
match ws with
| []             => (set_watching x p (rev kept), None)
| (i, b) :: rest =>
  if lookup_true (vals x) b then visit p rest ((i, b) :: kept) x else
  match tget (cmap x) i with
  | Some [a]              =>
    if a =? p then
      (set_watching x p (rev_append kept ws), Some i) else visit p rest kept x
  | Some (c0 :: c1 :: ls) =>
    if (c0 =? p) || (c1 =? p) then
      let o := if c0 =? p then c1 else c0 in
      let x1 := set_clause x i (o :: p :: ls) in
      if lookup_true (vals x1) o then visit p rest ((i, o) :: kept) x1 else
      match swap_watch (vals x1) p ls with
      | Some (r, ls') => visit p rest kept (move_watch x1 i (o :: r :: ls') r o)
      | None          =>
        if lookup_undef (vals x1) o then visit p rest ((i, o) :: kept)
          (assign x1 o (input i))
        else (set_watching x1 p (rev_append kept ws), Some i)
      end
    else visit p rest kept x
  | _                     => visit p rest kept x
  end
end.

(* Visit the watchers of the queued literals, at most fuel of them, until a conflict. *)
Fixpoint propagate (fuel: nat) (x: Ctx): Ctx * option nat :=
match fuel with
| 0       => (x, None)
| S fuel' =>
  if qhead x <? tlen x then
    let p := ¬(tget (tr x) (qhead x)) in
    match visit p (watching (wls x) p) [] x with
    | (x', Some i) => (x', Some i)
    | (x', None)   => propagate fuel' (advance x')
    end
  else (x, None)
end.

(* Check the clauses ss with fewer than two literals: propagate the unassigned ones, until
   a conflict. *)
Fixpoint check_shorts (ss: list nat) (x: Ctx): Ctx * option nat :=
match ss with
| []       => (x, None)
| i :: ss' =>
  match tget (cmap x) i with
  | Some (a :: _) =>
    match lookup (vals x) a with
    | Some true  => check_shorts ss' x
    | Some false => (x, Some i)
    | None       => check_shorts ss' (assign x a (input i))
    end
  | Some []       => (x, Some i)
  | None          => check_shorts ss' x
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

(* The reason r justifies t after m, with the clauses and reason clauses of x. *)
Abbreviation ReasonOkIn x m t r := (ReasonOk (cmap x) (rcl x) (rps x) (nr x) m t r).

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
Record Core {m: PA} {f: CNF} {x: Ctx}: Prop := {
  core_vals: ValuesOf (vals x) m;
  core_fresh: Fresh m;
  core_trail: TrailOf (tr x) (tlen x) m;
  core_sound: forall (i: nat) (ls: list Lit), tget (cmap x) i = Some ls -> ClauseOf f ls;
  core_nodup: forall (i: nat) (ls: list Lit), tget (cmap x) i = Some ls -> NoDup ls;
  core_dl: dl x = decisions m;
  core_traced: TraceOk (cmap x) (rsn x) (lvl x) (rcl x) (rps x) (nr x) m
}.
Arguments Core : clear implicits.

Section Trail.
  (* A trail has as many literals as its length. *)
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

  (* The appended literal is queued. *)
  Lemma queued_new: forall (tr: Table Lit) (q tlen: nat) (l: Lit),
    q <= tlen -> Queued (tset tr tlen l) q (S tlen) l.
  Proof.
    intros tr q tlen l Hq. exists tlen. split.
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

  (* The trail before the decision l of ⟨m; l ++ n⟩ is fresh, and l unassigned in it. *)
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

  (* A table holding m', the literals of m and then t, has t at position |m| and holds m
     before it. *)
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

(* The empty queue. *)
Abbreviation NoQueue := (fun (_: Lit) => False).

(* At every decision of m, the watches are fine up to an empty queue with respect to the
   values before it, so a backjump can keep them. *)
Fixpoint SavedQ (cm: ClauseMap) (m: PA): Prop :=
match m with
| ⟨⟩     => True
| ⟨m, _⟩ => SavedQ cm m
| ⟨m; _⟩ => AllWatchQ (values m) NoQueue cm /\ SavedQ cm m
end.

(* Clause i of x has only false literals: a conflict. *)
Abbreviation ClauseFalse x i :=
  (exists (ls: list Lit), tget (cmap x) i = Some ls /\
     forall (y: Lit), In y ls -> lookup (vals x) y = Some false).

(* No clause of x is empty. *)
Abbreviation NoEmpty x := (forall (i: nat), tget (cmap x) i <> Some []).

(* The fields of the context that propagation does not change. *)
Definition kept (x: Ctx) :=
  (shorts x, alls x, nlits x, cur x, saved x, dl x, mrk x, nvars x, rcl x, rps x, nr x,
   rcap x, hr x).

(* x' has the clauses of x, reordered, and its kept fields. *)
Definition SameFixed (x x': Ctx): Prop :=
  Reordered (cmap x) (cmap x') /\ kept x' = kept x.

(* x' has the positions of the decisions and the lower literals of x: all but backjumps
   and new decisions keep them. *)
Definition SameStacks (x x': Ctx): Prop := lims x' = lims x /\ lower x' = lower x.

(* The same, while the queue stays where it is: the steps of a visit. *)
Definition SameRest (x x': Ctx): Prop := SameFixed x x' /\ qhead x' = qhead x.

(* Each watch of ls' was a watch of ls, or is not false in v. *)
Definition WatchesKept (v: Values) (ls ls': list Lit): Prop :=
  forall (w: Lit), In w (firstn 2 ls') -> In w (firstn 2 ls) \/ lookup v w <> Some false.

Section Reorder.
  (* Every clause map is a reordering of itself. *)
  Lemma reordered_refl: forall (cm: ClauseMap), Reordered cm cm.
  Proof.
    intros cm i. destruct (tget cm i) as [ls|].
    - right. exists ls, ls. now repeat split.
    - now left.
  Qed.

  (* Two reorderings make one. *)
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
      + rewrite H2 in H2'. injection H2' as <-. right. exists ls1, ls3. splits.
        * assumption.
        * assumption.
        * now apply Permutation_trans with ls2.
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

  (* A clause of cm' is a reordered clause of cm. *)
  Lemma reordered_some_l: forall (cm cm': ClauseMap) (i: nat) (ls': list Lit),
    Reordered cm cm' -> tget cm' i = Some ls' ->
      exists (ls: list Lit), tget cm i = Some ls /\ Permutation ls ls'.
  Proof.
    intros cm cm' i ls' Hre Hi.
    destruct (Hre i) as [[_ Hnone]|(ls & ls'' & H & H' & Hperm)].
    - congruence.
    - rewrite Hi in H'. injection H' as <-. now exists ls.
  Qed.

  (* A clause of cm is a reordered clause of cm'. *)
  Lemma reordered_some_r: forall (cm cm': ClauseMap) (i: nat) (ls: list Lit),
    Reordered cm cm' -> tget cm i = Some ls ->
      exists (ls': list Lit), tget cm' i = Some ls' /\ Permutation ls ls'.
  Proof.
    intros cm cm' i ls Hre Hi.
    destruct (Hre i) as [[Hnone _]|(ls'' & ls' & H & H' & Hperm)].
    - congruence.
    - rewrite Hi in H. injection H as <-. now exists ls'.
  Qed.

  (* An empty clause after reordering was empty before. *)
  Lemma reordered_empty: forall (cm cm': ClauseMap) (i: nat),
    Reordered cm cm' -> tget cm' i = Some [] -> tget cm i = Some [].
  Proof.
    intros cm cm' i Hre Hi.
    destruct (reordered_some_l cm cm' i [] Hre Hi) as [ls [Hls Hperm]].
    apply Permutation_sym, Permutation_nil in Hperm. now rewrite <- Hperm.
  Qed.

  (* Reordering keeps the length of a clause. *)
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

  (* A clause with a true literal still has one after reordering. *)
  Lemma some_true_perm: forall (v: Values) (ls ls': list Lit), SomeTrue v ls ->
    Permutation ls ls' -> SomeTrue v ls'.
  Proof.
    intros v ls ls' [y [Hy Ht]] Hperm. exists y. split.
    - now apply Permutation_in with ls.
    - assumption.
  Qed.

  (* A clause with a true literal still has one when values are added. *)
  Lemma some_true_incl: forall (v v': Values) (ls: list Lit), SomeTrue v ls ->
    Incl v v' -> SomeTrue v' ls.
  Proof.
    intros v v' ls [y [Hy Ht]] Hincl. exists y. split.
    - assumption.
    - now apply Hincl.
  Qed.

  (* The watches of a reordered clause stay fine if they are kept. *)
  Lemma watch_q_reorder: forall (v: Values) (Q: Lit -> Prop) (ls ls': list Lit),
    WatchQ v Q ls -> Permutation ls ls' -> WatchesKept v ls ls' -> WatchQ v Q ls'.
  Proof.
    intros v Q ls ls' Hwq Hperm Hnew w Hw Hf. destruct (Hnew w Hw) as [Hold|Hnf].
    - destruct (Hwq w Hold Hf) as [Hq|Ht].
      + now left.
      + right. now apply some_true_perm with ls.
    - contradiction.
  Qed.

  (* Reordering clause i with its watches kept keeps the watches of all clauses fine. *)
  Lemma all_watch_q_reorder: forall (v: Values) (Q: Lit -> Prop) (cm: ClauseMap) (i: nat)
    (ls ls': list Lit),
    AllWatchQ v Q cm -> tget cm i = Some ls -> Permutation ls ls' ->
    WatchesKept v ls ls' ->
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

  #[global] Arguments all_watch_q_reorder {v Q}.

  (* After setting clause i to ls', clause j is ls' if j is i, and as before otherwise. *)
  Lemma tget_set_clause: forall (cm: ClauseMap) (i j: nat) (ls' ls'': list Lit),
    tget (tset cm i (Some ls')) j = Some ls'' ->
    (j = i /\ ls'' = ls') \/ (j <> i /\ tget cm j = Some ls'').
  Proof.
    intros cm i j ls' ls'' Hj. rewrite tget_tset in Hj.
    destruct (Nat.eq_dec i j) as [<-|Hne].
    - left. now injection Hj as <-.
    - right. split.
      + intros Heq. now apply Hne.
      + assumption.
  Qed.
End Reorder.

(* SameFixed and SameRest are preorders. *)
Lemma same_fixed_trans: forall (x1 x2 x3: Ctx),
  SameFixed x1 x2 -> SameFixed x2 x3 -> SameFixed x1 x3.
Proof.
  intros x1 x2 x3 [Hcm12 Hk12] [Hcm23 Hk23]. split.
  - now apply reordered_trans with (cmap x2).
  - congruence.
Qed.

Lemma same_rest_refl: forall (x: Ctx), SameRest x x.
Proof. intros x. split.
  - split.
    + apply reordered_refl.
    + reflexivity.
  - reflexivity.
Qed.

Lemma same_rest_trans: forall (x1 x2 x3: Ctx),
  SameRest x1 x2 -> SameRest x2 x3 -> SameRest x1 x3.
Proof.
  intros x1 x2 x3 [Hfix1 Hq1] [Hfix2 Hq2]. split.
  - now apply same_fixed_trans with x2.
  - congruence.
Qed.

Section Values.
  (* Assigning a literal unassigned in m only adds a value to those of m. *)
  Lemma incl_values_set: forall (m: PA) (l: Lit),
    l_eval m l = None -> Incl (values m) (set_value (values m) l).
  Proof.
    intros m l Hl. apply incl_set_value.
    - apply incl_refl.
    - now rewrite lookup_values.
  Qed.

  (* A literal on a fresh trail is true in its values. *)
  Lemma values_of_in_true: forall (v: Values) (m: PA) (l: Lit),
    ValuesOf v m -> Fresh m -> l ∈ m -> lookup v l = Some true.
  Proof. intros v m l Hv Hfresh Hin. rewrite Hv. now apply fresh_in_true. Qed.

  (* A literal whose negation is on a fresh trail is false in its values. *)
  Lemma values_of_neg_in_false: forall (v: Values) (m: PA) (l: Lit),
    ValuesOf v m -> Fresh m -> ¬l ∈ m -> lookup v l = Some false.
  Proof.
    intros v m l Hv Hfresh Hin. apply (values_of_in_true v) in Hin.
    - rewrite lookup_neg in Hin. destruct (lookup v l) as [[|]|]; easy.
    - assumption.
    - assumption.
  Qed.
End Values.

Section Saved.
  (* Reordering clause i so that its watches are kept in values v that include those of m
     keeps the watches fine at every decision of m. *)
  Lemma saved_q_reorder: forall (cm: ClauseMap) (m: PA) (v: Values) (i: nat)
    (ls ls': list Lit),
    SavedQ cm m ->
    Incl (values m) v ->
    Fresh m ->
    tget cm i = Some ls ->
    Permutation ls ls' ->
    WatchesKept v ls ls' ->
    SavedQ (tset cm i (Some ls')) m.
  Proof.
    intros cm m.
    induction m as
      [|m IH l|m IH l]; intros v i ls ls' Hsaved Hincl Hfresh Hi Hperm Hnew; simpl in *.
    - easy.
    - destruct Hfresh as [Hfresh Hl]. apply (IH v i ls).
      + assumption.
      + apply incl_trans with (set_value (values m) l).
        * now apply incl_values_set.
        * assumption.
      + assumption.
      + assumption.
      + assumption.
      + assumption.
    - destruct Hfresh as [Hfresh Hl]. destruct Hsaved as [Hall Hsaved].
      assert (Hincl': Incl (values m) v).
      + apply incl_trans with (set_value (values m) l).
        * now apply incl_values_set.
        * assumption.
      + split.
        * apply (all_watch_q_reorder cm i ls).
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

(* The invariant of a visit of the watchers of p, whose negation is the first queued
   literal: the clauses watching p have their watchers in kept or ws instead of the watch
   list of p, the clauses of kept have a true literal, and all blockers outside the watch
   list of p are literals of their clauses. *)
Record VisitInv {p: Lit} {kept ws: list Watcher} {m: PA} {f: CNF} {x: Ctx}: Prop := {
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
Arguments VisitInv : clear implicits.

(* The visited literal p is false. *)
Lemma visit_p_false: forall (p: Lit) (kept ws: list Watcher) (m: PA) (f: CNF) (x: Ctx),
  VisitInv p kept ws m f x -> lookup (vals x) p = Some false.
Proof.
  intros p kept ws m f x [[Hvals Hfresh Htrail _ _] Hq Hhead _ _ _ _ _ _].
  apply (values_of_neg_in_false _ m).
  - assumption.
  - assumption.
  - rewrite <- Hhead. now apply (trail_of_in _ (tlen x)).
Qed.

Section Traces.
  Variables (cm: ClauseMap) (rsn: Table Reason) (lv: Table nat) (rcl: Table (list Lit))
    (rps: Table nat) (nr: nat).

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
  Lemma trace_other: forall (m: PA) (a: nat) (r: Reason) (k: nat),
    (forall (y: Lit), y ∈ m -> extract y <> a) ->
    TraceOk cm rsn lv rcl rps nr m ->
    TraceOk cm (tset rsn a r) (tset lv a k) rcl rps nr m.
  Proof.
    intros m a r k.
    induction m as [|m IH t|m IH t]; intros Hother Htrace.
    - constructor.
    - destruct Htrace as (Hlv & Hrsn & Htrace). cbn [TraceOk].
      assert (Ht: a <> extract t).
      { intros Heq. apply (Hother t).
        - now left.
        - now symmetry. }
      rewrite !tget_tset_other by assumption. splits.
      + assumption.
      + assumption.
      + apply IH.
        * intros y Hy. apply Hother. now right.
        * assumption.
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
  Lemma trace_reorder: forall (m: PA) (i: nat) (ls ls': list Lit),
    tget cm i = Some ls -> Permutation ls ls' ->
    TraceOk cm rsn lv rcl rps nr m -> TraceOk (tset cm i (Some ls')) rsn lv rcl rps nr m.
  Proof.
    intros m i ls ls' Hi Hperm.
    induction m as [|m IH t|m IH t]; intros Htrace.
    - constructor.
    - destruct Htrace as (Hlv & Hrsn & Htrace). cbn [TraceOk]. splits.
      + assumption.
      + destruct (tget rsn (extract t)) as [|j|j]; cbn [ReasonOk] in Hrsn |- *.
        * constructor.
        * destruct Hrsn as (ls0 & Hj & Hjust). rewrite tget_tset.
          destruct (Nat.eq_dec i j) as [<- | Hne].
          -- exists ls'. split.
             ++ reflexivity.
             ++ rewrite Hi in Hj. injection Hj as <-.
                now apply (justifies_perm m t ls).
          -- now exists ls0.
        * assumption.
      + now apply IH.
    - destruct Htrace as (Hlv & Htrace). cbn [TraceOk]. split.
      + assumption.
      + now apply IH.
  Qed.
End Traces.

(* l is in ls, and the other literals of ls are false in v. *)
Abbreviation UnitIn v l ls :=
  (In l ls /\ forall (y: Lit), In y ls -> y <> l -> lookup v y = Some false).

(* The clause [l] is a unit clause for l. *)
Lemma unit_in_single: forall (v: Values) (l: Lit), UnitIn v l [l].
Proof.
  intros v l. split.
  - now left.
  - intros y [<-|[]] Hne. contradiction.
Qed.

(* The fields of the context that Core reads. *)
Definition core_fields (x: Ctx) :=
  (vals x, tr x, tlen x, cmap x, rsn x, lvl x, dl x, rcl x, rps x, nr x).

(* Core only looks at the values, the trail, the clauses and the levels and reasons. *)
Lemma core_ext: forall (m: PA) (f: CNF) (x x': Ctx),
  Core m f x -> core_fields x' = core_fields x -> Core m f x'.
Proof.
  intros m f x x' [Hvals Hfresh Htrail Hsound Hnodup Hdl Htrace] Hfields.
  injection Hfields as Hv Htr Hlen Hcm Hrsn Hlv Hd Hrcl Hrps Hnr. split.
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
  ReasonOkIn x m l r -> Core ⟨m, l⟩ f (assign x l r).
Proof.
  intros m f x l r [Hvals Hfresh Htrail Hsound Hnodup Hdl Htrace] Hl Hr.
  assert (Hundef: l_eval m l = None) by now rewrite <- Hvals.
  split.
  - intros y. simpl. now rewrite lookup_add, Hvals.
  - split; assumption.
  - now apply trail_of_cons.
  - assumption.
  - assumption.
  - assumption.
  - cbn [assign cmap rsn lvl rcl rps nr dl TraceOk]. rewrite !tget_tset_same. splits.
    + assumption.
    + assumption.
    + apply trace_other.
      * intros y Hy. now apply (undef_atom m l y).
      * assumption.
Qed.

(* An input clause whose other literals are false justifies l. *)
Lemma reason_input: forall (m: PA) (f: CNF) (x: Ctx) (i: nat) (ls: list Lit) (l: Lit),
  Core m f x -> tget (cmap x) i = Some ls -> UnitIn (vals x) l ls ->
  ReasonOkIn x m l (input i).
Proof.
  intros m f x i ls l Hcore Hi [Hl Hothers]. exists ls. split.
  - assumption.
  - split.
    + assumption.
    + intros y Hy Hne. rewrite <- (core_vals Hcore). now apply Hothers.
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
  - now apply (trace_reorder _ _ _ _ _ _ m i ls).
Qed.

Section VisitSteps.
  (* The values of a trail are included in any values of it. *)
  Lemma values_of_incl: forall (v: Values) (m: PA), ValuesOf v m -> Incl (values m) v.
  Proof. intros v m Hv l b Hl. now rewrite Hv, <- lookup_values. Qed.

  (* A literal false after assigning the unassigned l is ¬l, or was false before. *)
  Lemma lookup_set_false: forall (v: Values) (l y: Lit),
    lookup (set_value v l) y = Some false -> lookup v l = None ->
    y = ¬l \/ lookup v y = Some false.
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
    (f: CNF) (x: Ctx) (ls ls': list Lit),
    VisitInv p kept ws m f x ->
    tget (cmap x) i = Some ls ->
    Permutation ls ls' ->
    (forall (z: Lit), In z (firstn 2 ls') <-> In z (firstn 2 ls)) ->
    VisitInv p kept ws m f (set_clause x i ls').
  Proof.
    intros p i ws kept m f x ls ls'
      [Hcore Hq Hhead Hwatch Hsaved Hlisted Hblocked Hblockers Hkept] Hi Hperm Hsame.
    pose proof Hcore as [Hvals Hfresh Htrail Hsound Hnodup Hdl Htrace].
    split; simpl.
    - now apply (core_reorder m f x i ls).
    - assumption.
    - assumption.
    - apply (all_watch_q_reorder _ i ls).
      + assumption.
      + assumption.
      + assumption.
      + intros w Hw. left. now apply Hsame.
    - apply (saved_q_reorder _ m (vals x) i ls).
      + assumption.
      + now apply values_of_incl.
      + assumption.
      + assumption.
      + assumption.
      + intros w Hw. left. now apply Hsame.
    - intros j ls'' z Hj Hz. apply tget_set_clause in Hj as [[-> ->]|[_ Hj']].
      + apply (Hlisted i ls z Hi). now apply Hsame.
      + now apply (Hlisted j ls'').
    - intros l Hl j c ls'' Hin Hj. apply tget_set_clause in Hj as [[-> ->]|[_ Hj']].
      + apply Permutation_in with ls.
        * assumption.
        * now apply (Hblocked l Hl i c).
      + now apply (Hblocked l Hl j c).
    - intros j c ls'' Hin Hj. apply tget_set_clause in Hj as [[-> ->]|[_ Hj']].
      + apply Permutation_in with ls.
        * assumption.
        * now apply (Hblockers i c).
      + now apply (Hblockers j c).
    - intros j c ls'' Hin Hj. apply tget_set_clause in Hj as [[-> ->]|[_ Hj']].
      + apply some_true_perm with ls.
        * now apply (Hkept i c).
        * assumption.
      + now apply (Hkept j c).
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
      + injection Hswap as <- <-. splits.
        * now left.
        * unfold not_false in Hy. destruct (lookup v y) as [[|]|]; easy.
        * apply perm_swap.
      + destruct (swap_watch v p ls) as [[r' ls1]|] eqn:Hrest.
        * injection Hswap as <- <-. destruct (IH ls1 eq_refl) as (Hin & Hnf & Hperm).
          splits.
          -- now right.
          -- assumption.
          -- apply perm_trans with (y :: r' :: ls1).
             ++ apply perm_swap.
             ++ apply perm_trans with (y :: p :: ls).
                ** now apply perm_skip.
                ** apply perm_swap.
        * discriminate.
  Qed.

  (* If swap_watch finds nothing, all literals of ls are false. *)
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
    intros wl l z e w He. rewrite watching_set. destruct (Lit.eq_dec l z) as [<-|_].
    - apply in_or_app. now left.
    - assumption.
  Qed.

  (* The pushed watcher is in the watch list it was pushed to. *)
  Lemma watching_push_new: forall (wl: WatchLists) (l: Lit) (w: Watcher),
    In w (watching (tset wl (lit_key l) (watching wl l ++ [w])) l).
  Proof.
    intros wl l w. rewrite watching_set.
    destruct (Lit.eq_dec l l) as [_|]; [|contradiction].
    apply in_or_app. right. now left.
  Qed.

  (* The watches o and p and a literal r of the rest of a clause without duplicates
     differ. *)
  Lemma nodup_watches: forall (o p r: Lit) (ls: list Lit),
    NoDup (o :: p :: ls) -> In r ls -> o <> p /\ r <> o /\ r <> p.
  Proof.
    intros o p r ls Hnodup Hr. inversion Hnodup as [|? ? Hnotin Hnodup'].
    inversion Hnodup' as [|? ? Hnotin' _]. splits.
    - intros ->. apply Hnotin. now left.
    - intros ->. apply Hnotin. now right.
    - intros ->. contradiction.
  Qed.

  (* Moving a watch reorders the clause, which keeps it a clause of f. *)
  Lemma core_move: forall (m: PA) (f: CNF) (x: Ctx) (i: nat) (ls ls': list Lit)
    (l b: Lit),
    Core m f x -> tget (cmap x) i = Some ls -> Permutation ls ls' ->
    Core m f (move_watch x i ls' l b).
  Proof.
    intros m f x i ls ls' l b Hcore Hi Hperm.
    apply (core_ext m f (set_clause x i ls')).
    - now apply (core_reorder m f x i ls).
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
    pose proof (core_nodup (vi_core Hinv) i _ Hi) as Hnodup.
    destruct (nodup_watches o p r ls Hnodup Hr_in) as (Hop & Hro & Hrp).
    assert (Hperm': Permutation (o :: p :: ls) (o :: r :: ls')).
    - apply perm_skip. now apply Permutation_sym.
    - (* The new watches: o was a watch, r is not false *)
      assert (Hnew: WatchesKept (vals x) (o :: p :: ls) (o :: r :: ls')).
      + intros w [<-|[<-|[]]].
        * left. now left.
        * now right.
      + pose proof (core_move m f x i _ _ r o (vi_core Hinv) Hi Hperm') as Hcore'.
        destruct Hinv as [Hcore Hq Hhead Hwatch Hsaved Hlisted Hblocked Hblockers Hkept].
        split; simpl.
        * assumption.
        * assumption.
        * assumption.
        * apply (all_watch_q_reorder _ i (o :: p :: ls)); assumption.
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
        * intros l Hl j c ls'' Hin Hj. rewrite watching_set in Hin.
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
    VisitInv p kept ws m f x -> lookup (vals x) l = None -> ReasonOkIn x m l r ->
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
  Lemma visit_unit_step: forall (m: PA) (f: CNF) (x: Ctx) (i: nat) (ls: list Lit)
    (o: Lit),
    Core m f x -> tget (cmap x) i = Some ls -> UnitIn (vals x) o ls ->
    lookup (vals x) o = None -> state m f ==>[DPLL_BJ] state ⟨m, o⟩ f.
  Proof.
    intros m f x i ls o [Hvals _ _ Hsound _] Hi [Ho_in Hrest] Ho.
    apply Hsound in Hi as [c [Hc_in_f Hiff]].
    apply (t_step Unit).
    - right. now left.
    - apply (r_unit m f c o).
      + now apply Hiff.
      + assumption.
      + apply c_eval_false_iff. intros y Hy. apply Clause.remove_spec in Hy as [Hy Hneq].
        rewrite <- Hvals. apply Hrest.
        * now apply Hiff.
        * assumption.
      + unfold Undef. now rewrite <- Hvals.
  Qed.
End VisitSteps2.

(* m' is m followed by propagations only. *)
Definition Extends (m m': PA): Prop := exists (n: PA), m' = ⟨m ++ n⟩ /\ NoDecisions n.

(* Every trail extends itself. *)
Lemma extends_refl: forall (m: PA), Extends m m.
Proof. intros m. now exists ⟨⟩. Qed.

(* One more propagation extends the trail. *)
Lemma extends_snoc: forall (m: PA) (l: Lit), Extends m ⟨m, l⟩.
Proof. intros m l. now exists ⟨, l⟩. Qed.

(* A trail extending m with l added extends m. *)
Lemma extends_cons: forall (m m': PA) (l: Lit), Extends ⟨m, l⟩ m' -> Extends m m'.
Proof.
  intros m m' l [n [-> Hn]]. exists (PA.app ⟨, l⟩ n). split.
  - symmetry. apply (PA.app_assoc m ⟨, l⟩ n).
  - clear m. induction n as [|n IH l'|n IH l']; simpl in *.
    + easy.
    + now apply IH.
    + destruct Hn.
Qed.

(* Extensions of extensions are extensions. *)
Lemma extends_trans: forall (m1 m2 m3: PA),
  Extends m1 m2 -> Extends m2 m3 -> Extends m1 m3.
Proof.
  intros m1 m2 m3 [n [-> Hn]] [k [-> Hk]]. exists ⟨n ++ k⟩. split.
  - symmetry. apply PA.app_assoc.
  - induction k as [|k IH l|k IH l]; simpl in *.
    + assumption.
    + now apply IH.
    + destruct Hk.
Qed.

(* The result of visiting the watchers of the false literal p from m and x: Unit steps
   lead to m', which extends m, and in x' the watch lists are complete again; without a
   conflict r every clause watching p has a true literal, and clause r is false. *)
Record VisitOut {p: Lit} {m: PA} {f: CNF} {x: Ctx} {m': PA} {x': Ctx}
  {r: option nat}: Prop := {
  vo_steps: state m f ==>*[DPLL_BJ] state m' f;
  vo_ext: Extends m m';
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
    ClauseFalse x' i
}.
Arguments VisitOut : clear implicits.

(* A visit from m1 and x1 is one from m and x, if m1 follows from m and x1 from x by
   propagation. *)
Lemma visit_out_before: forall (p: Lit) (m m1: PA) (f: CNF) (x x1 x': Ctx)
  (r: option nat),
  state m f ==>*[DPLL_BJ] state m1 f -> Extends m m1 -> SameRest x x1 ->
  Incl (vals x) (vals x1) -> (exists (m': PA), VisitOut p m1 f x1 m' x' r) ->
  exists (m': PA), VisitOut p m f x m' x' r.
Proof.
  intros p m m1 f x x1 x' r Hsteps Hext Hrest Hincl
    [m' [Hsteps' Hext' Hrest' Hincl' Hcore Hq Hhead Hwatch Hsaved Hlisted
    Hblocked Hdone Hconflict]]. exists m'. split; try assumption.
  - now apply rt_trans with (state m1 f).
  - now apply extends_trans with m1.
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
    ClauseFalse x i) ->
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
    + apply extends_refl.
    + split.
      * split.
        -- apply reordered_refl.
        -- reflexivity.
      * reflexivity.
    + apply incl_refl.
    + now apply (core_ext m f x).
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + intros i ls z Hi Hz. destruct (Hlisted i ls z Hi Hz) as [Hother Hp].
      rewrite watching_set.
      destruct (Lit.eq_dec p z) as [<-|Hne].
      * destruct (Hp eq_refl) as [c Hc]. exists c. now apply Hback.
      * apply Hother. intros Heq. now apply Hne.
    + intros l i c ls Hin Hi. rewrite watching_set in Hin.
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

(* Reordering a clause keeps the rest of the context. *)
Lemma same_rest_set_clause: forall (x: Ctx) (i: nat) (ls ls': list Lit),
  tget (cmap x) i = Some ls -> Permutation ls ls' -> SameRest x (set_clause x i ls').
Proof.
  intros x i ls ls' Hi Hperm. split.
  - split.
    + now apply (reordered_set (cmap x) i ls).
    + reflexivity.
  - reflexivity.
Qed.

(* Moving a watch keeps the rest of the context. *)
Lemma same_rest_move: forall (x: Ctx) (i: nat) (ls ls': list Lit) (l b: Lit),
  tget (cmap x) i = Some ls -> Permutation ls ls' -> SameRest x (move_watch x i ls' l b).
Proof.
  intros x i ls ls' l b Hi Hperm. split.
  - split.
    + now apply (reordered_set (cmap x) i ls).
    + reflexivity.
  - reflexivity.
Qed.

(* Assigning a literal keeps the rest of the context. *)
Lemma same_rest_assign: forall (x: Ctx) (l: Lit) (r: Reason), SameRest x (assign x l r).
Proof.
  intros x l r. split.
  - split.
    + apply reordered_refl.
    + reflexivity.
  - reflexivity.
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

(* Visiting the watchers ws of p from a state of the invariant gives a VisitOut. *)
Definition VisitSpec (p: Lit) (ws: list Watcher) (f: CNF): Prop :=
  forall (kept: list Watcher) (m: PA) (x x': Ctx) (r: option nat),
  VisitInv p kept ws m f x -> visit p ws kept x = (x', r) ->
  exists (m': PA), VisitOut p m f x m' x' r.

(* The visit of a watcher with a false blocker of a clause c0 :: c1 :: ls watching p, the
   rest being visited as VisitSpec says: the clause is put in the form o :: p :: ls, and
   then kept with blocker o if o is true, its watch moves from p, o is propagated, or the
   visit stops at a conflict. *)
Lemma visit_watched_spec: forall (p: Lit) (i: nat) (b: Lit) (rest kept: list Watcher)
  (m: PA) (f: CNF) (x x': Ctx) (r: option nat) (c0 c1: Lit) (ls: list Lit),
  VisitInv p kept ((i, b) :: rest) m f x -> VisitSpec p rest f ->
  lookup_true (vals x) b = false -> tget (cmap x) i = Some (c0 :: c1 :: ls) ->
  (c0 =? p) || (c1 =? p) = true -> visit p ((i, b) :: rest) kept x = (x', r) ->
  exists (m': PA), VisitOut p m f x m' x' r.
Proof.
  intros p i b rest kept m f x x' r c0 c1 ls Hinv0 IH Hb Hi0 Hwatching Hvisit.
  cbn [visit] in Hvisit. rewrite Hb, Hi0, Hwatching in Hvisit.
  destruct (put_second p c0 c1 ls Hwatching) as [Hperm0 Hsame].
  set (o := if c0 =? p then c1 else c0) in *.
  set (x1 := set_clause x i (o :: p :: ls)) in *.
  assert (Hinv: VisitInv p kept ((i, b) :: rest) m f x1)
    by now apply (visit_inv_reorder p i _ kept m f x (c0 :: c1 :: ls)).
  assert (Hi: tget (cmap x1) i = Some (o :: p :: ls)) by apply tget_tset_same.
  pose proof (visit_p_false p kept ((i, b) :: rest) m f x1 Hinv) as Hp.
  enough (Hout: exists (m': PA), VisitOut p m f x1 m' x' r).
  (* The clause is put in the form o :: p :: ls first *)
  - apply (visit_out_before p m m f x x1 x' r).
    + apply rt_refl.
    + apply extends_refl.
    + now apply (same_rest_set_clause x i (c0 :: c1 :: ls)).
    + apply incl_refl.
    + assumption.
  (* The clause in the form o :: p :: ls *)
  - destruct (lookup_true (vals x1) o) eqn:Ho.
    (* The other watch is true: keep the watcher, with blocker o *)
    + apply (IH ((i, o) :: kept) m x1 x' r).
      * apply visit_inv_keep with b.
        -- assumption.
        -- intros ls' Hi'. rewrite Hi in Hi'. injection Hi' as <-. now left.
        -- unfold lookup_true in Ho. destruct (lookup (vals x1) o) as [[|]|]; easy.
      * assumption.
    + destruct (swap_watch (vals x1) p ls) as [[r' ls']|] eqn:Hswap.
      (* Move the watch from p to r' *)
      * apply swap_watch_some in Hswap as (Hr_in & Hr & Hperm).
        apply (visit_out_before p m m f x1 (move_watch x1 i (o :: r' :: ls') r' o) x' r).
        -- apply rt_refl.
        -- apply extends_refl.
        -- apply (same_rest_move x1 i (o :: p :: ls)).
           ++ assumption.
           ++ apply perm_skip. now apply Permutation_sym.
        -- apply incl_refl.
        -- apply (IH kept m _ x' r).
           ++ now apply (visit_inv_move p i b rest kept m f x1 o r' ls ls').
           ++ assumption.
      * pose proof (swap_watch_none (vals x1) p ls Hswap) as Hfalse.
        destruct (lookup_undef (vals x1) o) eqn:Hu.
        (* Unit: propagate o *)
        -- assert (Hu': lookup (vals x1) o = None)
             by (unfold lookup_undef in Hu; destruct (lookup (vals x1) o); easy).
           assert (Hunit: UnitIn (vals x1) o (o :: p :: ls)).
           ++ split.
              ** now left.
              ** intros y [<-|[<-|Hy]] Hyo.
                 --- contradiction.
                 --- assumption.
                 --- now apply Hfalse.
           ++ apply (visit_out_before p m ⟨m, o⟩ f x1 (assign x1 o (input i)) x' r).
              ** apply rt_step. apply (visit_unit_step m f x1 i (o :: p :: ls) o).
                 --- apply Hinv.
                 --- assumption.
                 --- assumption.
                 --- assumption.
              ** apply extends_snoc.
              ** apply same_rest_assign.
              ** apply incl_set_value.
                 --- apply incl_refl.
                 --- assumption.
              ** apply (IH ((i, o) :: kept) ⟨m, o⟩ _ x' r).
                 --- apply visit_inv_keep with b.
                     +++ apply visit_inv_assign.
                         *** assumption.
                         *** assumption.
                         *** apply (reason_input m f x1 i (o :: p :: ls) o).
                             ---- apply Hinv.
                             ---- assumption.
                             ---- assumption.
                     +++ intros ls' Hi'. cbn [assign cmap] in Hi'. rewrite Hi in Hi'.
                         injection Hi' as <-. now left.
                     +++ apply lookup_add_self.
                 --- assumption.
        (* Conflict: o is false too *)
        -- injection Hvisit as <- <-. exists m. apply visit_out_end.
           ++ assumption.
           ++ intros Heq. discriminate.
           ++ intros j Heq. injection Heq as <-. exists (o :: p :: ls). split.
              ** assumption.
              ** intros y [<-|[<-|Hy]].
                 --- unfold lookup_true in Ho. unfold lookup_undef in Hu.
                     destruct (lookup (vals x1) o) as [[|]|]; easy.
                 --- assumption.
                 --- now apply Hfalse.
Qed.

(* Every visit gives a VisitOut. *)
Lemma visit_spec: forall (p: Lit) (ws: list Watcher) (f: CNF), VisitSpec p ws f.
Proof.
  intros p ws f.
  induction ws as [|[i b] rest IH]; intros kept m x x' r Hinv Hvisit.
  (* All visited: the kept watchers go back into the watch list of p *)
  - simpl in Hvisit. injection Hvisit as <- <-. exists m.
    replace (rev kept) with (rev_append kept []).
    + apply visit_out_end.
      * assumption.
      * now intros _.
      * intros i Heq. discriminate.
    + now rewrite rev_append_rev, app_nil_r.
  - pose proof Hvisit as Hvisit_all. simpl in Hvisit.
    destruct (lookup_true (vals x) b) eqn:Hb.
    (* The blocker is true: keep the watcher *)
    + apply (IH ((i, b) :: kept) m x x' r).
      * apply visit_inv_keep with b.
        -- assumption.
        -- intros ls Hi. apply (vi_blockers Hinv i b ls).
           ++ apply in_app_iff. right. now left.
           ++ assumption.
        -- unfold lookup_true in Hb. destruct (lookup (vals x) b) as [[|]|]; easy.
      * assumption.
    + destruct (tget (cmap x) i) as [[|c0 [|c1 ls]]|] eqn:Hi.
      (* The empty clause watches nothing *)
      * apply (IH kept m x x' r).
        -- apply (visit_inv_drop p i b).
           ++ assumption.
           ++ intros ls Hi'. rewrite Hi in Hi'. injection Hi' as <-. intros [].
        -- assumption.
      (* A unit clause: false if it is [p] *)
      * destruct (c0 =? p) eqn:Hc0.
        -- injection Hvisit as <- <-. exists m. apply visit_out_end.
           ++ assumption.
           ++ intros Heq. discriminate.
           ++ intros j Heq. injection Heq as <-. exists [c0]. split.
              ** assumption.
              ** apply Lit.eqb_eq in Hc0 as ->. intros y [<-|[]].
                 now apply (visit_p_false p kept ((i, b) :: rest) m f x).
        -- apply (IH kept m x x' r).
           ++ apply (visit_inv_drop p i b).
              ** assumption.
              ** intros ls Hi'. rewrite Hi in Hi'. injection Hi' as <-. intros [Heq|[]].
                 apply Lit.eqb_neq in Hc0. contradiction.
           ++ assumption.
      * destruct ((c0 =? p) || (c1 =? p)) eqn:Hwatching.
        (* The clause watches p *)
        -- apply (visit_watched_spec p i b rest kept m f x x' r c0 c1 ls).
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ assumption.
        (* The clause does not watch p *)
        -- apply (IH kept m x x' r).
           ++ apply (visit_inv_drop p i b).
              ** assumption.
              ** intros ls' Hi'. rewrite Hi in Hi'. injection Hi' as <-.
                 apply orb_false_iff in Hwatching as [H0 H1]. apply Lit.eqb_neq in H0, H1.
                 intros [Heq|[Heq|[]]].
                 --- now apply H0.
                 --- now apply H1.
           ++ assumption.
      (* Not a clause *)
      * apply (IH kept m x x' r).
        -- apply (visit_inv_drop p i b).
           ++ assumption.
           ++ intros ls Hi'. congruence.
        -- assumption.
Qed.

(* Between visits: the watches are fine up to the queue from qhead on, and the watch lists
   are complete, with blockers from their clauses. *)
Record PropInv {m: PA} {f: CNF} {x: Ctx}: Prop := {
  pi_core: Core m f x;
  pi_qhead: qhead x <= tlen x;
  pi_watch: AllWatchQ (vals x) (Queued (tr x) (qhead x) (tlen x)) (cmap x);
  pi_saved: SavedQ (cmap x) m;
  pi_listed: Listed (cmap x) (wls x);
  pi_blocked: Blocked (cmap x) (wls x)
}.
Arguments PropInv : clear implicits.

(* SameRest is SameFixed and more. *)
Lemma same_rest_fixed: forall (x x': Ctx), SameRest x x' -> SameFixed x x'.
Proof. intros x x' [Hfix _]. assumption. Qed.

(* The trail of a context is at most nvars long. *)
Lemma trail_bound: forall (m: PA) (f: CNF) (x: Ctx),
  Core m f x -> WellFormed (state m f) -> S (max_atom_f f) <= nvars x ->
  tlen x <= nvars x.
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
  intros p m0 m f x0 x [_ _ _ _ Hcore Hq Hhead Hwatch Hsaved Hlisted Hblocked Hdone _].
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
Lemma propagate_spec: forall (fuel: nat) (m: PA) (f: CNF) (x x': Ctx) (r: option nat),
  PropInv m f x ->
  WellFormed (state m f) ->
  S (max_atom_f f) <= nvars x ->
  nvars x - qhead x < fuel ->
  propagate fuel x = (x', r) ->
  exists (m': PA), Extends m m' /\
  state m f ==>*[DPLL_BJ] state m' f /\ SameFixed x x' /\ Incl (vals x) (vals x') /\
  PropInv m' f x' /\ (r = None -> qhead x' = tlen x') /\
  (forall (i: nat), r = Some i -> ClauseFalse x' i).
Proof.
  intros fuel.
  induction fuel as [|fuel IH]; intros m f x x' r Hinv Hwf Hbound Hfuel Hprop.
  - lia.
  - simpl in Hprop. destruct (qhead x <? tlen x) eqn:Hlt.
    + apply Nat.ltb_lt in Hlt. set (p := ¬(tget (tr x) (qhead x))) in Hprop.
      destruct (visit p (watching (wls x) p) [] x) as [x1 r1] eqn:Hvisit.
      destruct (visit_spec p (watching (wls x) p) f [] m x x1 r1) as [m1 Hout].
      * now apply visit_inv_start.
      * assumption.
      * destruct r1 as [i|].
        (* A conflict *)
        -- injection Hprop as <- <-. exists m1. splits.
           ++ apply Hout.
           ++ apply Hout.
           ++ apply same_rest_fixed, Hout.
           ++ apply Hout.
           ++ split.
              ** apply Hout.
              ** pose proof (vo_qhead Hout). lia.
              ** apply Hout.
              ** apply Hout.
              ** apply Hout.
              ** apply Hout.
           ++ intros Heq. discriminate.
           ++ apply Hout.
      (* The watchers of p are done: move on *)
        -- pose proof (vo_rest Hout) as [[_ Hkept] Hqh].
           injection Hkept as _ _ _ _ _ _ _ Hnv _ _ _ _ _.
           assert (Hwf1: WellFormed (state m1 f)).
           ++ apply (derivation_well_formed DPLL_BJ m m1 f f).
              ** apply Hout.
              ** assumption.
           ++ destruct (IH m1 f (advance x1) x' r)
                as (m' & Hext' & Hder' & Hfixed' & Hincl' & Hres').
              ** now apply (prop_inv_advance p m m1 f x x1).
              ** assumption.
              ** simpl. now rewrite Hnv.
              ** simpl. rewrite Hnv.
                 pose proof
                   (trail_bound m1 f x1 (vo_core Hout) Hwf1) as Hbound1.
                 rewrite Hnv in Hbound1. specialize (Hbound1 Hbound).
                 pose proof (vo_qhead Hout). lia.
              ** assumption.
              ** exists m'. split.
                 --- apply extends_trans with m1.
                     +++ apply Hout.
                     +++ assumption.
                 --- split.
                     +++ apply rt_trans with (state m1 f).
                         *** apply Hout.
                         *** assumption.
                     +++ split.
                         *** apply (same_fixed_trans _ x1).
                             ---- apply same_rest_fixed, Hout.
                             ---- apply (same_fixed_trans _ (advance x1)).
                                  ++++ split.
                                       **** apply reordered_refl.
                                       **** reflexivity.
                                  ++++ assumption.
                         *** split.
                             ---- apply incl_trans with (vals x1).
                                  ++++ apply Hout.
                                  ++++ assumption.
                             ---- assumption.
    + injection Hprop as <- <-. apply Nat.ltb_ge in Hlt. exists m. splits.
      * apply extends_refl.
      * apply rt_refl.
      * split.
        -- apply reordered_refl.
        -- reflexivity.
      * apply incl_refl.
      * assumption.
      * intros _. destruct Hinv as [_ Hq _ _ _ _]. lia.
      * intros i Heq. discriminate.
Qed.

(* Assigning an unassigned literal keeps propagation consistent: it is queued. *)
Lemma prop_inv_assign: forall (m: PA) (f: CNF) (x: Ctx) (l: Lit) (r: Reason),
  PropInv m f x -> lookup (vals x) l = None ->
  ReasonOkIn x m l r -> PropInv ⟨m, l⟩ f (assign x l r).
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

(* The clauses of cm in sh have at most one literal. *)
Abbreviation ShortsShort cm sh :=
  (forall (i: nat) (ls: list Lit), In i sh -> tget cm i = Some ls -> length ls <= 1).

(* Checking the short clauses ss takes Unit steps for their unassigned literals, or stops
   at a false one. *)
Lemma check_shorts_spec: forall (ss: list nat) (m: PA) (f: CNF) (x x': Ctx)
  (r: option nat),
  PropInv m f x -> ShortsShort (cmap x) ss ->
  check_shorts ss x = (x', r) ->
  exists (m': PA), Extends m m' /\
  state m f ==>*[DPLL_BJ] state m' f /\ SameRest x x' /\ Incl (vals x) (vals x') /\
  PropInv m' f x' /\
  (r = None -> forall (i: nat) (ls: list Lit), In i ss -> tget (cmap x') i = Some ls ->
     ls <> []) /\
  (forall (i: nat), r = Some i -> ClauseFalse x' i).
Proof.
  intros ss.
  induction ss as [|i ss IH]; intros m f x x' r Hinv Hshort Hcheck; simpl in Hcheck.
  - injection Hcheck as <- <-. exists m. splits.
    + apply extends_refl.
    + apply rt_refl.
    + apply same_rest_refl.
    + apply incl_refl.
    + assumption.
    + intros _ j ls [].
    + intros j Heq. discriminate.
  - destruct (tget (cmap x) i) as [[|a ls]|] eqn:Hi.
    (* The empty clause *)
    + injection Hcheck as <- <-. exists m. splits.
      * apply extends_refl.
      * apply rt_refl.
      * apply same_rest_refl.
      * apply incl_refl.
      * assumption.
      * intros Heq. discriminate.
      * intros j Heq. injection Heq as <-. exists []. split.
        -- assumption.
        -- intros y [].
    + assert (Hls: ls = []).
      * destruct ls as [|b ls].
        -- reflexivity.
        -- specialize (Hshort i (a :: b :: ls) (or_introl eq_refl) Hi). simpl in Hshort.
           lia.
      * subst ls. destruct (lookup (vals x) a) as [[|]|] eqn:Ha.
        (* Satisfied *)
        -- destruct (IH m f x x' r)
             as (m' & Hext & Hder & Hrest & Hincl & Hinv' & Hnone & Hsome).
           ++ assumption.
           ++ intros j ls Hj. apply Hshort. now right.
           ++ assumption.
           ++ exists m'. repeat (split; try assumption). intros Hr j ls [<-|Hj] Hj'.
              ** apply (reordered_not_empty (cmap x) (cmap x') i [a] ls).
                 --- apply Hrest.
                 --- assumption.
                 --- assumption.
                 --- discriminate.
              ** now apply (Hnone Hr j).
        (* False *)
        -- injection Hcheck as <- <-. exists m. splits.
           ++ apply extends_refl.
           ++ apply rt_refl.
           ++ apply same_rest_refl.
           ++ apply incl_refl.
           ++ assumption.
           ++ intros Heq. discriminate.
           ++ intros j Heq. injection Heq as <-. exists [a]. split.
              ** assumption.
              ** intros y [<-|[]]. assumption.
    (* Unassigned: propagate it *)
        -- destruct (IH ⟨m, a⟩ f (assign x a (input i)) x' r)
             as (m' & Hext & Hder & Hrest & Hincl & Hinv' & Hnone & Hsome).
           ++ apply prop_inv_assign.
              ** assumption.
              ** assumption.
              ** apply (reason_input m f x i [a] a).
                 --- apply Hinv.
                 --- assumption.
                 --- apply unit_in_single.
           ++ intros j ls Hj. apply Hshort. now right.
           ++ assumption.
           ++ exists m'. split.
              ** now apply (extends_cons m m' a).
              ** split.
                 --- apply rt_trans with (state ⟨m, a⟩ f).
                     +++ apply rt_step. apply (visit_unit_step m f x i [a] a).
                         *** apply Hinv.
                         *** assumption.
                         *** apply unit_in_single.
                         *** assumption.
                     +++ assumption.
                 --- split.
                     +++ apply (same_rest_trans _ (assign x a (input i))).
                         *** apply same_rest_assign.
                         *** assumption.
                     +++ split.
                         *** apply incl_trans with (vals (assign x a (input i))).
                             ---- apply incl_set_value.
                                  ++++ apply incl_refl.
                                  ++++ assumption.
                             ---- assumption.
                         *** repeat (split; try assumption). intros Hr j ls [<-|Hj] Hj'.
                             ---- apply (reordered_not_empty (cmap (assign x a (input i)))
                                    (cmap x') i [a] ls).
                                  ++++ apply Hrest.
                                  ++++ assumption.
                                  ++++ assumption.
                                  ++++ discriminate.
                             ---- now apply (Hnone Hr j).
    (* Not a clause *)
    + destruct (IH m f x x' r)
        as (m' & Hext & Hder & Hrest & Hincl & Hinv' & Hnone & Hsome).
      * assumption.
      * intros j ls Hj. apply Hshort. now right.
      * assumption.
      * exists m'. repeat (split; try assumption). intros Hr j ls [<-|Hj] Hj'.
        -- destruct (reordered_some_l (cmap x) (cmap x') i ls) as [ls0 [Hi0 _]].
           ++ apply Hrest.
           ++ assumption.
           ++ congruence.
        -- now apply (Hnone Hr j).
Qed.

(* A visit keeps the positions of the decisions and the lower literals. *)
Lemma visit_stacks: forall (p: Lit) (ws kept: list Watcher) (x: Ctx),
  SameStacks x (fst (visit p ws kept x)).
Proof.
  intros p ws. induction ws as [|[i b] ws IH]; intros kept x; simpl.
  - split; reflexivity.
  - destruct (lookup_true (vals x) b).
    + apply IH.
    + destruct (tget (cmap x) i) as [[|c0 [|c1 ls]]|].
      * apply IH.
      * destruct (c0 =? p).
        -- split; reflexivity.
        -- apply IH.
      * destruct ((c0 =? p) || (c1 =? p)).
        -- (* the clause is reordered first, then kept, moved or unit *)
           set (x1 := set_clause x i ((if c0 =? p then c1 else c0) :: p :: ls)).
           assert (H1: SameStacks x x1) by (split; reflexivity).
           destruct (lookup_true _ (if c0 =? p then c1 else c0)).
           ++ destruct (IH ((i, if c0 =? p then c1 else c0) :: kept) x1) as [Hl Hlow].
              destruct H1 as [Hl1 Hlow1]. split; congruence.
           ++ destruct (swap_watch _ p ls) as [[r' ls']|].
              ** destruct (IH kept (move_watch x1 i ((if c0 =? p then c1 else c0) :: r'
                             :: ls') r' (if c0 =? p then c1 else c0))) as [Hl Hlow].
                 destruct H1 as [Hl1 Hlow1]. split.
                 --- rewrite Hl. apply Hl1.
                 --- rewrite Hlow. apply Hlow1.
              ** destruct (lookup_undef _ (if c0 =? p then c1 else c0)).
                 --- destruct (IH ((i, if c0 =? p then c1 else c0) :: kept)
                                (assign x1 (if c0 =? p then c1 else c0) (input i)))
                       as [Hl Hlow].
                     destruct H1 as [Hl1 Hlow1]. split.
                     +++ rewrite Hl. apply Hl1.
                     +++ rewrite Hlow. apply Hlow1.
                 --- split; reflexivity.
        -- apply IH.
      * apply IH.
Qed.

(* Propagation keeps the positions of the decisions and the lower literals. *)
Lemma propagate_stacks: forall (fuel: nat) (x: Ctx),
  SameStacks x (fst (propagate fuel x)).
Proof.
  intros fuel. induction fuel as [|fuel IH]; intros x; simpl.
  - split; reflexivity.
  - destruct (qhead x <? tlen x).
    + pose proof (visit_stacks (¬(tget (tr x) (qhead x)))
                    (watching (wls x) (¬(tget (tr x) (qhead x)))) [] x) as [Hl Hlow].
      destruct (visit _ _ [] x) as [x1 [i|]]; cbn [fst] in Hl, Hlow.
      * split; assumption.
      * destruct (IH (advance x1)) as [Hl' Hlow']. split.
        -- rewrite Hl'. apply Hl.
        -- rewrite Hlow'. apply Hlow.
    + split; reflexivity.
Qed.

(* The check of the short clauses keeps the positions of the decisions and the lower
   literals. *)
Lemma check_shorts_stacks: forall (ss: list nat) (x: Ctx),
  SameStacks x (fst (check_shorts ss x)).
Proof.
  intros ss. induction ss as [|i ss IH]; intros x; simpl.
  - split; reflexivity.
  - destruct (tget (cmap x) i) as [[|a ls]|].
    + split; reflexivity.
    + destruct (lookup (vals x) a) as [[|]|].
      * apply IH.
      * split; reflexivity.
      * (* assigning keeps them *)
        destruct (IH (assign x a (input i))) as [Hl Hlow]. split.
        -- rewrite Hl. reflexivity.
        -- rewrite Hlow. reflexivity.
    + apply IH.
Qed.

(* A visit keeps the queue, and only extends the trail. *)
Lemma visit_qhead: forall (p: Lit) (ws kept: list Watcher) (x x': Ctx) (r: option nat),
  visit p ws kept x = (x', r) -> qhead x' = qhead x /\ (tlen x <= tlen x')%nat.
Proof.
  intros p ws. induction ws as [|[i b] ws IH]; intros kept x x' r Hv; simpl in Hv.
  - injection Hv as <- <-. cbn [set_watching qhead tlen]. split.
    + reflexivity.
    + lia.
  - destruct (lookup_true (vals x) b).
    + now apply IH in Hv.
    + destruct (tget (cmap x) i) as [[|c0 [|c1 ls]]|].
      * now apply IH in Hv.
      * destruct (c0 =? p).
        -- injection Hv as <- <-. cbn [set_watching qhead tlen]. split.
           ++ reflexivity.
           ++ lia.
        -- now apply IH in Hv.
      * destruct ((c0 =? p) || (c1 =? p)).
        -- destruct (lookup_true _ (if c0 =? p then c1 else c0)).
           ++ apply IH in Hv as [Hq Ht]. cbn [set_clause qhead tlen] in Hq, Ht. split.
              ** assumption.
              ** lia.
           ++ destruct (swap_watch _ p ls) as [[r' ls']|].
              ** apply IH in Hv as [Hq Ht].
                 cbn [move_watch set_clause qhead tlen] in Hq, Ht.
                 split.
                 --- assumption.
                 --- lia.
              ** destruct (lookup_undef _ (if c0 =? p then c1 else c0)).
                 --- apply IH in Hv as [Hq Ht].
                     cbn [assign set_clause qhead tlen] in Hq, Ht.
                     split.
                     +++ assumption.
                     +++ lia.
                 --- injection Hv as <- <-. cbn [set_watching set_clause qhead tlen].
                     split.
                     +++ reflexivity.
                     +++ lia.
        -- now apply IH in Hv.
      * now apply IH in Hv.
Qed.
Arguments visit_qhead {p ws kept x x' r}.

(* Moving a watch is setting the clause, then appending to the watch list of the new
   watch. *)
Lemma move_watch_split: forall (x: Ctx) (i: nat) (ls: list Lit) (l b: Lit),
  move_watch x i ls l b =
    set_watching (set_clause x i ls) l (watching (wls (set_clause x i ls)) l ++ [(i, b)]).
Proof. reflexivity. Qed.

(* If all literals of ls are false (by position, as the C proof sees them), swap_watch
   finds nothing. *)
Lemma swap_watch_all_false: forall (v: Values) (p: Lit) (ls: list Lit),
  (forall (d: nat), (d < length ls)%nat ->
    lookup v (nth d ls (Pos 0%nat)) = Some false) ->
  swap_watch v p ls = None.
Proof.
  intros v p ls. induction ls as [|y ls IH]; intros Hall; simpl.
  - reflexivity.
  - assert (Hy: lookup v y = Some false) by (apply (Hall 0%nat); simpl; lia).
    unfold not_false. rewrite Hy, IH.
    + reflexivity.
    + intros d Hd. apply (Hall (S d)). simpl. lia.
Qed.
