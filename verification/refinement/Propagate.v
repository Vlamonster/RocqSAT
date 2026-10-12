From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Relations.
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
From RocqSAT.refinement Require Import Analysis.

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

(* The watches w1 and w2 are fine up to the queue Q: a false watch has its negation queued, or the other watch is
   true. *)
Definition WatchQ (v: Values) (Q: Lit -> Prop) (w1 w2: Lit): Prop :=
  (lookup v w1 = Some false -> Q (¬w1) \/ lookup v w2 = Some true) /\
  (lookup v w2 = Some false -> Q (¬w2) \/ lookup v w1 = Some true).

(* The watches of every clause are literals of it, and equal only if the clause has no other literal. *)
Definition Shaped (cm: ClauseMap) (w: Watches): Prop :=
  forall (i: nat) (ls: list Lit) (w1 w2: Lit), tget cm i = Some ls -> tget w i = (w1, w2) ->
  ((ls = [] /\ w1 = w2) \/ (In w1 ls /\ In w2 ls)) /\ (w1 = w2 -> forall (y: Lit), In y ls -> y = w1).

(* Every clause is in the watch lists of both its watches. *)
Definition Listed (cm: ClauseMap) (w: Watches) (wl: WatchLists): Prop :=
  forall (i: nat) (ls: list Lit) (w1 w2: Lit), tget cm i = Some ls -> tget w i = (w1, w2) ->
  In i (watching wl w1) /\ In i (watching wl w2).

(* The watches of every clause are fine up to the queue Q. *)
Definition AllWatchQ (v: Values) (Q: Lit -> Prop) (cm: ClauseMap) (w: Watches): Prop :=
  forall (i: nat) (ls: list Lit) (w1 w2: Lit), tget cm i = Some ls -> tget w i = (w1, w2) -> WatchQ v Q w1 w2.

(* The context of the solver. *)
Record Ctx: Type := mkCtx {
  vals: Values;      (* the values of the trail *)
  cmap: ClauseMap;   (* the clauses of the formula with their literals, by index *)
  wat: Watches;      (* the two watched literals of each clause *)
  wls: WatchLists;   (* for each literal, the clauses that watch it *)
  tr: Table Lit;     (* the trail, oldest first *)
  tlen: nat;         (* the length of the trail *)
  qhead: nat;        (* the watchers of the negations of the trail literals from qhead on are still to be visited *)
  shorts: list nat;  (* the clauses with fewer than two literals, still to be checked *)
  alls: Table Lit;   (* the literals to decide on, in order *)
  nlits: nat;        (* the number of literals to decide on *)
  cur: nat;          (* the literals to decide on before cur are assigned *)
  saved: list nat;   (* the cursor before each decision, newest first *)
  rsn: Table nat;    (* hint: S i if clause i propagated the atom, 0 if nothing did *)
  lvl: Table nat;    (* hint: the decision level at which the atom was assigned *)
  dl: nat;           (* hint: the current decision level *)
  mrk: Table bool;   (* marks of literals by lit_key, used by the analysis and cleared after it *)
  phs: Values;       (* hint: the value each atom last had, used to decide *)
  nvars: nat         (* a bound on the length of the trail, which bounds the propagation loop *)
}.

(* Assign l with reason r at the current level, appending it to the trail. *)
Definition assign (x: Ctx) (l: Lit) (r: nat): Ctx :=
mkCtx (set_value (vals x) l) (cmap x) (wat x) (wls x) (tset (tr x) (tlen x) l) (S (tlen x)) (qhead x) (shorts x)
  (alls x) (nlits x) (cur x) (saved x) (tset (rsn x) (extract l) r) (tset (lvl x) (extract l) (dl x)) (dl x) (mrk x)
  (set_value (phs x) l) (nvars x).

(* Clause i now watches w, and is appended to the watch list of x. *)
Definition move_watch (x: Ctx) (i: nat) (w: Lit * Lit) (l: Lit): Ctx :=
mkCtx (vals x) (cmap x) (tset (wat x) i w) (tset (wls x) (lit_key l) (watching (wls x) l ++ [i])) (tr x) (tlen x)
  (qhead x) (shorts x) (alls x) (nlits x) (cur x) (saved x) (rsn x) (lvl x) (dl x) (mrk x) (phs x) (nvars x).

(* The watch list of l becomes ws. *)
Definition set_watching (x: Ctx) (l: Lit) (ws: list nat): Ctx :=
mkCtx (vals x) (cmap x) (wat x) (tset (wls x) (lit_key l) ws) (tr x) (tlen x) (qhead x) (shorts x) (alls x) (nlits x)
  (cur x) (saved x) (rsn x) (lvl x) (dl x) (mrk x) (phs x) (nvars x).

(* The queue moves past one literal. *)
Definition advance (x: Ctx): Ctx :=
mkCtx (vals x) (cmap x) (wat x) (wls x) (tr x) (tlen x) (S (qhead x)) (shorts x) (alls x) (nlits x) (cur x) (saved x)
  (rsn x) (lvl x) (dl x) (mrk x) (phs x) (nvars x).

(* Visit the clauses ws watching the false literal p, keeping kept (newest first) in the watch list of p: keep a
   clause whose other watch o is true; otherwise move the watch from p to a literal that is neither false nor o;
   otherwise all its literals but o are false, so propagate o if it is unassigned, and stop at the conflict
   clause if o is false. Clauses that no longer watch p are dropped. *)
Fixpoint visit (p: Lit) (ws kept: list nat) (m: PA) (x: Ctx): PA * Ctx * option nat :=
match ws with
| []        => (m, set_watching x p (rev kept), None)
| i :: rest =>
  match tget (wat x) i with
  | (w1, w2) =>
    if (w1 =? p) || (w2 =? p) then
      let o := if w1 =? p then w2 else w1 in
      if lookup_true (vals x) o then visit p rest (i :: kept) m x else
      match tget (cmap x) i with
      | Some ls =>
        match find (fun (r: Lit) => not_false (vals x) r && negb (r =? o)) ls with
        | Some r => visit p rest kept m (move_watch x i (if w1 =? p then (r, w2) else (w1, r)) r)
        | None   =>
          if lookup_undef (vals x) o then visit p rest (i :: kept) ⟨m, o⟩ (assign x o (S i))
          else (m, set_watching x p (rev_append kept ws), Some i)
        end
      | None    => visit p rest kept m x
      end
    else visit p rest kept m x
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
    | None       => check_shorts ss' ⟨m, a⟩ (assign x a (S i))
    end
  | Some []       => (m, x, Some i)
  | None          => check_shorts ss' m x
  end
end.

(* What propagation keeps: the context agrees with the trail m, and its clauses are clauses of f. *)
Record Core (m: PA) (f: CNF) (x: Ctx): Prop := {
  core_vals: ValuesOf (vals x) m;
  core_fresh: Fresh m;
  core_trail: TrailOf (tr x) (tlen x) m;
  core_sound: forall (i: nat) (ls: list Lit), tget (cmap x) i = Some ls -> ClauseOf f ls;
  core_shaped: Shaped (cmap x) (wat x)
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
End Trail.

(* At every decision of m, the watches are fine up to an empty queue with respect to the values before it, so a
   backjump can keep them. *)
Fixpoint SavedQ (cm: ClauseMap) (w: Watches) (m: PA): Prop :=
match m with
| ⟨⟩     => True
| ⟨m, _⟩ => SavedQ cm w m
| ⟨m; _⟩ => AllWatchQ (values m) (fun (_: Lit) => False) cm w /\ SavedQ cm w m
end.

(* The parts of the context that propagation does not change. *)
Definition SameRest (x x': Ctx): Prop :=
  cmap x' = cmap x /\ qhead x' = qhead x /\ shorts x' = shorts x /\ alls x' = alls x /\ nlits x' = nlits x /\
  cur x' = cur x /\ saved x' = saved x /\ dl x' = dl x /\ mrk x' = mrk x /\ nvars x' = nvars x.

Lemma same_rest_refl: forall (x: Ctx), SameRest x x.
Proof. intros x. now repeat split. Qed.

Lemma same_rest_trans: forall (x1 x2 x3: Ctx), SameRest x1 x2 -> SameRest x2 x3 -> SameRest x1 x3.
Proof.
  intros x1 x2 x3 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
  repeat split; congruence.
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
  (* Moving the watch p of clause i, false with respect to the values v of m, to r, which is not false, keeps the
     watches fine at every decision of m. *)
  Lemma saved_q_move: forall (cm: ClauseMap) (w: Watches) (m: PA) (v: Values) (i: nat) (p r w1 w2: Lit)
    (w': Lit * Lit),
    SavedQ cm w m ->
    Incl (values m) v ->
    Fresh m ->
    lookup v p = Some false ->
    lookup v r <> Some false ->
    tget w i = (w1, w2) ->
    (w1 = p /\ w' = (r, w2)) \/ (w2 = p /\ w' = (w1, r)) ->
    SavedQ cm (tset w i w') m.
  Proof.
    intros cm w m. induction m as [|m IH l|m IH l]; intros v i p r w1 w2 w' Hsaved Hincl Hfresh Hp Hr Hw Hw'; simpl in *.
    - easy.
    - destruct Hfresh as [Hfresh Hl]. apply (IH v i p r w1 w2).
      + assumption.
      + apply incl_trans with (set_value (values m) l).
        * now apply incl_values_cons.
        * assumption.
      + assumption.
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
        * intros j ls a b Hj Hwj. rewrite tget_tset in Hwj. destruct (Nat.eq_dec i j) as [<-|Hneq].
          -- destruct (Hall i ls w1 w2 Hj Hw) as [H1 H2].
             assert (Hr': lookup (values m) r <> Some false).
             ++ intros Hr'. now apply Hincl' in Hr'.
             ++ assert (Hp': lookup (values m) p <> Some true).
                ** intros Hp'. apply Hincl' in Hp'. congruence.
                ** destruct Hw' as [[-> ->]|[-> ->]]; injection Hwj as <- <-; split.
                   --- intros Hra. contradiction.
                   --- intros Hb. destruct (H2 Hb) as [[]|Hpt]. contradiction.
                   --- intros Ha. destruct (H1 Ha) as [[]|Hpt]. contradiction.
                   --- intros Hrb. contradiction.
          -- now apply (Hall j ls).
        * now apply (IH v i p r w1 w2).
  Qed.
End Saved.

(* Clause i watching z is in the watch list of z, or, if z is p, in kept or ws. *)
Definition WatchedV (wl: WatchLists) (p: Lit) (kept ws: list nat) (i: nat) (z: Lit): Prop :=
  (z <> p -> In i (watching wl z)) /\ (z = p -> In i kept \/ In i ws).

(* During the visit of the watchers of the false literal p, the first queued literal: the clauses watching p are
   in kept or ws instead of the watch list of p, and those in kept have a true other watch. *)
Record VisitInv (p: Lit) (kept ws: list nat) (m: PA) (f: CNF) (x: Ctx): Prop := {
  vi_core: Core m f x;
  vi_qhead: qhead x < tlen x;
  vi_head: tget (tr x) (qhead x) = ¬p;
  vi_watch: AllWatchQ (vals x) (Queued (tr x) (qhead x) (tlen x)) (cmap x) (wat x);
  vi_saved: SavedQ (cmap x) (wat x) m;
  vi_listed: forall (i: nat) (ls: list Lit) (w1 w2: Lit), tget (cmap x) i = Some ls -> tget (wat x) i = (w1, w2) ->
    WatchedV (wls x) p kept ws i w1 /\ WatchedV (wls x) p kept ws i w2;
  vi_kept: forall (i: nat) (ls: list Lit) (w1 w2: Lit), In i kept -> tget (cmap x) i = Some ls ->
    tget (wat x) i = (w1, w2) -> (w1 = p -> lookup (vals x) w2 = Some true) /\ (w2 = p -> lookup (vals x) w1 = Some true)
}.

(* The visited literal p is false. *)
Lemma visit_p_false: forall (p: Lit) (kept ws: list nat) (m: PA) (f: CNF) (x: Ctx),
  VisitInv p kept ws m f x -> lookup (vals x) p = Some false.
Proof.
  intros p kept ws m f x [[Hvals Hfresh Htrail _ _] Hq Hhead _ _ _ _]. apply (values_neg_in_false _ m).
  - assumption.
  - assumption.
  - rewrite <- Hhead. now apply (trail_of_in _ (tlen x)).
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
  Lemma watch_q_assign: forall (v: Values) (Q Q': Lit -> Prop) (l w1 w2: Lit),
    WatchQ v Q w1 w2 -> lookup v l = None -> (forall (y: Lit), Q y -> Q' y) -> Q' l ->
    WatchQ (set_value v l) Q' w1 w2.
  Proof.
    intros v Q Q' l w1 w2 [H1 H2] Hl HQ Hl'. split.
    - intros Hw1. apply lookup_set_false in Hw1 as [->|Hw1].
      + left. now rewrite Neg.involutive.
      + destruct (H1 Hw1) as [Hq|Hw2].
        * left. now apply HQ.
        * right. now apply lookup_set_defined.
      + assumption.
    - intros Hw2. apply lookup_set_false in Hw2 as [->|Hw2].
      + left. now rewrite Neg.involutive.
      + destruct (H2 Hw2) as [Hq|Hw1].
        * left. now apply HQ.
        * right. now apply lookup_set_defined.
      + assumption.
  Qed.

  (* A clause that does not watch p is dropped. *)
  Lemma visit_inv_drop: forall (p: Lit) (i: nat) (rest kept: list nat) (m: PA) (f: CNF) (x: Ctx),
    VisitInv p kept (i :: rest) m f x ->
    (forall (ls: list Lit) (w1 w2: Lit), tget (cmap x) i = Some ls -> tget (wat x) i = (w1, w2) -> w1 <> p /\ w2 <> p) ->
    VisitInv p kept rest m f x.
  Proof.
    intros p i rest kept m f x [Hcore Hq Hhead Hwatch Hsaved Hlisted Hkept] Hnot.
    split; try assumption.
    intros j ls w1 w2 Hj Hw. destruct (Hlisted j ls w1 w2 Hj Hw) as [[Hz1 Hp1] [Hz2 Hp2]]. split.
    - split.
      + assumption.
      + intros ->. destruct (Hp1 eq_refl) as [Hin|[<-|Hin]].
        * now left.
        * now destruct (Hnot ls p w2 Hj Hw).
        * now right.
    - split.
      + assumption.
      + intros ->. destruct (Hp2 eq_refl) as [Hin|[<-|Hin]].
        * now left.
        * now destruct (Hnot ls w1 p Hj Hw).
        * now right.
  Qed.

  (* A clause whose other watch is true is kept. *)
  Lemma visit_inv_keep: forall (p: Lit) (i: nat) (rest kept: list nat) (m: PA) (f: CNF) (x: Ctx),
    VisitInv p kept (i :: rest) m f x ->
    (forall (ls: list Lit) (w1 w2: Lit), tget (cmap x) i = Some ls -> tget (wat x) i = (w1, w2) ->
      (w1 = p -> lookup (vals x) w2 = Some true) /\ (w2 = p -> lookup (vals x) w1 = Some true)) ->
    VisitInv p (i :: kept) rest m f x.
  Proof.
    intros p i rest kept m f x [Hcore Hq Hhead Hwatch Hsaved Hlisted Hkept] Hother.
    split; try assumption.
    - intros j ls w1 w2 Hj Hw. destruct (Hlisted j ls w1 w2 Hj Hw) as [[Hz1 Hp1] [Hz2 Hp2]]. split.
      + split.
        * assumption.
        * intros ->. destruct (Hp1 eq_refl) as [Hin|[<-|Hin]].
          -- left. now right.
          -- left. now left.
          -- now right.
      + split.
        * assumption.
        * intros ->. destruct (Hp2 eq_refl) as [Hin|[<-|Hin]].
          -- left. now right.
          -- left. now left.
          -- now right.
    - intros j ls w1 w2 [<-|Hin] Hj Hw.
      + now apply (Hother ls).
      + now apply (Hkept j ls).
  Qed.

  (* Moving the watch p of clause i to a literal r of it that is neither false nor the other watch o. *)
  Lemma visit_inv_move: forall (p: Lit) (i: nat) (rest kept: list nat) (m: PA) (f: CNF) (x: Ctx) (ls: list Lit)
    (w1 w2 o r: Lit) (w': Lit * Lit),
    VisitInv p kept (i :: rest) m f x ->
    tget (cmap x) i = Some ls ->
    tget (wat x) i = (w1, w2) ->
    (w1 = p /\ o = w2 /\ w' = (r, w2)) \/ (w1 <> p /\ w2 = p /\ o = w1 /\ w' = (w1, r)) ->
    In r ls ->
    lookup (vals x) r <> Some false ->
    r <> o ->
    VisitInv p kept rest m f (move_watch x i w' r).
  Proof.
    intros p i rest kept m f x ls w1 w2 o r w' Hinv Hi Hw Hcase Hr_in Hr Hro.
    pose proof (visit_p_false p kept (i :: rest) m f x Hinv) as Hp.
    destruct Hinv as [[Hvals Hfresh Htrail Hsound Hshaped] Hq Hhead Hwatch Hsaved Hlisted Hkept].
    assert (Hrp: r <> p).
    - intros ->. contradiction.
    - destruct (Hshaped i ls w1 w2 Hi Hw) as [Hmembers Hdistinct].
      assert (Hin: In w1 ls /\ In w2 ls).
      + destruct Hmembers as [[-> _]|Hin].
        * destruct Hr_in.
        * assumption.
      + assert (Hop: o <> p).
        * intros ->. destruct Hcase as [(-> & <- & _)|(Hneq & -> & -> & _)].
          -- apply Hrp, (Hdistinct eq_refl), Hr_in.
          -- contradiction.
        * (* The other watch is in its watch list, and its falsity is queued since p is false *)
          assert (Ho_listed: In i (watching (wls x) o)).
          -- destruct (Hlisted i ls w1 w2 Hi Hw) as [[Hz1 _] [Hz2 _]].
             destruct Hcase as [(_ & -> & _)|(_ & _ & -> & _)].
             ++ now apply Hz2.
             ++ now apply Hz1.
          -- assert (Ho_q: lookup (vals x) o = Some false -> Queued (tr x) (qhead x) (tlen x) (¬o)).
             ++ intros Ho. destruct (Hwatch i ls w1 w2 Hi Hw) as [H1 H2].
                destruct Hcase as [(-> & -> & _)|(_ & -> & -> & _)].
                ** destruct (H2 Ho) as [Hq'|Hpt].
                   --- assumption.
                   --- congruence.
                ** destruct (H1 Ho) as [Hq'|Hpt].
                   --- assumption.
                   --- congruence.
             ++ split.
                (* Core *)
                ** split; try assumption.
                   intros j ls' a b Hj Hwj. simpl in Hj, Hwj. rewrite tget_tset in Hwj.
                   destruct (Nat.eq_dec i j) as [<-|Hneq].
                   --- rewrite Hi in Hj. injection Hj as <-.
                       destruct Hcase as [(-> & -> & ->)|(_ & -> & -> & ->)]; injection Hwj as <- <-; split.
                       +++ right. now split.
                       +++ intros Heq. now apply Hro in Heq.
                       +++ right. now split.
                       +++ intros Heq. symmetry in Heq. now apply Hro in Heq.
                   --- now apply (Hshaped j).
                ** assumption.
                ** assumption.
                (* The watches are fine *)
                ** intros j ls' a b Hj Hwj. simpl in Hj, Hwj |- *. rewrite tget_tset in Hwj.
                   destruct (Nat.eq_dec i j) as [<-|Hneq].
                   --- destruct Hcase as [(-> & -> & ->)|(_ & -> & -> & ->)]; injection Hwj as <- <-; split.
                       +++ intros Hrf. contradiction.
                       +++ intros Ho. left. now apply Ho_q.
                       +++ intros Ho. left. now apply Ho_q.
                       +++ intros Hrf. contradiction.
                   --- now apply (Hwatch j ls').
                (* At the decisions too *)
                ** simpl. apply (saved_q_move _ _ m (vals x) i p r w1 w2).
                   --- assumption.
                   --- now apply values_of_incl.
                   --- assumption.
                   --- assumption.
                   --- assumption.
                   --- assumption.
                   --- destruct Hcase as [(-> & _ & ->)|(_ & -> & _ & ->)].
                       +++ now left.
                       +++ now right.
                (* The watch lists *)
                ** intros j ls' a b Hj Hwj. simpl in Hj, Hwj |- *. rewrite tget_tset in Hwj.
                   assert (Hgrow: forall (z: Lit) (k: nat), In k (watching (wls x) z) ->
                     In k (watching (tset (wls x) (lit_key r) (watching (wls x) r ++ [i])) z)).
                   --- intros z k Hk. rewrite watching_add. destruct (Lit.eq_dec r z) as [<-|_].
                       +++ apply in_or_app. now left.
                       +++ assumption.
                   --- destruct (Nat.eq_dec i j) as [<-|Hneq].
                       +++ assert (Hr_listed: In i (watching (tset (wls x) (lit_key r) (watching (wls x) r ++ [i])) r)).
                           *** rewrite watching_add. destruct (Lit.eq_dec r r) as [_|]; [|contradiction].
                               apply in_or_app. right. now left.
                           *** destruct Hcase as [(-> & -> & ->)|(_ & -> & -> & ->)]; injection Hwj as <- <-; split.
                               ---- split.
                                    ++++ now intros _.
                                    ++++ intros Heq. contradiction.
                               ---- split.
                                    ++++ intros _. now apply Hgrow.
                                    ++++ intros Heq. contradiction.
                               ---- split.
                                    ++++ intros _. now apply Hgrow.
                                    ++++ intros Heq. contradiction.
                               ---- split.
                                    ++++ now intros _.
                                    ++++ intros Heq. contradiction.
                       +++ destruct (Hlisted j ls' a b Hj Hwj) as [[Hz1 Hp1] [Hz2 Hp2]]. split.
                           *** split.
                               ---- intros Hne. now apply Hgrow, Hz1.
                               ---- intros ->. destruct (Hp1 eq_refl) as [Hk|[Heq|Hk]].
                                    ++++ now left.
                                    ++++ contradiction.
                                    ++++ now right.
                           *** split.
                               ---- intros Hne. now apply Hgrow, Hz2.
                               ---- intros ->. destruct (Hp2 eq_refl) as [Hk|[Heq|Hk]].
                                    ++++ now left.
                                    ++++ contradiction.
                                    ++++ now right.
                (* The kept clauses *)
                ** intros j ls' a b Hk Hj Hwj. simpl in Hj, Hwj |- *. rewrite tget_tset in Hwj.
                   destruct (Nat.eq_dec i j) as [<-|Hneq].
                   --- destruct Hcase as [(-> & -> & ->)|(_ & -> & -> & ->)]; injection Hwj as <- <-; split.
                       +++ intros Heq. contradiction.
                       +++ intros Heq. contradiction.
                       +++ intros Heq. contradiction.
                       +++ intros Heq. contradiction.
                   --- now apply (Hkept j ls').
  Qed.

  (* Assigning the unassigned other watch o of clause i, all of whose other literals are false, keeps it. *)
  Lemma visit_inv_unit: forall (p: Lit) (i: nat) (rest kept: list nat) (m: PA) (f: CNF) (x: Ctx) (ls: list Lit)
    (w1 w2 o: Lit),
    VisitInv p kept (i :: rest) m f x ->
    tget (cmap x) i = Some ls ->
    tget (wat x) i = (w1, w2) ->
    (w1 = p /\ o = w2) \/ (w1 <> p /\ w2 = p /\ o = w1) ->
    lookup (vals x) o = None ->
    VisitInv p (i :: kept) rest ⟨m, o⟩ f (assign x o (S i)).
  Proof.
    intros p i rest kept m f x ls w1 w2 o Hinv Hi Hw Hcase Ho.
    pose proof (visit_p_false p kept (i :: rest) m f x Hinv) as Hp.
    destruct Hinv as [[Hvals Hfresh Htrail Hsound Hshaped] Hq Hhead Hwatch Hsaved Hlisted Hkept].
    assert (Hop: o <> p).
    - intros ->. congruence.
    - split.
      + split.
        * intros y. simpl. now rewrite lookup_add, Hvals.
        * split.
          -- assumption.
          -- now rewrite <- Hvals.
        * now apply trail_of_cons.
        * assumption.
        * assumption.
      + simpl. lia.
      + simpl. rewrite tget_tset_other.
        * assumption.
        * lia.
      + intros j ls' a b Hj Hwj. simpl in Hj, Hwj |- *. apply (watch_q_assign (vals x) (Queued (tr x) (qhead x) (tlen x))).
        * now apply (Hwatch j ls').
        * assumption.
        * intros y. apply queued_cons.
        * apply queued_new. lia.
      + assumption.
      + intros j ls' a b Hj Hwj. simpl in Hj, Hwj. destruct (Hlisted j ls' a b Hj Hwj) as [[Hz1 Hp1] [Hz2 Hp2]]. split.
        * split.
          -- assumption.
          -- intros ->. destruct (Hp1 eq_refl) as [Hk|[<-|Hk]].
             ++ left. now right.
             ++ left. now left.
             ++ now right.
        * split.
          -- assumption.
          -- intros ->. destruct (Hp2 eq_refl) as [Hk|[<-|Hk]].
             ++ left. now right.
             ++ left. now left.
             ++ now right.
      + intros j ls' a b [<-|Hk] Hj Hwj; simpl in Hj, Hwj |- *.
        * rewrite Hw in Hwj. injection Hwj as <- <-.
          destruct Hcase as [(-> & ->)|(Hneq & -> & ->)]; split.
          -- intros _. apply lookup_add_self.
          -- intros Heq. contradiction.
          -- intros Heq. contradiction.
          -- intros _. apply lookup_add_self.
        * destruct (Hkept j ls' a b Hk Hj Hwj) as [H1 H2]. split.
          -- intros Ha. apply lookup_set_defined.
             ++ now apply H1.
             ++ assumption.
          -- intros Hb. apply lookup_set_defined.
             ++ now apply H2.
             ++ assumption.
  Qed.

  (* That assignment is a Unit step. *)
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
End VisitSteps.

Lemma core_ext: forall (m: PA) (f: CNF) (x x': Ctx),
  Core m f x -> vals x' = vals x -> tr x' = tr x -> tlen x' = tlen x -> cmap x' = cmap x -> wat x' = wat x ->
  Core m f x'.
Proof.
  intros m f x x' [Hvals Hfresh Htrail Hsound Hshaped] Hv Htr Hlen Hcm Hw. split.
  - now rewrite Hv.
  - assumption.
  - now rewrite Htr, Hlen.
  - now rewrite Hcm.
  - now rewrite Hcm, Hw.
Qed.

(* The result of a visit: the transitions taken are Unit steps, the watch lists are complete again, and either the
   clauses watching p have a true other watch, or clause i is false. *)
Lemma visit_spec: forall (p: Lit) (ws kept: list nat) (m m': PA) (f: CNF) (x x': Ctx) (r: option nat),
  VisitInv p kept ws m f x ->
  visit p ws kept m x = (m', x', r) ->
  state m f ==>*[DPLL_BJ] state m' f /\ SameRest x x' /\ Incl (vals x) (vals x') /\
  Core m' f x' /\ qhead x' < tlen x' /\ tget (tr x') (qhead x') = ¬p /\
  AllWatchQ (vals x') (Queued (tr x') (qhead x') (tlen x')) (cmap x') (wat x') /\
  SavedQ (cmap x') (wat x') m' /\ Listed (cmap x') (wat x') (wls x') /\
  (r = None -> forall (i: nat) (ls: list Lit) (w1 w2: Lit), tget (cmap x') i = Some ls -> tget (wat x') i = (w1, w2) ->
    (w1 = p -> lookup (vals x') w2 = Some true) /\ (w2 = p -> lookup (vals x') w1 = Some true)) /\
  (forall (i: nat), r = Some i ->
    exists (ls: list Lit), tget (cmap x') i = Some ls /\ forall (y: Lit), In y ls -> lookup (vals x') y = Some false).
Proof.
  intros p ws. induction ws as [|i rest IH]; intros kept m m' f x x' r Hinv Hvisit; simpl in Hvisit.
  (* All visited: the kept clauses go back into the watch list of p *)
  - injection Hvisit as <- <- <-. destruct Hinv as [Hcore Hq Hhead Hwatch Hsaved Hlisted Hkept].
    split.
    + apply rt_refl.
    + split.
      * now repeat split.
      * split.
        -- apply incl_refl.
        -- split.
           ++ now apply (core_ext m f x).
           ++ split.
              ** assumption.
              ** split.
                 --- assumption.
                 --- split.
                     +++ assumption.
                     +++ split.
                         *** assumption.
                         *** split.
                             ---- intros j ls a b Hj Hwj. simpl in Hj, Hwj |- *.
                                  destruct (Hlisted j ls a b Hj Hwj) as [[Hz1 Hp1] [Hz2 Hp2]].
                                  rewrite !watching_add. split.
                                  ++++ destruct (Lit.eq_dec p a) as [<-|Hneq].
                                       **** destruct (Hp1 eq_refl) as [Hk|[]]. now apply in_rev in Hk.
                                       **** apply Hz1. intros Heq. now apply Hneq.
                                  ++++ destruct (Lit.eq_dec p b) as [<-|Hneq].
                                       **** destruct (Hp2 eq_refl) as [Hk|[]]. now apply in_rev in Hk.
                                       **** apply Hz2. intros Heq. now apply Hneq.
                             ---- split.
                                  ++++ intros _ j ls a b Hj Hwj. simpl in Hj, Hwj |- *.
                                       destruct (Hlisted j ls a b Hj Hwj) as [[_ Hp1] [_ Hp2]]. split.
                                       **** intros ->. destruct (Hp1 eq_refl) as [Hk|[]]. now apply (Hkept j ls p b).
                                       **** intros ->. destruct (Hp2 eq_refl) as [Hk|[]]. now apply (Hkept j ls a p).
                                  ++++ intros j Heq. discriminate.
  - destruct (tget (wat x) i) as [w1 w2] eqn:Hw. destruct ((w1 =? p) || (w2 =? p)) eqn:Hwp.
    + pose proof (visit_p_false p kept (i :: rest) m f x Hinv) as Hp.
      set (o := if w1 =? p then w2 else w1) in Hvisit.
      assert (Hcase: (w1 = p /\ o = w2) \/ (w1 <> p /\ w2 = p /\ o = w1)).
      * subst o. destruct (w1 =? p) eqn:Hw1p.
        -- left. split.
           ++ now apply Lit.eqb_eq.
           ++ reflexivity.
        -- right. simpl in Hwp. split.
           ++ now apply Lit.eqb_neq.
           ++ split.
              ** now apply Lit.eqb_eq.
              ** reflexivity.
      * assert (Ho_in: forall (ls: list Lit), tget (cmap x) i = Some ls -> ls <> [] -> In o ls).
        -- intros ls Hi Hne. destruct Hinv as [[_ _ _ _ Hshaped] _ _ _ _ _ _].
           destruct (Hshaped i ls w1 w2 Hi Hw) as [[[-> _]|[Hin1 Hin2]] _].
           ++ contradiction.
           ++ destruct Hcase as [(_ & ->)|(_ & _ & ->)].
              ** assumption.
              ** assumption.
        -- destruct (lookup_true (vals x) o) eqn:Ho.
           (* The other watch is true: keep the clause *)
           ++ apply (IH (i :: kept) m m' f x x' r).
              ** apply visit_inv_keep.
                 --- assumption.
                 --- intros ls a b Hi Hwi. rewrite Hw in Hwi. injection Hwi as <- <-.
                     unfold lookup_true in Ho. destruct (lookup (vals x) o) as [[|]|] eqn:Ho'; try discriminate.
                     destruct Hcase as [(-> & ->)|(Hneq & -> & ->)]; split.
                     +++ now intros _.
                     +++ intros ->. assumption.
                     +++ intros Heq. contradiction.
                     +++ now intros _.
              ** assumption.
           ++ destruct (tget (cmap x) i) as [ls|] eqn:Hi.
              ** destruct (find (fun (r: Lit) => not_false (vals x) r && negb (r =? o)) ls) as [r'|] eqn:Hfind.
                 (* Move the watch from p to r' *)
                 --- apply find_some in Hfind as [Hr_in Hr]. apply andb_prop in Hr as [Hr_nf Hr_o].
                     assert (Hr_nf': lookup (vals x) r' <> Some false).
                     +++ unfold not_false in Hr_nf. destruct (lookup (vals x) r') as [[|]|]; easy.
                     +++ assert (Hro: r' <> o).
                         *** apply negb_true_iff, Lit.eqb_neq in Hr_o. assumption.
                         *** set (w' := if w1 =? p then (r', w2) else (w1, r')) in Hvisit.
                             assert (Hcase': (w1 = p /\ o = w2 /\ w' = (r', w2)) \/ (w1 <> p /\ w2 = p /\ o = w1 /\ w' = (w1, r'))).
                             ---- subst w'. destruct Hcase as [(Heq & Ho2)|(Hneq & Heq & Ho1)].
                                  ++++ left. rewrite Heq, Lit.eqb_refl. now repeat split.
                                  ++++ right. apply Lit.eqb_neq in Hneq as Hneq'. rewrite Hneq'. now repeat split.
                             ---- destruct (IH kept m m' f (move_watch x i w' r') x' r) as (Hder & Hrest & Hincl & Hres).
                                  ++++ now apply (visit_inv_move p i rest kept m f x ls w1 w2 o r' w').
                                  ++++ assumption.
                                  ++++ split.
                                       **** assumption.
                                       **** split.
                                            ----- apply (same_rest_trans _ (move_watch x i w' r')).
                                                  +++++ now repeat split.
                                                  +++++ assumption.
                                            ----- now split.
                 --- destruct (lookup_undef (vals x) o) eqn:Hu.
                     (* Unit: propagate o *)
                     +++ assert (Hu': lookup (vals x) o = None).
                         *** unfold lookup_undef in Hu. destruct (lookup (vals x) o); easy.
                         *** assert (Hfalse: forall (y: Lit), In y ls -> y <> o -> lookup (vals x) y = Some false).
                             ---- intros y Hy Hyo. apply find_none with (x := y) in Hfind.
                                  ++++ apply andb_false_iff in Hfind as [Hnf|Heq].
                                       **** unfold not_false in Hnf. destruct (lookup (vals x) y) as [[|]|]; easy.
                                       **** apply negb_false_iff, Lit.eqb_eq in Heq. contradiction.
                                  ++++ assumption.
                             ---- assert (Hne: ls <> []).
                                  ++++ intros ->. destruct Hinv as [[_ _ _ _ Hshaped] _ _ _ _ _ _].
                                       destruct (Hshaped i [] w1 w2 Hi Hw) as [[[_ Heq]|[[] _]] _].
                                       destruct Hcase as [(-> & ->)|(_ & -> & ->)].
                                       **** rewrite <- Heq in Hu'. congruence.
                                       **** rewrite Heq in Hu'. congruence.
                                  ++++ destruct (IH (i :: kept) ⟨m, o⟩ m' f (assign x o (S i)) x' r) as (Hder & Hrest & Hincl & Hres).
                                       **** now apply (visit_inv_unit p i rest kept m f x ls w1 w2 o).
                                       **** assumption.
                                       **** split.
                                            ----- apply rt_trans with (state ⟨m, o⟩ f).
                                                  +++++ apply rt_step. apply (visit_unit_step m f x i ls o).
                                                        ***** apply Hinv.
                                                        ***** assumption.
                                                        ***** now apply Ho_in.
                                                        ***** assumption.
                                                        ***** assumption.
                                                  +++++ assumption.
                                            ----- split.
                                                  +++++ apply (same_rest_trans _ (assign x o (S i))).
                                                        ***** now repeat split.
                                                        ***** assumption.
                                                  +++++ split.
                                                        ***** apply incl_trans with (vals (assign x o (S i))).
                                                              ------ apply incl_set_value.
                                                                     ++++++ apply incl_refl.
                                                                     ++++++ assumption.
                                                              ------ assumption.
                                                        ***** assumption.
                     (* Conflict: o is false too *)
                     +++ injection Hvisit as <- <- <-. destruct Hinv as [Hcore Hq Hhead Hwatch Hsaved Hlisted Hkept].
                         split.
                         *** apply rt_refl.
                         *** split.
                             ---- now repeat split.
                             ---- split.
                                  ++++ apply incl_refl.
                                  ++++ split.
                                       **** now apply (core_ext m f x).
                                       **** split.
                                            ----- assumption.
                                            ----- split.
                                                  +++++ assumption.
                                                  +++++ split.
                                                        ***** assumption.
                                                        ***** split.
                                                              ------ assumption.
                                                              ------ split.
                                                                     ++++++ intros j ls' a b Hj Hwj. simpl in Hj, Hwj |- *.
                                                                            destruct (Hlisted j ls' a b Hj Hwj) as [[Hz1 Hp1] [Hz2 Hp2]].
                                                                            rewrite !watching_add, rev_append_rev. split.
                                                                            ****** destruct (Lit.eq_dec p a) as [<-|Hneq].
                                                                                   ------- apply in_or_app. destruct (Hp1 eq_refl) as [Hk|Hk].
                                                                                           ******* left. now apply in_rev in Hk.
                                                                                           ******* now right.
                                                                                   ------- apply Hz1. intros Heq. now apply Hneq.
                                                                            ****** destruct (Lit.eq_dec p b) as [<-|Hneq].
                                                                                   ------- apply in_or_app. destruct (Hp2 eq_refl) as [Hk|Hk].
                                                                                           ******* left. now apply in_rev in Hk.
                                                                                           ******* now right.
                                                                                   ------- apply Hz2. intros Heq. now apply Hneq.
                                                                     ++++++ split.
                                                                            ****** intros Heq. discriminate.
                                                                            ****** intros j Heq. injection Heq as <-. exists ls. split.
                                                                                   ------- assumption.
                                                                                   ------- intros y Hy. simpl. destruct (Lit.eq_dec y o) as [->|Hyo].
                                                                                           ******* unfold lookup_true in Ho. unfold lookup_undef in Hu.
                                                                                                   destruct (lookup (vals x) o) as [[|]|]; easy.
                                                                                           ******* apply find_none with (x := y) in Hfind.
                                                                                                   ++++++++ apply andb_false_iff in Hfind as [Hnf|Heq].
                                                                                                            -------- unfold not_false in Hnf. destruct (lookup (vals x) y) as [[|]|]; easy.
                                                                                                            -------- apply negb_false_iff, Lit.eqb_eq in Heq. contradiction.
                                                                                                   ++++++++ assumption.
              (* Not a clause *)
              ** apply (IH kept m m' f x x' r).
                 --- apply (visit_inv_drop p i).
                     +++ assumption.
                     +++ intros ls Hi'. congruence.
                 --- assumption.
    (* The clause no longer watches p *)
    + apply (IH kept m m' f x x' r).
      * apply (visit_inv_drop p i).
        -- assumption.
        -- intros ls a b _ Hwi. rewrite Hw in Hwi. injection Hwi as <- <-.
           apply orb_false_iff in Hwp as [H1 H2]. apply Lit.eqb_neq in H1, H2. now split.
      * assumption.
Qed.

(* Between visits: the watches are fine up to the queue from qhead on, and the watch lists are complete. *)
Record PropInv (m: PA) (f: CNF) (x: Ctx): Prop := {
  pi_core: Core m f x;
  pi_qhead: qhead x <= tlen x;
  pi_watch: AllWatchQ (vals x) (Queued (tr x) (qhead x) (tlen x)) (cmap x) (wat x);
  pi_saved: SavedQ (cmap x) (wat x) m;
  pi_listed: Listed (cmap x) (wat x) (wls x)
}.

(* The parts of the context that propagation does not change. *)
Definition SameFixed (x x': Ctx): Prop :=
  cmap x' = cmap x /\ shorts x' = shorts x /\ alls x' = alls x /\ nlits x' = nlits x /\ cur x' = cur x /\
  saved x' = saved x /\ dl x' = dl x /\ mrk x' = mrk x /\ nvars x' = nvars x.

Lemma same_fixed_trans: forall (x1 x2 x3: Ctx), SameFixed x1 x2 -> SameFixed x2 x3 -> SameFixed x1 x3.
Proof.
  intros x1 x2 x3 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
  repeat split; congruence.
Qed.

Lemma same_rest_fixed: forall (x x': Ctx), SameRest x x' -> SameFixed x x'.
Proof. intros x x' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10). now repeat split. Qed.

(* The trail of a context is at most nvars long. *)
Lemma trail_bound: forall (m: PA) (f: CNF) (x: Ctx),
  Core m f x -> WellFormed (state m f) -> S (max_atom_f f) <= nvars x -> tlen x <= nvars x.
Proof.
  intros m f x [_ _ [Hlen _] _ _] Hwf Hbound. rewrite Hlen, trail_lits_length. apply well_formed_length_le in Hwf.
  lia.
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
    + apply Nat.ltb_lt in Hlt. destruct Hinv as [Hcore Hq Hwatch Hsaved Hlisted].
      set (p := ¬(tget (tr x) (qhead x))) in Hprop.
      destruct (visit p (watching (wls x) p) [] m x) as [[m1 x1] r1] eqn:Hvisit.
      destruct (visit_spec p (watching (wls x) p) [] m m1 f x x1 r1) as
        (Hder & Hrest & Hincl & Hcore1 & Hq1 & Hhead1 & Hwatch1 & Hsaved1 & Hlisted1 & Hdone & Hconf).
      * split.
        -- assumption.
        -- assumption.
        -- subst p. now rewrite Neg.involutive.
        -- assumption.
        -- assumption.
        -- intros i ls w1 w2 Hi Hw. destruct (Hlisted i ls w1 w2 Hi Hw) as [H1 H2]. split.
           ++ split.
              ** now intros _.
              ** intros ->. now right.
           ++ split.
              ** now intros _.
              ** intros ->. now right.
        -- intros i ls w1 w2 [].
      * assumption.
      * destruct r1 as [i|].
        (* A conflict *)
        -- injection Hprop as <- <- <-. split.
           ++ assumption.
           ++ split.
              ** now apply same_rest_fixed.
              ** split.
                 --- assumption.
                 --- split.
                     +++ split.
                         *** assumption.
                         *** lia.
                         *** assumption.
                         *** assumption.
                         *** assumption.
                     +++ split.
                         *** intros Heq. discriminate.
                         *** assumption.
        (* The watchers of p are done: move on *)
        -- pose proof Hrest as (Hcm & Hqh & _ & _ & _ & _ & _ & _ & _ & Hnv).
           assert (Hwf1: WellFormed (state m1 f)).
           ++ now apply (derivation_well_formed DPLL_BJ m m1 f f).
           ++ destruct (IH m1 m' f (advance x1) x' r) as (Hder' & Hfixed' & Hincl' & Hres').
              ** split.
                 --- now apply (core_ext m1 f x1).
                 --- simpl. lia.
                 --- intros j ls a b Hj Hwj. simpl in Hj, Hwj |- *. destruct (Hwatch1 j ls a b Hj Hwj) as [H1 H2].
                     assert (Hnext: forall (z o: Lit), (z = p -> lookup (vals x1) o = Some true) ->
                       Queued (tr x1) (qhead x1) (tlen x1) (¬z) \/ lookup (vals x1) o = Some true ->
                       Queued (tr x1) (S (qhead x1)) (tlen x1) (¬z) \/ lookup (vals x1) o = Some true).
                     +++ intros z o Hzp [[j0 [Hj0 Hz]]|Ho].
                         *** destruct (Nat.eq_dec j0 (qhead x1)) as [->|Hne].
                             ---- right. apply Hzp. rewrite Hhead1 in Hz. rewrite <- (Neg.involutive z), <- Hz.
                                  apply Neg.involutive.
                             ---- left. exists j0. split.
                                  ++++ lia.
                                  ++++ assumption.
                         *** now right.
                     +++ destruct (Hdone eq_refl j ls a b Hj Hwj) as [Ha Hb]. split.
                         *** intros Hfa. now apply Hnext, H1.
                         *** intros Hfb. now apply Hnext, H2.
                 --- assumption.
                 --- assumption.
              ** assumption.
              ** simpl. now rewrite Hnv.
              ** simpl. rewrite Hnv. pose proof (trail_bound m1 f x1 Hcore1 Hwf1) as Hbound1.
                 rewrite Hnv in Hbound1. specialize (Hbound1 Hbound). lia.
              ** assumption.
              ** split.
                 --- now apply rt_trans with (state m1 f).
                 --- split.
                     +++ apply (same_fixed_trans _ x1).
                         *** now apply same_rest_fixed.
                         *** apply (same_fixed_trans _ (advance x1)).
                             ---- now repeat split.
                             ---- assumption.
                     +++ split.
                         *** now apply incl_trans with (vals x1).
                         *** assumption.
    + injection Hprop as <- <- <-. apply Nat.ltb_ge in Hlt. split.
      * apply rt_refl.
      * split.
        -- now repeat split.
        -- split.
           ++ apply incl_refl.
           ++ split.
              ** assumption.
              ** split.
                 --- intros _. destruct Hinv as [_ Hq _ _ _]. lia.
                 --- intros i Heq. discriminate.
Qed.

(* Assigning an unassigned literal keeps propagation consistent: it is queued. *)
Lemma prop_inv_assign: forall (m: PA) (f: CNF) (x: Ctx) (l: Lit) (r: nat),
  PropInv m f x -> lookup (vals x) l = None -> PropInv ⟨m, l⟩ f (assign x l r).
Proof.
  intros m f x l r [[Hvals Hfresh Htrail Hsound Hshaped] Hq Hwatch Hsaved Hlisted] Hl. split.
  - split.
    + intros y. simpl. now rewrite lookup_add, Hvals.
    + split.
      * assumption.
      * now rewrite <- Hvals.
    + now apply trail_of_cons.
    + assumption.
    + assumption.
  - simpl. lia.
  - intros j ls a b Hj Hwj. simpl in Hj, Hwj |- *. apply (watch_q_assign (vals x) (Queued (tr x) (qhead x) (tlen x))).
    + now apply (Hwatch j ls).
    + assumption.
    + intros y. apply queued_cons.
    + now apply queued_new.
  - assumption.
  - assumption.
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
              ** destruct Hrest as [Hcm _]. rewrite Hcm, Hi in Hj'. injection Hj' as <-. discriminate.
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
        -- destruct (IH ⟨m, a⟩ m' f (assign x a (S i)) x' r) as (Hder & Hrest & Hincl & Hinv' & Hnone & Hsome).
           ++ now apply prop_inv_assign.
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
                 --- apply (same_rest_trans _ (assign x a (S i))).
                     +++ now repeat split.
                     +++ assumption.
                 --- split.
                     +++ apply incl_trans with (vals (assign x a (S i))).
                         *** apply incl_set_value.
                             ---- apply incl_refl.
                             ---- assumption.
                         *** assumption.
                     +++ repeat (split; try assumption). intros Hr j ls [<-|Hj] Hj'.
                         *** destruct Hrest as [Hcm _]. simpl in Hcm. rewrite Hcm, Hi in Hj'. injection Hj' as <-.
                             discriminate.
                         *** now apply (Hnone Hr j).
    (* Not a clause *)
    + destruct (IH m m' f x x' r) as (Hder & Hrest & Hincl & Hinv' & Hnone & Hsome).
      * assumption.
      * intros j ls Hj. apply Hshort. now right.
      * assumption.
      * repeat (split; try assumption). intros Hr j ls [<-|Hj] Hj'.
        -- destruct Hrest as [Hcm _]. rewrite Hcm, Hi in Hj'. discriminate.
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

(* Visits, propagation and checking the short clauses only extend the trail by propagations. *)
Lemma visit_extends: forall (p: Lit) (ws kept: list nat) (m m': PA) (x x': Ctx) (r: option nat),
  visit p ws kept m x = (m', x', r) -> Extends m m'.
Proof.
  intros p ws. induction ws as [|i rest IH]; intros kept m m' x x' r Hvisit; simpl in Hvisit.
  - injection Hvisit as <- _ _. apply extends_refl.
  - destruct (tget (wat x) i) as [w1 w2]. destruct ((w1 =? p) || (w2 =? p)).
    + destruct (lookup_true (vals x) (if w1 =? p then w2 else w1)).
      * now apply IH in Hvisit.
      * destruct (tget (cmap x) i) as [ls|].
        -- destruct (find _ ls) as [r'|].
           ++ now apply IH in Hvisit.
           ++ destruct (lookup_undef (vals x) (if w1 =? p then w2 else w1)).
              ** apply (extends_cons m m' (if w1 =? p then w2 else w1)). now apply IH in Hvisit.
              ** injection Hvisit as <- _ _. apply extends_refl.
        -- now apply IH in Hvisit.
    + now apply IH in Hvisit.
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
