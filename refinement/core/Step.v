From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require SetoidList.
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
From RocqSAT Require Import Entails.
From RocqSAT Require Import Measure.
From RocqSAT Require Import Rule.
From RocqSAT Require Import Trans.
From RocqSAT.rules Require Import Decide.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Search.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import Heur.
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement Require Import Analysis.

(* The parts of the solver step of SolverStep.v, on the context of Ctx.v: the cursor
   of decisions, the positions of the decisions (LimsOf) and the trail they give with the
   trail table (trail), the invariant between steps (StepCore, StepInv), the checks of
   the short clauses and propagation (check_shorts_step, propagate_step), deciding
   (decide_spec), jumping back (cut, back, jump_core, unset_range), the final states
   (final_state), and the initial context for any clause lists (initial_of,
   initial_of_inv). *)

Section Cursor.
  (* The cursor c of the literals alls[0..n) of f: every unassigned literal of f is in
     alls[c..n). *)
  Definition CursorT (v: Values) (f: CNF) (alls: Table Lit) (n c: nat): Prop :=
    c <= n /\ (forall (j: nat), j < n -> tget alls j ∈ f) /\
    (forall (l: Lit), l ∈ f -> lookup v l = None ->
       exists (j: nat), c <= j < n /\ tget alls j = l).

  (* The first position from c on with an unassigned literal, or n (fuel n - c
     suffices). *)
  Fixpoint skip_from (v: Values) (alls: Table Lit) (n fuel c: nat): nat :=
  match fuel with
  | 0       => c
  | S fuel' =>
    if (c <? n) && negb (lookup_undef v (tget alls c)) then skip_from v alls n fuel' (S c)
    else c
  end.

  (* skip_from moves a cursor to an unassigned literal, or to n. *)
  Lemma skip_from_spec: forall (v: Values) (f: CNF) (alls: Table Lit) (n fuel c: nat),
    n - c <= fuel ->
    CursorT v f alls n c ->
    let c' := skip_from v alls n fuel c in
    CursorT v f alls n c' /\ (c' < n -> lookup v (tget alls c') = None).
  Proof.
    intros v f alls n fuel.
    induction fuel as [|fuel IH]; intros c Hfuel [Hc [Hin Hcomplete]]; simpl.
    - split.
      + now split.
      + intros Hlt. lia.
    - destruct ((c <? n) && negb (lookup_undef v (tget alls c))) eqn:Hskip.
      + apply andb_prop in Hskip as [Hlt Hdef]. apply Nat.ltb_lt in Hlt. apply IH.
        * lia.
        * split.
          -- lia.
          -- split.
             ++ assumption.
             ++ intros l Hl_in_f Hl. destruct (Hcomplete l Hl_in_f Hl) as [j [Hj Hjl]].
                destruct (Nat.eq_dec j c) as [->|Hne].
                ** exfalso. unfold lookup_undef in Hdef. rewrite Hjl, Hl in Hdef.
                   discriminate.
                ** exists j. split.
                   --- lia.
                   --- assumption.
      + split.
        * now split.
        * intros Hlt. apply andb_false_iff in Hskip as [Hge|Hundef].
          -- apply Nat.ltb_ge in Hge. lia.
          -- apply negb_false_iff in Hundef. unfold lookup_undef in Hundef.
             destruct (lookup v (tget alls c)); easy.
  Qed.

  (* Fewer unassigned literals keep a cursor valid. *)
  Lemma cursor_incl: forall (v v': Values) (f: CNF) (alls: Table Lit) (n c: nat),
    (forall (l: Lit), lookup v' l = None -> lookup v l = None) ->
    CursorT v f alls n c -> CursorT v' f alls n c.
  Proof.
    intros v v' f alls n c Hincl [Hc [Hin Hcomplete]]. split.
    - assumption.
    - split.
      + assumption.
      + intros l Hl_in_f Hl. apply Hcomplete.
        * assumption.
        * now apply Hincl.
  Qed.

  (* A literal unassigned in v' is unassigned in the smaller v. *)
  Lemma incl_undef: forall (v v': Values) (l: Lit),
    Incl v v' -> lookup v' l = None -> lookup v l = None.
  Proof.
    intros v v' l Hincl Hl. destruct (lookup v l) as [b|] eqn:Hb.
    - apply Hincl in Hb. congruence.
    - reflexivity.
  Qed.
End Cursor.

(* The first literal to decide on from the cursor of x on that is unassigned, or nlits x
   when there is none: where the next decision by the cursor goes. *)
Definition next_undef (x: Ctx): nat :=
  skip_from (vals x) (alls x) (nlits x) (nlits x - cur x) (cur x).

(* With the cursor of x consistent, so is the next unassigned literal. *)
Lemma next_undef_spec: forall (f: CNF) (x: Ctx),
  CursorT (vals x) f (alls x) (nlits x) (cur x) ->
  CursorT (vals x) f (alls x) (nlits x) (next_undef x) /\
  (next_undef x < nlits x -> lookup (vals x) (tget (alls x) (next_undef x)) = None).
Proof.
  intros f x Hcursor. apply skip_from_spec.
  - lia.
  - assumption.
Qed.

Section Lims.
  (* lims holds the positions of the decisions of m on its trail, newest first. *)
  Fixpoint LimsOf (lims: list nat) (m: PA): Prop :=
  match m with
  | ⟨⟩     => lims = []
  | ⟨m, _⟩ => LimsOf lims m
  | ⟨m; _⟩ =>
    match lims with
    | j :: lims' => j = PA.length m /\ LimsOf lims' m
    | []         => False
    end
  end.

  (* Propagations keep the positions of the decisions. *)
  Lemma lims_extends: forall (lims: list nat) (m m': PA),
    LimsOf lims m -> Extends m m' -> LimsOf lims m'.
  Proof.
    intros lims m m' Hlims [n [-> Hn]]. induction n as [|n IH l|n IH l]; simpl in Hn |- *.
    - assumption.
    - now apply IH.
    - destruct Hn.
  Qed.

  (* The positions of the decisions of ⟨m; l ++ n⟩: those of n, that of l, then those of
     m. *)
  Lemma lims_split: forall (lims: list nat) (m n: PA) (l: Lit),
    LimsOf lims ⟨m; l ++ n⟩ ->
    exists (lims': list nat),
      skipn (decisions n) lims = PA.length m :: lims' /\ LimsOf lims' m /\
      length lims = decisions n + S (length lims').
  Proof.
    intros lims m n l. revert lims.
    induction n as [|n IH y|n IH y]; intros lims Hlims; simpl in Hlims |- *.
    - destruct lims as [|j lims].
      + contradiction.
      + destruct Hlims as [-> Hlims]. now exists lims.
    - now apply IH.
    - destruct lims as [|j lims].
      + contradiction.
      + destruct Hlims as [_ Hlims].
        destruct (IH lims Hlims) as (lims' & Hskip & Hlims' & Hlen). exists lims'.
        simpl. split.
        * assumption.
        * split.
          -- assumption.
          -- lia.
  Qed.

  (* Without decisions, no positions. *)
  Lemma lims_none: forall (lims: list nat) (m: PA),
    LimsOf lims m -> NoDecisions m -> lims = [].
  Proof.
    intros lims m. revert lims.
    induction m as [|m IH l|m IH l]; intros lims Hlims Hm; simpl in Hlims, Hm.
    - assumption.
    - now apply IH.
    - destruct Hm.
  Qed.

  (* Decision positions are on the trail, one per decision. *)
  Lemma lims_lt: forall (lims: list nat) (m: PA) (j: nat),
    LimsOf lims m -> In j lims -> j < PA.length m.
  Proof.
    intros lims m. revert lims.
    induction m as [|m IH l|m IH l]; intros lims j Hlims Hj; simpl in Hlims |- *.
    - now subst lims.
    - apply (IH lims j) in Hlims.
      + lia.
      + assumption.
    - destruct lims as [|j' lims].
      + contradiction.
      + destruct Hlims as [-> Hlims]. destruct Hj as [<- | Hj].
        * lia.
        * apply (IH lims j) in Hlims.
          -- lia.
          -- assumption.
  Qed.
End Lims.

Section Trail.
  (* The trail the tables hold: the first n literals of tr, those at the positions ls
     decided and the others propagated. *)
  Fixpoint trail_upto (tr: Table Lit) (ls: list nat) (n: nat): PA :=
  match n with
  | 0    => ⟨⟩
  | S n' =>
    if existsb (Nat.eqb n') ls then ⟨(trail_upto tr ls n'); (tget tr n')⟩
    else ⟨(trail_upto tr ls n'), (tget tr n')⟩
  end.

  (* The trail of x: the first tlen x literals of tr x, decided at the positions
     lims x. *)
  Definition trail (x: Ctx): PA := trail_upto (tr x) (lims x) (tlen x).

  (* The trail the tables hold has the first n literals. *)
  Lemma trail_upto_length: forall (tr: Table Lit) (ls: list nat) (n: nat),
    PA.length (trail_upto tr ls n) = n.
  Proof.
    intros tr ls n. induction n as [|n IH]; simpl.
    - reflexivity.
    - destruct (existsb (Nat.eqb n) ls).
      + simpl. now rewrite IH.
      + simpl. now rewrite IH.
  Qed.

  (* The trail of x is tlen x long. *)
  Lemma trail_length: forall (x: Ctx), PA.length (trail x) = tlen x.
  Proof. intros x. apply trail_upto_length. Qed.

  (* A position from n on does not matter for the first n literals. *)
  Lemma trail_upto_skip: forall (tr: Table Lit) (ls: list nat) (k n: nat),
    n <= k -> trail_upto tr (k :: ls) n = trail_upto tr ls n.
  Proof.
    intros tr ls k n. induction n as [|n IH]; intros Hn; simpl.
    - reflexivity.
    - replace (Nat.eqb n k) with false by (symmetry; apply Nat.eqb_neq; lia).
      simpl. rewrite IH by lia. reflexivity.
  Qed.

  (* The tables hold exactly one trail: tr has the literals of m and ls the positions of
     its decisions. *)
  Lemma trail_upto_of: forall (tr: Table Lit) (ls: list nat) (m: PA),
    TrailOf tr (PA.length m) m -> LimsOf ls m -> trail_upto tr ls (PA.length m) = m.
  Proof.
    intros tr ls m. revert ls.
    induction m as [|m IH l|m IH l]; intros ls Htrail Hlims; simpl in Hlims |- *.
    - reflexivity.
    - (* a propagation: its position is not that of a decision *)
      destruct (trail_of_snoc tr _ m ⟨m, l⟩ l eq_refl Htrail) as (_ & Hl & Htrail').
      replace (existsb (Nat.eqb (PA.length m)) ls) with false.
      + rewrite Hl, IH.
        * reflexivity.
        * assumption.
        * assumption.
      + symmetry. apply Bool.not_true_iff_false. intros Hex.
        apply existsb_exists in Hex as [j [Hj Heq]]. apply Nat.eqb_eq in Heq.
        apply (lims_lt ls m j Hlims) in Hj. lia.
    - (* a decision: its position comes first in ls *)
      destruct ls as [|j ls].
      + contradiction.
      + destruct Hlims as [-> Hlims].
        destruct (trail_of_snoc tr _ m ⟨m; l⟩ l eq_refl Htrail) as (_ & Hl & Htrail').
        simpl. rewrite Nat.eqb_refl. simpl. rewrite trail_upto_skip by lia.
        rewrite Hl, IH.
        * reflexivity.
        * assumption.
        * assumption.
  Qed.
End Trail.

(* For every decision on m, the saved cursor is the one before it. *)
Fixpoint SavedC (f: CNF) (alls: Table Lit) (n: nat) (m: PA) (st: list nat): Prop :=
match m with
| ⟨⟩     => st = []
| ⟨m, _⟩ => SavedC f alls n m st
| ⟨m; _⟩ =>
  match st with
  | c :: st' => CursorT (values m) f alls n c /\ SavedC f alls n m st'
  | []       => False
  end
end.

(* The context before deciding at cursor c: c is saved, and the decision level goes up. *)
Definition open_level (x: Ctx) (c: nat): Ctx :=
mkCtx (vals x) (cmap x) (wls x) (tr x) (tlen x) (qhead x) (shorts x) (alls x) (nlits x) c
  (c :: saved x) (tlen x :: lims x) (rsn x) (lvl x) (S (dl x)) (mrk x) (lower x) (phs x)
  (nvars x) (rcl x) (rps x) (nr x) (rcap x) (hr x).

(* The cursor of x is c, for the formula f. *)
Abbreviation CursorAt f x c := (CursorT (vals x) f (alls x) (nlits x) c).

(* The positions of the decisions of x are on its trail. *)
Abbreviation LimsBelow x := (forall (j: nat), In j (lims x) -> j < tlen x).

(* The literals to decide on of the heuristic h are literals of f. *)
Definition DlitIn (f: CNF) (h: Heur): Prop := DlitAll (fun (l: Lit) => l ∈ f) h.

Section Unset.
  (* v without the values of the literals at the n positions from j on, newest first. *)
  Fixpoint unset_range (v: Values) (tr: Table Lit) (j n: nat): Values :=
  match n with
  | 0    => v
  | S n' => unset_range (unset_value v (tget tr (j + n'))) tr j n'
  end.

  (* Unsetting the positions of the segment from the decision d of ⟨mt; d ++ n⟩ on is
     unassigning that segment. *)
  Lemma unset_range_spec: forall (tr: Table Lit) (tlen: nat) (mt n: PA) (d: Lit)
    (v: Values),
    TrailOf tr tlen ⟨mt; d ++ n⟩ ->
    unset_range v tr (PA.length mt) (S (PA.length n)) = unassign_segment v d n.
  Proof.
    intros tr tlen mt n d. revert tlen.
    induction n as [|n IH x|n IH x]; intros tlen v Htrail.
    - destruct (trail_of_snoc tr tlen mt ⟨mt; d⟩ d eq_refl Htrail) as (_ & Hd & _). simpl.
      now rewrite Nat.add_0_r, Hd.
    - destruct (trail_of_snoc tr tlen ⟨mt; d ++ n⟩ ⟨mt; d ++ n, x⟩ x eq_refl Htrail)
        as (_ & Hx & Hprefix).
      cbn [unassign_segment PA.length unset_range].
      replace (PA.length mt + S (PA.length n)) with (PA.length ⟨mt; d ++ n⟩).
      + rewrite Hx. now apply (IH (PA.length ⟨mt; d ++ n⟩)).
      + rewrite (pa_length_app ⟨mt; d⟩ n). simpl. lia.
    - destruct (trail_of_snoc tr tlen ⟨mt; d ++ n⟩ ⟨mt; d ++ n; x⟩ x eq_refl Htrail)
        as (_ & Hx & Hprefix).
      cbn [unassign_segment PA.length unset_range].
      replace (PA.length mt + S (PA.length n)) with (PA.length ⟨mt; d ++ n⟩).
      + rewrite Hx. now apply (IH (PA.length ⟨mt; d ++ n⟩)).
      + rewrite (pa_length_app ⟨mt; d⟩ n). simpl. lia.
  Qed.

  #[global] Arguments unset_range_spec {tr tlen}.

  (* Unassigning the last level is unassigning the segment of its decision. *)
  Lemma unassign_level_segment: forall (v: Values) (m n: PA) (l: Lit),
    NoDecisions n -> unassign_level v ⟨m; l ++ n⟩ = unassign_segment v l n.
  Proof.
    intros v m n l. revert v.
    induction n as [|n IH x|n IH x]; intros v Hn; simpl in Hn |- *.
    - reflexivity.
    - now apply IH.
    - destruct Hn.
  Qed.
End Unset.

(* Cutting the trail at position j, as cut does: the literals from j on are unassigned,
   the trail and the queue end at j, the reason clauses of those literals are dropped, and
   their atoms go back into the heap. *)
Definition cut (x: Ctx) (j: nat): Ctx :=
  x <| vals := unset_range (vals x) (tr x) j (tlen x - j) |> <| tlen := j |>
    <| qhead := j |>
    <| nr := pop_reasons (rps x) j (nr x) |>
    <| hr := reinsert (hr x) (tr x) (nvars x) j (tlen x) (tlen x - j) |>.

(* Going back to level d, as resolve does: cut at the position j of the decision of level
   d + 1, with the cursor c saved for it, and the saved cursors st and decision positions
   ls of the levels up to d. *)
Definition back (x: Ctx) (j c: nat) (st: list nat) (d: nat) (ls: list nat): Ctx :=
  (cut x j) <| cur := c |> <| saved := st |> <| dl := d |> <| lims := ls |>.

(* Going back after an analysis, field by field: the values from j on are unset, the trail
   and the queue end at j, the reason clauses from j on are dropped and their atoms go
   back into the heap; the marks, the lower literals and the heuristic are those the
   analysis left. *)
Lemma back_fields: forall (x: Ctx) (mk: Table bool) (lt: list Lit) (h: Heur) (j c: nat)
  (st ls: list nat) (d: nat),
  back (x <| mrk := mk |> <| lower := lt |> <| hr := h |>) j c st d ls =
  mkCtx (unset_range (vals x) (tr x) j (tlen x - j)) (cmap x) (wls x) (tr x) j j
    (shorts x) (alls x) (nlits x) c st ls (rsn x) (lvl x) d mk lt (phs x) (nvars x)
    (rcl x) (rps x) (pop_reasons (rps x) j (nr x)) (rcap x)
    (reinsert h (tr x) (nvars x) j (tlen x) (tlen x - j)).
Proof. reflexivity. Qed.

(* The reason clauses are entailed, and stored for increasing positions on the trail. *)
Record SlotsOk {f: CNF} {x: Ctx}: Prop := {
  so_entailed: forall (j: nat), j < nr x -> Entailed f (tget (rcl x) j);
  so_order: forall (j1 j2: nat), j1 < j2 < nr x -> tget (rps x) j1 < tget (rps x) j2;
  so_below: forall (j: nat), j < nr x -> tget (rps x) j < tlen x
}.
Arguments SlotsOk : clear implicits.

(* Every clause of f is in the clause table cm. *)
Abbreviation AllStored f cm :=
  (forall (c: Clause), c ∈ f ->
     exists (i: nat) (ls: list Lit),
       tget cm i = Some ls /\ forall (l: Lit), In l ls <-> l ∈ c).

(* Every empty clause of cm is in the list sh of short clauses. *)
Abbreviation EmptyInShorts cm sh := (forall (i: nat), tget cm i = Some [] -> In i sh).

(* The context agrees with the state m f between steps. *)
Record StepCore {m: PA} {f: CNF} {x: Ctx}: Prop := {
  sc_prop: PropInv m f x;
  sc_complete: AllStored f (cmap x);
  sc_cursor: CursorAt f x (cur x);
  sc_saved: SavedC f (alls x) (nlits x) m (saved x);
  sc_empty: EmptyInShorts (cmap x) (shorts x);
  sc_shorts: ShortsShort (cmap x) (shorts x);
  sc_marks: Unmarked (mrk x);
  sc_bound: S (max_atom_f f) <= nvars x;
  sc_slots: SlotsOk f x;
  sc_dlit: DlitIn f (hr x);
  sc_lims: LimsOf (lims x) m;
  sc_lower: lower x = []
}.
Arguments StepCore : clear implicits.

(* Moreover the state is well-formed and entailed, as every reachable state is. *)
Definition StepInv (s: State) (x: Ctx): Prop :=
match s with
| fail      => True
| state m f => StepCore m f x /\ WellFormed (state m f) /\ Entails f m
end.

(* Between steps, the state is the trail of the context. *)
Lemma step_core_trail: forall (m: PA) (f: CNF) (x: Ctx), StepCore m f x -> m = trail x.
Proof.
  intros m f x [[[_ _ Htrail _ _ _ _] _ _ _ _ _] _ _ _ _ _ _ _ _ _ Hlims].
  unfold trail. pose proof Htrail as [Hlen _].
  rewrite trail_lits_length in Hlen. rewrite Hlen in Htrail |- *.
  symmetry. now apply trail_upto_of.
Qed.
Arguments step_core_trail {m f x}.

Section Split.
  (* The decision l of ⟨m; l ++ n⟩ has its cursor saved after those of n. *)
  Lemma saved_c_split: forall (f: CNF) (alls: Table Lit) (k: nat) (m n: PA) (l: Lit)
    (st: list nat),
    SavedC f alls k ⟨m; l ++ n⟩ st ->
    exists (c: nat) (st': list nat),
      skipn (decisions n) st = c :: st' /\ CursorT (values m) f alls k c /\
      SavedC f alls k m st'.
  Proof.
    intros f alls k m n l. induction n as [|n IH l'|n IH l']; simpl; intros st Hsaved.
    - destruct st as [|c st'].
      + contradiction.
      + now exists c, st'.
    - now apply IH.
    - destruct st as [|c st'].
      + contradiction.
      + destruct Hsaved as [_ Hsaved]. now apply IH.
  Qed.

  (* Before the decision l of ⟨m; l ++ n⟩, the watches were fine with an empty queue. *)
  Lemma saved_q_split: forall (cm: ClauseMap) (m n: PA) (l: Lit),
    SavedQ cm ⟨m; l ++ n⟩ -> AllWatchQ (values m) NoQueue cm /\ SavedQ cm m.
  Proof.
    intros cm m n l. induction n as [|n IH l'|n IH l']; simpl.
    - intros Hsaved. assumption.
    - assumption.
    - intros [_ Hsaved]. now apply IH.
  Qed.

  (* The saved cursors only depend on the decisions. *)
  Lemma saved_c_extends: forall (f: CNF) (alls: Table Lit) (k: nat) (m n: PA)
    (st: list nat),
    NoDecisions n -> SavedC f alls k m st -> SavedC f alls k ⟨m ++ n⟩ st.
  Proof.
    intros f alls k m n st. induction n as [|n IH l|n IH l]; simpl.
    - easy.
    - assumption.
    - intros [].
  Qed.

  (* A queue from q to q is empty. *)
  Lemma watch_q_empty: forall (v: Values) (tr: Table Lit) (q: nat) (cm: ClauseMap),
    AllWatchQ v (Queued tr q q) cm -> AllWatchQ v NoQueue cm.
  Proof.
    intros v tr q cm Hall i ls Hi w Hw Hf.
    destruct (Hall i ls Hi w Hw Hf) as [[j [Hj _]]|Ht].
    - lia.
    - now right.
  Qed.

  (* Fine watches only depend on the values of literals. *)
  Lemma all_watch_q_ext: forall (v v': Values) (Q: Lit -> Prop) (cm: ClauseMap),
    (forall (l: Lit), lookup v l = lookup v' l) -> AllWatchQ v Q cm -> AllWatchQ v' Q cm.
  Proof.
    intros v v' Q cm Hext Hall i ls Hi w Hw Hf. rewrite <- Hext in Hf.
    destruct (Hall i ls Hi w Hw Hf) as [Hq|[y [Hy Ht]]].
    - now left.
    - right. exists y. split.
      + assumption.
      + now rewrite <- Hext.
  Qed.

  (* Reordering keeps every clause of f in the clause table. *)
  Lemma reordered_complete: forall (f: CNF) (cm cm': ClauseMap),
    Reordered cm cm' -> AllStored f cm -> AllStored f cm'.
  Proof.
    intros f cm cm' Hre Hcomplete c Hc_in_f.
    destruct (Hcomplete c Hc_in_f) as [i [ls [Hi Hiff]]].
    destruct (reordered_some_r cm cm' i ls Hre Hi) as [ls' [Hi' Hperm]]. exists i, ls'.
    split.
    - assumption.
    - intros l. rewrite <- Hiff. split.
      + apply Permutation_in. now apply Permutation_sym.
      + now apply Permutation_in.
  Qed.

  (* The trail of a context grows when its trail is extended. *)
  Lemma core_tlen_extends: forall (m m': PA) (f: CNF) (x x': Ctx),
    Core m f x -> Core m' f x' -> Extends m m' -> tlen x <= tlen x'.
  Proof.
    intros m m' f x x' Hcore Hcore' [n [-> _]].
    destruct (core_trail Hcore) as [Hlen _].
    destruct (core_trail Hcore') as [Hlen' _].
    rewrite Hlen, Hlen', !trail_lits_length, pa_length_app. lia.
  Qed.

  (* The reason clauses stay fine when the trail grows. *)
  Lemma slots_grow: forall (f: CNF) (x x': Ctx),
    SlotsOk f x -> rcl x' = rcl x -> rps x' = rps x -> nr x' = nr x ->
    tlen x <= tlen x' -> SlotsOk f x'.
  Proof.
    intros f x x' [Hent Horder Hbelow] Hrcl Hrps Hnr Hlen. split.
    - intros j Hj. rewrite Hrcl. apply Hent. now rewrite <- Hnr.
    - intros j1 j2 Hj. rewrite Hrps. apply Horder. now rewrite <- Hnr.
    - intros j Hj. rewrite Hrps. rewrite Hnr in Hj. pose proof (Hbelow j Hj). lia.
  Qed.
End Split.

(* Checking the short clauses is a derivation to a consistent context; if no clause is
   false, none is empty. *)
Lemma check_shorts_step: forall (m: PA) (f: CNF) (x x1: Ctx) (r: option nat),
  StepCore m f x ->
  check_shorts (shorts x) x = (x1, r) ->
  exists (m1: PA),
  state m f ==>*[DPLL_BJ] state m1 f /\ Extends m m1 /\ StepCore m1 f x1 /\
  (r = None -> NoEmpty x1) /\ (forall (i: nat), r = Some i -> ClauseFalse x1 i).
Proof.
  intros m f x x1 r
    [Hprop Hcomplete Hcursor Hsaved Hempty Hshorts Hmarks Hbound Hslots Hdlit Hlims Hlow]
    Hcheck.
  destruct (check_shorts_spec (shorts x) m f x x1 r Hprop Hshorts Hcheck)
    as (m1 & Hext & Hder & ([Hcm Hkept] & _) & Hincl & Hprop1 & Hnone & Hsome).
  injection Hkept as Hsh Hal Hnl Hcur Hsv _ Hmk Hnv Hrcl Hrps Hnr _ Hhr.
  exists m1. split.
  - assumption.
  - split.
    + assumption.
    + split.
      * split.
        -- assumption.
        -- now apply (reordered_complete f (cmap x)).
        -- rewrite Hal, Hnl, Hcur. apply (cursor_incl (vals x)).
           ++ intros l. now apply incl_undef.
           ++ assumption.
        -- rewrite Hal, Hnl, Hsv. destruct Hext as [n [-> Hn]]. now apply saved_c_extends.
        -- intros i Hi. rewrite Hsh. apply Hempty.
           now apply (reordered_empty (cmap x) (cmap x1)).
        -- intros i ls Hin Hi. rewrite Hsh in Hin.
           destruct (reordered_length (cmap x) (cmap x1) i ls Hcm Hi) as [ls0 [Hi0 ->]].
           now apply (Hshorts i).
        -- now rewrite Hmk.
        -- now rewrite Hnv.
        -- apply (slots_grow f x).
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ apply (core_tlen_extends m m1 f).
              ** apply Hprop.
              ** apply Hprop1.
              ** assumption.
        -- unfold DlitIn. rewrite Hhr. assumption.
        -- (* checking keeps the positions of the decisions *)
           pose proof (check_shorts_stacks (shorts x) x) as [Hl _]. rewrite Hcheck in Hl.
           cbn [fst] in Hl. rewrite Hl. now apply (lims_extends (lims x) m).
        -- (* and leaves no lower literals *)
           pose proof (check_shorts_stacks (shorts x) x) as [_ Hlo].
           rewrite Hcheck in Hlo.
           cbn [fst] in Hlo. rewrite Hlo. assumption.
      * split.
        -- intros Hr i Hi. apply (Hnone Hr i []).
           ++ apply Hempty. now apply (reordered_empty (cmap x) (cmap x1)).
           ++ assumption.
           ++ reflexivity.
        -- assumption.
Qed.

(* Propagation is a derivation to a consistent context, and empties the queue unless a
   clause is false. *)
Lemma propagate_step: forall (m1: PA) (f: CNF) (x1 x2: Ctx) (r: option nat),
  StepCore m1 f x1 ->
  WellFormed (state m1 f) ->
  NoEmpty x1 ->
  propagate (S (nvars x1)) (x1 <| shorts := [] |>) = (x2, r) ->
  exists (m2: PA),
  state m1 f ==>*[DPLL_BJ] state m2 f /\ Extends m1 m2 /\ StepCore m2 f x2 /\
  shorts x2 = [] /\ NoEmpty x2 /\
  (r = None -> qhead x2 = tlen x2) /\ (forall (i: nat), r = Some i -> ClauseFalse x2 i).
Proof.
  intros m1 f x1 x2 r
    [Hprop Hcomplete Hcursor Hsaved Hempty Hshorts Hmarks Hbound Hslots Hdlit Hlims Hlow]
    Hwf
    Hnonempty Hpropagate.
  destruct (propagate_spec (S (nvars x1)) m1 f (x1 <| shorts := [] |>) x2 r) as
    (m2 & Hext & Hder & [Hcm Hkept] & Hincl & Hprop2 & Hnone & Hsome).
  - destruct Hprop as [Hcore Hq Hwatch Hsaved' Hlisted Hblocked]. split.
    + now apply (core_ext m1 f x1).
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
  - assumption.
  - assumption.
  - simpl. lia.
  - assumption.
  - injection Hkept as Hsh Hal Hnl Hcur Hsv _ Hmk Hnv Hrcl Hrps Hnr _ Hhr.
    simpl in Hcm, Hsh, Hal, Hnl, Hcur, Hsv, Hmk, Hnv, Hrcl, Hrps, Hnr, Hhr, Hincl.
    exists m2. split.
    + assumption.
    + split.
      * assumption.
      * split.
        -- split.
           ++ assumption.
           ++ now apply (reordered_complete f (cmap x1)).
           ++ rewrite Hal, Hnl, Hcur. apply (cursor_incl (vals x1)).
              ** intros l. now apply incl_undef.
              ** assumption.
           ++ rewrite Hal, Hnl, Hsv. destruct Hext as [n [-> Hn]].
              now apply saved_c_extends.
           ++ intros i Hi. apply (reordered_empty (cmap x1) (cmap x2)) in Hi.
              ** now apply Hnonempty in Hi.
              ** assumption.
           ++ rewrite Hsh. intros i ls [].
           ++ now rewrite Hmk.
           ++ now rewrite Hnv.
           ++ apply (slots_grow f x1).
              ** assumption.
              ** assumption.
              ** assumption.
              ** assumption.
              ** apply (core_tlen_extends m1 m2 f x1).
                 --- apply Hprop.
                 --- apply Hprop2.
                 --- assumption.
           ++ unfold DlitIn. rewrite Hhr. assumption.
           ++ (* propagation keeps the positions of the decisions *)
              pose proof (propagate_stacks (S (nvars x1)) (x1 <| shorts := [] |>))
                as [Hl _].
              rewrite Hpropagate in Hl. cbn [fst set_shorts lims] in Hl. rewrite Hl.
              now apply (lims_extends (lims x1) m1).
           ++ (* and leaves no lower literals *)
              pose proof (propagate_stacks (S (nvars x1)) (x1 <| shorts := [] |>))
                as [_ Hlo].
              rewrite Hpropagate in Hlo. cbn [fst set_shorts lower] in Hlo. rewrite Hlo.
              assumption.
        -- split.
           ++ assumption.
           ++ split.
              ** intros i Hi. apply (reordered_empty (cmap x1) (cmap x2)) in Hi.
                 --- now apply Hnonempty in Hi.
                 --- assumption.
              ** now split.
Qed.

(* Watches fine up to an empty queue are fine up to any queue. *)
Lemma watch_q_weaken: forall (v: Values) (Q: Lit -> Prop) (cm: ClauseMap),
  AllWatchQ v NoQueue cm -> AllWatchQ v Q cm.
Proof.
  intros v Q cm Hall i ls Hi w Hw Hf. destruct (Hall i ls Hi w Hw Hf) as [[]|Ht].
  now right.
Qed.

(* The fields of the context that PropInv reads. *)
Definition prop_fields (x: Ctx) :=
  (vals x, tr x, tlen x, qhead x, cmap x, wls x, rsn x, lvl x, dl x, rcl x, rps x, nr x).

(* PropInv only looks at the values, the trail, the queue, the clauses, the watch lists
   and the levels and reasons. *)
Lemma prop_inv_ext: forall (m: PA) (f: CNF) (x x': Ctx),
  PropInv m f x -> prop_fields x' = prop_fields x -> PropInv m f x'.
Proof.
  intros m f x x' [Hcore Hq Hwatch Hsaved Hlisted Hblocked] Hfields.
  injection Hfields as Hv Htr Hlen Hqh Hcm Hwl Hrsn Hlv Hd Hrcl Hrps Hnr. split.
  - apply (core_ext m f x).
    + assumption.
    + unfold core_fields. now rewrite Hv, Htr, Hlen, Hcm, Hrsn, Hlv, Hd, Hrcl, Hrps, Hnr.
  - now rewrite Hqh, Hlen.
  - now rewrite Hv, Htr, Hqh, Hlen, Hcm.
  - now rewrite Hcm.
  - now rewrite Hcm, Hwl.
  - now rewrite Hcm, Hwl.
Qed.

(* The lower literals do not matter for propagation. *)
Lemma prop_inv_lower: forall (m: PA) (f: CNF) (x: Ctx) (lt: list Lit),
  PropInv m f x -> PropInv m f (x <| lower := lt |>).
Proof.
  intros m f x lt Hprop. apply (prop_inv_ext m f x).
  - assumption.
  - reflexivity.
Qed.

Section Jumps.
  (* Dropping reason clauses that no literal of m uses keeps the levels and reasons of
     m. *)
  Lemma trace_pop: forall (cm: ClauseMap) (rsn: Table Reason) (lv: Table nat)
    (rcl: Table (list Lit)) (rps: Table nat) (nr nr': nat) (m: PA),
    TraceOk cm rsn lv rcl rps nr m ->
    (forall (j: nat), j < nr -> tget rps j < PA.length m -> j < nr') ->
    TraceOk cm rsn lv rcl rps nr' m.
  Proof.
    intros cm rsn lv rcl rps nr nr' m.
    induction m as [|m IH t|m IH t]; cbn [TraceOk]; intros Htrace Hkeep.
    - constructor.
    - destruct Htrace as (Hlv & Hreason & Htrace). split.
      + assumption.
      + split.
        * destruct (tget rsn (extract t)) as [|i|j]; cbn [ReasonOk] in Hreason |- *.
          -- constructor.
          -- assumption.
          -- destruct Hreason as (Hj & Hpos & Hjust). split.
             ++ apply Hkeep.
                ** assumption.
                ** cbn [PA.length]. lia.
             ++ now split.
        * apply IH.
          -- assumption.
          -- intros j Hj Hpos. apply Hkeep.
             ++ assumption.
             ++ cbn [PA.length]. lia.
    - destruct Htrace as (Hlv & Htrace). split.
      + assumption.
      + apply IH.
        * assumption.
        * intros j Hj Hpos. apply Hkeep.
          -- assumption.
          -- cbn [PA.length]. lia.
  Qed.
  #[global] Arguments trace_pop {cm rsn lv rcl rps}.

  (* Storing a new reason clause keeps the levels and reasons of m. *)
  Lemma trace_push: forall (cm: ClauseMap) (rsn: Table Reason) (lv: Table nat)
    (rcl: Table (list Lit)) (rps: Table nat) (nr: nat) (m: PA) (c: list Lit) (p: nat),
    TraceOk cm rsn lv rcl rps nr m ->
    TraceOk cm rsn lv (tset rcl nr c) (tset rps nr p) (S nr) m.
  Proof.
    intros cm rsn lv rcl rps nr m c p.
    induction m as [|m IH t|m IH t]; cbn [TraceOk]; intros Htrace.
    - constructor.
    - destruct Htrace as (Hlv & Hreason & Htrace). split.
      + assumption.
      + split.
        * destruct (tget rsn (extract t)) as [|i|j]; cbn [ReasonOk] in Hreason |- *.
          -- constructor.
          -- assumption.
          -- destruct Hreason as (Hj & Hpos & Hjust).
             rewrite !tget_tset_other by lia. split.
             ++ lia.
             ++ now split.
        * now apply IH.
    - destruct Htrace as (Hlv & Htrace). split.
      + assumption.
      + now apply IH.
  Qed.

  (* Storing a reason clause keeps propagation consistent if the levels and reasons of m
     stay fine with it: propagation only looks at the reasons they give the trail. *)
  Lemma prop_inv_reasons: forall (m: PA) (f: CNF) (x: Ctx) (c: list Lit),
    PropInv m f x ->
    TraceOk (cmap x) (rsn x) (lvl x) (tset (rcl x) (nr x) c)
      (tset (rps x) (nr x) (tlen x)) (S (nr x)) m ->
    PropInv m f (add_reason x c).
  Proof.
    intros m f x c
      [[Hvals Hfresh Htrail Hsound Hnodup Hdl _] Hq Hwatch Hsaved Hlisted Hblocked]
      Htrace.
    split.
    - split.
      + assumption.
      + assumption.
      + assumption.
      + assumption.
      + assumption.
      + assumption.
      + assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
  Qed.

  (* How the literal asserted after going back to the trail mt is justified: by no
     reason, or by the reason clause of u and the lower literals that push_reason stores,
     if there is room; the clause is entailed, and the lower literals are false in mt. *)
  Definition JumpReason (f: CNF) (mt: PA) (u: Lit) (xj x': Ctx) (r: Reason): Prop :=
    (x' = xj /\ r = no_reason) \/
    (push_reason xj u = (x', r) /\ Entailed f (u :: lower xj) /\
       forall (y: Lit), In y (lower xj) -> l_eval mt y = Some false).

  (* After an analysis of x left xa, going back to before the decision d of ⟨mt; d ++ n⟩
     (with the cursor c0, saved cursors st and decision positions ls of mt) and asserting
     the unassigned u with a justified reason gives a context that agrees with ⟨mt, u⟩. *)
  Lemma jump_core: forall (mt n: PA) (f: CNF) (x xa: Ctx) (d u: Lit) (c0: nat)
    (st ls: list nat) (x': Ctx) (r: Reason),
    StepCore ⟨mt; d ++ n⟩ f x -> Analysed x xa -> Unmarked (mrk xa) ->
    l_eval mt u = None ->
    CursorT (values mt) f (alls x) (nlits x) c0 ->
    SavedC f (alls x) (nlits x) mt st -> LimsOf ls mt ->
    JumpReason f mt u (back xa (PA.length mt) c0 st (decisions mt) ls) x' r ->
    StepCore ⟨mt, u⟩ f (assign (x' <| lower := [] |>) u r).
  Proof.
    intros mt n f x xa d u c0 st ls x' r
      [[[Hvals Hfresh Htrail Hsound Hnodup Hdl Htrace] Hq Hwatch Hsavedq Hlisted
        Hblocked] Hcomplete Hcursor Hsaved Hempty Hshorts Hmarks Hbound
        [Hent Horder Hbelow] Hdlit Hlims Hlow] [Hxa Hd] Hmk Hu0 Hc0 Hst Hls Hreason.
    (* xa is x with the marks mk, the lower literals lt and the heuristic h of the
       analysis, which keeps the literals to decide on. *)
    rewrite Hxa in Hreason.
    set (mk := mrk xa) in *. set (lt := lower xa) in *. set (h := hr xa) in *.
    assert (Hh: DlitIn f h).
    { unfold DlitIn. rewrite Hd. apply Hdlit. }
    rewrite back_fields in Hreason.
    set (v' := unset_range (vals x) (tr x) (PA.length mt) (tlen x - PA.length mt))
      in Hreason.
    set (h' := reinsert h (tr x) (nvars x) (PA.length mt) (tlen x)
                 (tlen x - PA.length mt))
      in Hreason.
    set (xj := mkCtx v' (cmap x) (wls x) (tr x) (PA.length mt) (PA.length mt) (shorts x)
                 (alls x) (nlits x) c0 st ls (rsn x) (lvl x) (decisions mt) mk lt (phs x)
                 (nvars x) (rcl x) (rps x) (pop_reasons (rps x) (PA.length mt) (nr x))
                 (rcap x) h') in Hreason.
    assert (Hv': ValuesOf v' mt).
    { assert (Hlen: tlen x - PA.length mt = S (PA.length n)).
      { destruct Htrail as [Hlen _].
        rewrite Hlen, trail_lits_length, (pa_length_app ⟨mt; d⟩ n).
        cbn [PA.length]. lia. }
      unfold v'. rewrite Hlen, (unset_range_spec mt n d _ Htrail).
      now apply unassign_segment_spec. }
    assert (Hu: lookup v' u = None) by now rewrite Hv'.
    assert (Hh': DlitIn f h') by (unfold DlitIn, h'; rewrite reinsert_dlit; apply Hh).
    (* The reason clause keeps the heuristic h'. *)
    assert (Hhr: hr x' = h').
    { pose proof Hreason as Hreason'.
      destruct Hreason' as [[-> _] | (Hpush & _ & _)].
      - reflexivity.
      - unfold push_reason in Hpush. destruct (_ && _).
        + injection Hpush as <- _. reflexivity.
        + injection Hpush as <- _. reflexivity. }
    (* and the positions of the decisions ls *)
    assert (Hlims': lims x' = ls).
    { pose proof Hreason as Hreason'.
      destruct Hreason' as [[-> _] | (Hpush & _ & _)].
      - reflexivity.
      - apply push_reason_stacks in Hpush as [Hl _]. apply Hl. }
    destruct (fresh_split mt n d Hfresh) as [Hfresh' _].
    destruct (saved_q_split (cmap x) mt n d Hsavedq) as [Hok Hsavedq'].
    destruct (pop_reasons_spec (rps x) (PA.length mt) (nr x) Horder) as [Hpop_le Hpop].
    assert (Hext: forall (y: Lit), lookup (values mt) y = lookup v' y).
    { intros y. now rewrite lookup_values, Hv'. }
    (* The levels and reasons of mt, without the dropped reason clauses *)
    assert (Htrace_mt: TraceOk (cmap x) (rsn x) (lvl x) (rcl x) (rps x) (nr xj) mt).
    { apply (trace_pop (nr x)).
      - pose proof (trace_app ⟨mt; d⟩ n Htrace) as [_ Htrace']. assumption.
      - intros j Hj Hpos. now apply Hpop. }
    (* The context after the jump agrees with mt *)
    assert (Hprop_j: PropInv mt f xj).
    { split.
      - split.
        + assumption.
        + assumption.
        + apply (trail_of_prefix _ (tlen x) mt (PA.app ⟨; d⟩ n)).
          now rewrite PA.app_assoc.
        + assumption.
        + assumption.
        + reflexivity.
        + assumption.
      - simpl. lia.
      - apply watch_q_weaken. now apply (all_watch_q_ext (values mt)).
      - assumption.
      - assumption.
      - assumption. }
    assert (Hslots_j: forall (j: nat), j < nr xj -> tget (rps xj) j < tlen xj).
    { intros j Hj. simpl in Hj |- *. apply Hpop.
      - lia.
      - assumption. }
    (* The reason of u, and the reason clauses after storing it *)
    assert (Hafter: PropInv mt f x' /\
                    ReasonOk (cmap x') (rcl x') (rps x') (nr x') mt u r /\
                    vals x' = v' /\ SlotsOk f (assign x' u r) /\ cmap x' = cmap x /\
                    alls x' = alls x /\ nlits x' = nlits x /\ saved x' = st /\
                    shorts x' = shorts x /\ mrk x' = mk /\ nvars x' = nvars x /\
                    cur x' = c0).
    { assert (Hnone: x' = xj -> r = no_reason ->
                PropInv mt f x' /\ ReasonOk (cmap x') (rcl x') (rps x') (nr x') mt u r /\
                vals x' = v' /\ SlotsOk f (assign x' u r) /\ cmap x' = cmap x /\
                alls x' = alls x /\ nlits x' = nlits x /\ saved x' = st /\
                shorts x' = shorts x /\ mrk x' = mk /\ nvars x' = nvars x /\
                cur x' = c0).
      { intros -> ->. split.
        - assumption.
        - split.
          + constructor.
          + repeat split.
            * intros j Hj. apply Hent. simpl in Hj. lia.
            * intros j1 j2 Hj. apply Horder. simpl in Hj. lia.
            * intros j Hj. pose proof (Hslots_j j Hj) as Hj'. cbn [assign rps tlen].
              lia. }
      destruct Hreason as [[-> ->] | (Hpush & Hlt_ent & Hlt_false)].
      - now apply Hnone.
      - unfold push_reason in Hpush. destruct (_ && _).
        + injection Hpush as <- <-.
          assert (Htrace_push: TraceOk (cmap x) (rsn x) (lvl x)
                                 (tset (rcl xj) (nr xj) (u :: lt))
                                 (tset (rps xj) (nr xj) (tlen xj)) (S (nr xj)) mt).
          { now apply trace_push. }
          split.
          * apply prop_inv_reasons.
            -- assumption.
            -- assumption.
          * unfold xj, add_reason in *.
            cbn [vals cmap wls tr tlen qhead shorts alls nlits cur saved rsn lvl dl mrk
              lower phs nvars rcl rps nr rcap] in *.
            set (j0 := pop_reasons (rps x) (PA.length mt) (nr x)) in *. split.
            -- cbn [ReasonOk]. rewrite !tget_tset_same. split.
               ++ lia.
               ++ split.
                  ** reflexivity.
                  ** split.
                     --- now left.
                     --- intros y [<- | Hy] Hne.
                         +++ contradiction.
                         +++ now apply Hlt_false.
            -- repeat split.
               ++ intros j Hj. cbn [assign rcl nr] in Hj |- *. rewrite tget_tset.
                  destruct (Nat.eq_dec j0 j) as [<- | Hne].
                  ** assumption.
                  ** apply Hent. lia.
               ++ intros j1 j2 Hj. cbn [assign rps nr] in Hj |- *. rewrite !tget_tset.
                  destruct (Nat.eq_dec j0 j1) as [<- | Hne1].
                  ** lia.
                  ** destruct (Nat.eq_dec j0 j2) as [<- | Hne2].
                     --- apply Hslots_j. lia.
                     --- apply Horder. lia.
               ++ intros j Hj. cbn [assign rps nr tlen] in Hj |- *. rewrite tget_tset.
                  destruct (Nat.eq_dec j0 j) as [<- | Hne].
                  ** lia.
                  ** assert (Hj0: j < j0) by lia.
                     pose proof (Hslots_j j Hj0). lia.
        + injection Hpush as <- <-. now apply Hnone. }
    destruct Hafter as (Hprop' & Hreason' & Hv'' & Hslots' & Hcm & Hal & Hnl & Hsv &
      Hsh & Hmk' & Hnv & Hcur).
    split.
    - apply prop_inv_assign.
      + now apply prop_inv_lower.
      + cbn [set_lower vals]. now rewrite Hv''.
      + apply Hreason'.
    - simpl. now rewrite Hcm.
    - simpl. rewrite Hal, Hnl, Hcur, Hv''. apply (cursor_incl (values mt)).
      + intros l Hl. rewrite Hext. apply (incl_undef v' (set_value v' u)).
        * apply incl_set_value.
          -- apply incl_refl.
          -- assumption.
        * assumption.
      + assumption.
    - simpl. now rewrite Hal, Hnl, Hsv.
    - simpl. rewrite Hcm, Hsh. assumption.
    - simpl. rewrite Hcm, Hsh. assumption.
    - simpl. now rewrite Hmk'.
    - simpl. now rewrite Hnv.
    - apply (slots_grow f (assign x' u r)).
      + assumption.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + cbn [assign set_lower tlen]. lia.
    - cbn [assign set_lower hr]. rewrite Hhr. apply Hh'.
    - cbn [assign set_lower lims LimsOf]. rewrite Hlims'. assumption.
    - reflexivity.
  Qed.
End Jumps.

(* A decision with an empty queue keeps propagation consistent: the watches are fine
   before it, and the decision opens a new level. *)
Lemma prop_inv_decide: forall (m: PA) (f: CNF) (x: Ctx) (c: nat) (l: Lit),
  PropInv m f x -> qhead x = tlen x -> lookup (vals x) l = None ->
  PropInv ⟨m; l⟩ f (assign (open_level x c) l no_reason).
Proof.
  intros m f x c l Hinv Hq Hl.
  destruct (prop_inv_assign m f x l no_reason Hinv Hl I)
    as [_ Hq' Hwatch Hsaved Hlisted Hblocked].
  destruct Hinv
    as [[Hvals0 Hfresh0 Htrail0 Hsound0 Hnodup0 Hdl0 Htrace0] _ Hwatch0 Hsaved0 _ _].
  assert (Hundef: l_eval m l = None) by now rewrite <- Hvals0.
  split.
  - split.
    + intros y. simpl. now rewrite lookup_add, Hvals0.
    + now split.
    + destruct (trail_of_cons (tr x) (tlen x) m l Htrail0) as [Hlen Hnth]. split.
      * assumption.
      * assumption.
    + assumption.
    + assumption.
    + simpl. now rewrite Hdl0.
    + cbn [assign open_level cmap rsn lvl rcl rps nr dl TraceOk].
      rewrite !tget_tset_same. split.
      * now rewrite Hdl0.
      * apply trace_other.
        -- intros y Hy. now apply (undef_atom m l y).
        -- assumption.
  - assumption.
  - assumption.
  - simpl. split.
    + apply (all_watch_q_ext (vals x)).
      * intros y. now rewrite Hvals0, lookup_values.
      * rewrite Hq in Hwatch0. now apply watch_q_empty in Hwatch0.
    + assumption.
  - assumption.
  - assumption.
Qed.

(* Deciding an unassigned literal l0 of f with its phase, saving the cursor c, is a Decide
   step to a consistent context. *)
Lemma decide_lit_spec: forall (m: PA) (f: CNF) (x: Ctx) (c: nat) (l0: Lit),
  StepCore m f x ->
  qhead x = tlen x ->
  shorts x = [] ->
  NoEmpty x ->
  CursorAt f x c -> l0 ∈ f ->
  lookup (vals x) l0 = None ->
  let l := phase (phs x) l0 in
  state m f ==>[DPLL_BJ] state ⟨m; l⟩ f /\
  StepCore ⟨m; l⟩ f (assign (open_level x c) l no_reason).
Proof.
  intros m f x c l0
    [Hprop Hcomplete _ Hsaved _ _ Hmarks Hbound Hslots Hdlit Hlims Hlow] Hq
    Hshorts Hnonempty Hc Hl0 Hundef l.
  pose proof Hprop as [[Hvals _ _ _ _ _ _] _ _ _ _ _].
  apply (phase_undef _ (phs x)) in Hundef as Hl.
  assert (Hext: forall (y: Lit), lookup (vals x) y = lookup (values m) y).
  - intros y. now rewrite Hvals, lookup_values.
  - split.
    + apply (t_step Decide).
      * right. right. now left.
      * apply r_decide.
        -- now apply phase_in.
        -- unfold Undef. now rewrite <- Hvals.
    + split.
      * apply prop_inv_decide.
        -- assumption.
        -- assumption.
        -- assumption.
      * assumption.
      * apply (cursor_incl (vals x)).
        -- intros y Hy.
           apply (incl_undef (vals x) (set_value (vals x) l)).
           ++ apply incl_set_value.
              ** apply incl_refl.
              ** assumption.
           ++ assumption.
        -- assumption.
      * simpl. split.
        -- apply (cursor_incl (vals x)).
           ++ intros y Hy. now rewrite Hext.
           ++ assumption.
        -- assumption.
      * intros i Hi. now apply Hnonempty in Hi.
      * simpl. rewrite Hshorts. intros i ls [].
      * assumption.
      * assumption.
      * apply (slots_grow f x).
        -- assumption.
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- simpl. lia.
      * assumption.
      * (* the decision is at the end of the trail *)
        cbn [assign open_level lims LimsOf]. split.
        -- destruct Hprop as [[_ _ [Hlen _] _ _ _ _] _ _ _ _ _].
           now rewrite Hlen, trail_lits_length.
        -- assumption.
      * assumption.
Qed.

(* Changing the heuristic, but not its literals to decide on, keeps the context
   consistent: nothing else depends on it. *)
Lemma step_core_heur: forall (m: PA) (f: CNF) (x: Ctx) (h: Heur),
  StepCore m f x -> dlit h = dlit (hr x) -> StepCore m f (x <| hr := h |>).
Proof.
  intros m f x h
    [Hprop Hcomplete Hcursor Hsaved Hempty Hshorts Hmarks Hbound Hslots Hdlit Hlims Hlow]
    Hh.
  split.
  - apply (prop_inv_ext m f x).
    + assumption.
    + reflexivity.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - apply (slots_grow f x).
    + assumption.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + cbn [set_hr tlen]. lia.
  - unfold DlitIn. cbn [set_hr hr]. rewrite Hh. assumption.
  - assumption.
  - assumption.
Qed.

(* Deciding the unassigned literal at the cursor c, with its phase, is a Decide step to a
   consistent context (a case of decide_lit_spec). *)
Lemma decide_spec: forall (m: PA) (f: CNF) (x: Ctx) (c: nat),
  StepCore m f x ->
  qhead x = tlen x ->
  shorts x = [] ->
  NoEmpty x ->
  CursorAt f x c ->
  c < nlits x ->
  lookup (vals x) (tget (alls x) c) = None ->
  let l := phase (phs x) (tget (alls x) c) in
  state m f ==>[DPLL_BJ] state ⟨m; l⟩ f /\
  StepCore ⟨m; l⟩ f (assign (open_level x c) l no_reason).
Proof.
  intros m f x c Hcore Hq Hshorts Hnonempty Hc Hlt Hundef.
  pose proof Hc as [_ [Hin _]].
  apply decide_lit_spec.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - now apply Hin.
  - assumption.
Qed.

(* No clause of f is false in m. *)
Abbreviation NoFalse m f := (forall (cl: Clause), cl ∈ f -> c_eval m cl <> Some false).

(* Every literal of f is assigned in m. *)
Abbreviation AllAssigned m f := (forall (l: Lit), l ∈ f -> ~ Undef m l).

(* With an empty queue, no empty clause and the cursor at the end, no clause is false and
   every literal of f is assigned. *)
Lemma final_state: forall (m: PA) (f: CNF) (x: Ctx) (c: nat),
  StepCore m f x ->
  qhead x = tlen x ->
  NoEmpty x ->
  CursorAt f x c ->
  ~ c < nlits x ->
  NoFalse m f /\ AllAssigned m f.
Proof.
  intros m f x c [[[Hvals _ _ _ _] _ Hwatch _ _ _] Hcomplete _ _ _ _ _ _] Hq Hnonempty
    [_ [_ Hcover]] Hge.
  split.
  (* A false clause would have a false first watch, but the queue is empty and no literal
     of it is true *)
  - intros cl Hcl_in_f Hcl. destruct (Hcomplete cl Hcl_in_f) as [i [ls [Hi Hiff]]].
    assert (Hall: forall (y: Lit), In y ls -> lookup (vals x) y = Some false).
    + intros y Hy. rewrite Hvals. apply c_eval_false_iff with (l := y) in Hcl.
      * assumption.
      * now apply Hiff.
    + destruct ls as [|w ls].
      * now apply Hnonempty in Hi.
      * assert (Hw: In w (firstn 2 (w :: ls))).
        -- now left.
        -- assert (Hwf: lookup (vals x) w = Some false).
           ++ apply Hall. now left.
           ++ destruct (Hwatch i (w :: ls) Hi w Hw Hwf) as [[j [Hj _]]|[y [Hy Ht]]].
              ** lia.
              ** rewrite (Hall y Hy) in Ht. discriminate.
  - intros l Hl_in_f Hundef. unfold Undef in Hundef. rewrite <- Hvals in Hundef.
    destruct (Hcover l Hl_in_f Hundef) as [j [Hj _]]. lia.
Qed.

Section Derivations.
  (* A step followed by a derivation is a strict derivation. *)
  Lemma step_then_derivation: forall (rs: list Rule) (s1 s2 s3: State),
    s1 ==>[rs] s2 -> clos_refl_trans_1n _ (Trans rs) s2 s3 -> s1 ==>+[rs] s3.
  Proof.
    intros rs s1 s2 s3 H12 H23. revert s1 H12.
    induction H23 as [|s2 s4 s3 H24 _ IH]; intros s1 H12.
    - now apply Relation_Operators.t_step.
    - apply Relation_Operators.t_trans with s2.
      + now apply Relation_Operators.t_step.
      + now apply IH.
  Qed.

  (* A derivation between different states is strict. *)
  Lemma derivation_strict: forall (rs: list Rule) (s s': State),
    s ==>*[rs] s' -> s <> s' -> s ==>+[rs] s'.
  Proof.
    intros rs s s' H Hneq. apply clos_rt_rt1n in H. destruct H as [|s1 s2 H12 H23].
    - contradiction.
    - now apply (step_then_derivation rs s s1 s2).
  Qed.

  (* A trail extended by propagations only, and as long, is the same trail. *)
  Lemma extends_same_length: forall (m m': PA),
    Extends m m' -> PA.length m' = PA.length m -> m' = m.
  Proof.
    intros m m' [n [-> _]] Hlen.
    rewrite <- !trail_lits_length, trail_lits_app, length_app in Hlen.
    destruct n as [|n l|n l].
    - reflexivity.
    - simpl in Hlen. rewrite length_app in Hlen. simpl in Hlen. lia.
    - simpl in Hlen. rewrite length_app in Hlen. simpl in Hlen. lia.
  Qed.

  (* A strict derivation from a well-formed, entailed state to a state the context x'
     agrees with gives the invariant. *)
  Lemma step_inv_after: forall (m m': PA) (f: CNF) (x': Ctx),
    WellFormed (state m f) -> Entails f m -> state m f ==>+[DPLL_BJ] state m' f ->
    StepCore m' f x' -> StepInv (state m' f) x'.
  Proof.
    intros m m' f x' Hwf Hentails Hplus Hcore. apply clos_t_clos_rt in Hplus. split.
    - assumption.
    - split.
      + now apply (derivation_well_formed DPLL_BJ m m' f f).
      + now apply (derivation_entails DPLL_BJ m m' f f).
  Qed.
End Derivations.

(* A state without a false clause and without an unassigned literal of f is final. *)
Lemma final_basic_of: forall (m: PA) (f: CNF),
  NoFalse m f -> AllAssigned m f -> Final Basic (state m f).
Proof.
  intros m f Hno_conflict Hno_decision [s' Htrans].
  inversion Htrans as [r ? ? s'' Hr Hstep]; subst.
  destruct Hr as [<-|[<-|[<-|[]]]].
  - inversion Hstep as [? ? c Hc_in_f Hc Hno_dec]; subst. now apply (Hno_conflict c).
  - inversion Hstep as [? ? l Hl_in_f Hundef]; subst.
    destruct Hl_in_f as [Hl_in_f|Hnegl_in_f].
    + now apply (Hno_decision l).
    + apply (Hno_decision (¬l)).
      * assumption.
      * now apply l_eval_neg_none_iff in Hundef.
  - inversion Hstep as [m_split n_split ? c l_split Hc_in_f Hc Hno_dec]; subst.
    now apply (Hno_conflict c).
Qed.

(* The initial context: the clauses indexed and watched, and the literals to decide on. *)
Section Initial.
  (* A watcher e is appended to the watch list of z. *)
  Definition add_watcher (wl: WatchLists) (z: Lit) (e: Watcher): WatchLists :=
    tset wl (lit_key z) (watching wl z ++ [e]).

  (* Appending keeps the watchers of every list. *)
  Lemma add_watcher_keep: forall (wl: WatchLists) (z y: Lit) (e e': Watcher),
    In e' (watching wl y) -> In e' (watching (add_watcher wl z e) y).
  Proof. intros wl z y e e' He'. now apply watching_push. Qed.

  (* The appended watcher is in the list of z. *)
  Lemma add_watcher_new: forall (wl: WatchLists) (z: Lit) (e: Watcher),
    In e (watching (add_watcher wl z e) z).
  Proof. intros wl z e. apply watching_push_new. Qed.

  (* The watchers in the list of y after appending e to that of z. *)
  Lemma add_watcher_in: forall (wl: WatchLists) (z y: Lit) (e e': Watcher),
    In e' (watching (add_watcher wl z e) y) -> In e' (watching wl y) \/ e' = e.
  Proof.
    intros wl z y e e' He'. unfold add_watcher in He'. rewrite watching_set in He'.
    destruct (Lit.eq_dec z y) as [<-|_].
    - apply in_app_iff in He' as [He'|[<-|[]]].
      + now left.
      + now right.
    - now left.
  Qed.

  (* Clause k with literals ls starts being watched: its first two literals watch it, each
     with the other as blocker, and a unit clause is watched by its literal. *)
  Definition watch_first (wl: WatchLists) (k: nat) (ls: list Lit): WatchLists :=
  match ls with
  | a :: b :: _ => add_watcher (add_watcher wl a (k, b)) b (k, a)
  | [a]         => add_watcher wl a (k, a)
  | []          => wl
  end.

  (* Watching a clause keeps the old watchers. *)
  Lemma watch_first_keep: forall (wl: WatchLists) (k: nat) (ls: list Lit) (y: Lit)
    (e: Watcher),
    In e (watching wl y) -> In e (watching (watch_first wl k ls) y).
  Proof.
    intros wl k [|a [|b ls]] y e He; simpl.
    - assumption.
    - now apply add_watcher_keep.
    - now apply add_watcher_keep, add_watcher_keep.
  Qed.

  (* The first two literals of clause k watch it. *)
  Lemma watch_first_listed: forall (wl: WatchLists) (k: nat) (ls: list Lit) (w: Lit),
    In w (firstn 2 ls) -> HasWatcher (watching (watch_first wl k ls) w) k.
  Proof.
    intros wl k [|a [|b ls]] w Hw; simpl in Hw |- *.
    - destruct Hw.
    - destruct Hw as [<-|[]]. exists a. apply add_watcher_new.
    - destruct Hw as [<-|[<-|[]]].
      + exists b. apply add_watcher_keep, add_watcher_new.
      + exists a. apply add_watcher_new.
  Qed.

  (* The new watchers are of clause k, with blockers from ls. *)
  Lemma watch_first_in: forall (wl: WatchLists) (k: nat) (ls: list Lit) (y: Lit) (j: nat)
    (c: Lit),
    In (j, c) (watching (watch_first wl k ls) y) -> In (j, c) (watching wl y) \/
      (j = k /\ In c ls).
  Proof.
    intros wl k [|a [|b ls]] y j c He; simpl in He.
    - now left.
    - apply add_watcher_in in He as [He|Heq].
      + now left.
      + injection Heq as -> ->. right. split.
        * reflexivity.
        * now left.
    - apply add_watcher_in in He as [He|Heq].
      + apply add_watcher_in in He as [He|Heq].
        * now left.
        * injection Heq as -> ->. right. split.
          -- reflexivity.
          -- right. now left.
      + injection Heq as -> ->. right. split.
        * reflexivity.
        * now left.
  Qed.

  (* Index the clauses lss from k on: store them, watch their first literals, and collect
     the short ones. *)
  Fixpoint index (k: nat) (lss: list (list Lit)) (cm: ClauseMap) (wl: WatchLists)
    (sh: list nat):
    ClauseMap * WatchLists * list nat :=
  match lss with
  | []         => (cm, wl, sh)
  | ls :: lss' =>
    index (S k) lss' (tset cm k (Some ls)) (watch_first wl k ls)
      (if length ls <=? 1 then k :: sh else sh)
  end.

  (* Indexing the clauses lss from k on, into tables used only below k, keeps the watches
     and the short clauses fine and adds exactly the clauses lss. *)
  Lemma index_spec: forall (lss: list (list Lit)) (k: nat) (cm cm': ClauseMap)
    (wl wl': WatchLists) (sh sh': list nat),
    (forall (i: nat) (ls: list Lit), tget cm i = Some ls -> i < k) ->
    (forall (l: Lit) (i: nat) (b: Lit), In (i, b) (watching wl l) -> i < k) ->
    (forall (i: nat), In i sh -> i < k) ->
    Listed cm wl -> Blocked cm wl -> EmptyInShorts cm sh -> ShortsShort cm sh ->
    index k lss cm wl sh = (cm', wl', sh') ->
    Listed cm' wl' /\ Blocked cm' wl' /\ EmptyInShorts cm' sh' /\ ShortsShort cm' sh' /\
    (forall (i: nat) (ls: list Lit),
       tget cm' i = Some ls -> tget cm i = Some ls \/ In ls lss) /\
    (forall (ls: list Lit), In ls lss -> exists (i: nat), tget cm' i = Some ls) /\
    (forall (i: nat) (ls: list Lit), tget cm i = Some ls -> tget cm' i = Some ls).
  Proof.
    intros lss.
    induction lss as
      [|ls lss IH]; intros k cm cm' wl wl' sh sh' Hfresh Hwfresh Hbelow Hlisted Hblocked
      Hempty Hshort Hindex; simpl in Hindex.
    - injection Hindex as <- <- <-. split.
      + assumption.
      + split.
        * assumption.
        * split.
          -- assumption.
          -- split.
             ++ assumption.
             ++ split.
                ** intros i' ls' Hi. now left.
                ** split.
                   --- intros ls' [].
                   --- now intros i' ls' Hi.
    - assert (Hk: tget cm k = None).
      + destruct (tget cm k) as [ls'|] eqn:Hk.
        * apply Hfresh in Hk. lia.
        * reflexivity.
      + destruct (IH (S k) (tset cm k (Some ls)) cm' (watch_first wl k ls) wl'
          (if length ls <=? 1 then k :: sh else sh) sh') as
            (Hl & Hb & He & Hsh & Hsound & Hcomplete & Hkeep).
        * intros i ls' Hi. rewrite tget_tset in Hi. destruct (Nat.eq_dec k i) as [<-|Hne].
          -- lia.
          -- apply Hfresh in Hi. lia.
        * intros l i b Hin. apply watch_first_in in Hin as [Hin|[-> _]].
          -- apply Hwfresh in Hin. lia.
          -- lia.
        * intros i Hin. destruct (length ls <=? 1).
          -- destruct Hin as [<-|Hin].
             ++ lia.
             ++ apply Hbelow in Hin. lia.
          -- apply Hbelow in Hin. lia.
        * intros i ls' z Hi Hz. rewrite tget_tset in Hi.
          destruct (Nat.eq_dec k i) as [<-|Hne].
          -- injection Hi as <-. now apply watch_first_listed.
          -- destruct (Hlisted i ls' z Hi Hz) as [b Hin]. exists b.
             now apply watch_first_keep.
        * intros l i b ls' Hin Hi. rewrite tget_tset in Hi.
          apply watch_first_in in Hin as [Hin|[-> Hb]].
          -- destruct (Nat.eq_dec k i) as [<-|Hne].
             ++ apply Hwfresh in Hin. lia.
             ++ now apply (Hblocked l i b).
          -- destruct (Nat.eq_dec k k) as [_|]; [|contradiction]. injection Hi as <-.
             assumption.
        * intros i Hi. rewrite tget_tset in Hi. destruct (Nat.eq_dec k i) as [<-|Hne].
          -- injection Hi as ->. simpl. now left.
          -- destruct (length ls <=? 1).
             ++ right. now apply Hempty.
             ++ now apply Hempty.
        * intros i ls' Hin Hi. rewrite tget_tset in Hi. destruct (Nat.eq_dec k i) as [<-|Hne].
          -- injection Hi as <-. destruct (length ls <=? 1) eqn:Hlen.
             ++ now apply Nat.leb_le in Hlen.
             ++ apply Hbelow in Hin. lia.
          -- destruct (length ls <=? 1).
             ++ destruct Hin as [->|Hin].
                ** contradiction.
                ** now apply (Hshort i).
             ++ now apply (Hshort i).
        * assumption.
        * split.
          -- assumption.
          -- split.
             ++ assumption.
             ++ split.
                ** assumption.
                ** split.
                   --- assumption.
                   --- split.
                       +++ intros i ls' Hi. destruct (Hsound i ls' Hi) as [Hi'|Hin].
                           *** rewrite tget_tset in Hi'. destruct (Nat.eq_dec k i) as [<-|Hne].
                               ---- injection Hi' as ->. right. now left.
                               ---- now left.
                           *** right. now right.
                       +++ split.
                           *** intros ls' [<-|Hin].
                               ---- exists k. apply Hkeep. apply tget_tset_same.
                               ---- now apply Hcomplete.
                           *** intros i ls' Hi. apply Hkeep. rewrite tget_tset_other.
                               ---- assumption.
                               ---- intros ->. congruence.
  Qed.

  (* Fill a table with the literals ls from position k on. *)
  Fixpoint fill (t: Table Lit) (k: nat) (ls: list Lit): Table Lit :=
  match ls with
  | []       => t
  | l :: ls' => fill (tset t k l) (S k) ls'
  end.

  (* Filling from k on keeps the positions below k. *)
  Lemma fill_below: forall (ls: list Lit) (t: Table Lit) (k j: nat),
    j < k -> tget (fill t k ls) j = tget t j.
  Proof.
    intros ls. induction ls as [|l ls IH]; intros t k j Hj; simpl.
    - reflexivity.
    - rewrite IH.
      + apply tget_tset_other. lia.
      + lia.
  Qed.

  (* Position k + j holds the literal j of ls. *)
  Lemma fill_spec: forall (ls: list Lit) (t: Table Lit) (k j: nat),
    j < length ls -> tget (fill t k ls) (k + j) = nth j ls (Pos 0).
  Proof.
    intros ls. induction ls as [|l ls IH]; intros t k j Hj; simpl in Hj |- *.
    - lia.
    - destruct j as [|j].
      + rewrite Nat.add_0_r, fill_below.
        * apply tget_tset_same.
        * lia.
      + replace (k + S j) with (S k + j) by lia. apply IH. lia.
  Qed.

  (* The initial context for the clauses lss and the literals ls to decide on, with nv as
     the bound on the trail: no values, an empty trail, the clauses indexed, and the
     heuristic with the atoms of ls. *)
  Definition initial_of (lss: list (list Lit)) (ls: list Lit) (nv rc: nat): Ctx :=
  match index 0 lss (tmake None) (tmake []) [] with
  | (cm, wl, sh) =>
    mkCtx (tmake None) cm wl (tmake (Pos 0)) 0 0 sh (fill (tmake (Pos 0)) 0 ls)
      (length ls) 0 [] [] (tmake no_reason) (tmake 0) 0 (tmake false) [] (tmake None) nv
      (tmake []) (tmake 0) 0 rc (init_heur (fill (tmake (Pos 0)) 0 ls) nv (length ls))
  end.

  (* The initial context agrees with the initial state of f if lss lists the clauses of f,
     without duplicate literals, and ls the literals of f. *)
  Lemma initial_of_inv: forall (f: CNF) (lss: list (list Lit)) (ls: list Lit)
    (nv rc: nat),
    (forall (cs: list Lit), In cs lss -> NoDup cs /\ ClauseOf f cs) ->
    (forall (c: Clause), c ∈ f ->
       exists (cs: list Lit), In cs lss /\ forall (l: Lit), In l cs <-> l ∈ c) ->
    (forall (l: Lit), In l ls <-> l ∈ f) ->
    S (max_atom_f f) <= nv ->
    StepInv (state ⟨⟩ f) (initial_of lss ls nv rc).
  Proof.
    intros f lss ls nv rc Hlss Hcovered Hls Hnv. unfold initial_of.
    destruct (index 0 lss (tmake None) (tmake []) []) as [[cm wl] sh] eqn:Hindex.
    destruct (index_spec lss 0 (tmake None) cm (tmake []) wl [] sh)
      as (Hlisted & Hblocked & Hempty & Hshort & Hsound & Hcomplete & _).
    - intros i cs Hi. now rewrite tget_tmake in Hi.
    - intros l i b Hin. unfold watching in Hin. now rewrite tget_tmake in Hin.
    - intros i [].
    - intros i cs z Hi. now rewrite tget_tmake in Hi.
    - intros l i b cs Hin. unfold watching in Hin. now rewrite tget_tmake in Hin.
    - intros i Hi. now rewrite tget_tmake in Hi.
    - intros i cs [].
    - assumption.
    - split.
      + split.
        * split.
          -- split.
             ++ intros l. simpl. unfold lookup. now rewrite tget_tmake.
             ++ easy.
             ++ split.
                ** reflexivity.
                ** intros j Hj. simpl in Hj. lia.
             ++ intros i cs Hi. destruct (Hsound i cs Hi) as [Hi'|Hin].
                ** now rewrite tget_tmake in Hi'.
                ** now apply Hlss.
             ++ intros i cs Hi. destruct (Hsound i cs Hi) as [Hi'|Hin].
                ** now rewrite tget_tmake in Hi'.
                ** now apply Hlss.
             ++ reflexivity.
             ++ easy.
          -- simpl. lia.
          -- intros i cs _ w _ Hf. simpl in Hf. unfold lookup in Hf.
             now rewrite tget_tmake in Hf.
          -- easy.
          -- assumption.
          -- assumption.
        * intros c Hc_in_f. destruct (Hcovered c Hc_in_f) as [cs [Hin Hiff]].
          destruct (Hcomplete cs Hin) as [i Hi].
          now exists i, cs.
        * split.
          -- simpl. lia.
          -- split.
             ++ intros j Hj. simpl. rewrite <- (Nat.add_0_l j), fill_spec.
                ** apply Hls, nth_In. assumption.
                ** assumption.
             ++ intros l Hl_in_f _.
                apply Hls, In_nth with (d := Pos 0) in Hl_in_f as [j [Hj Hl]].
                exists j. split.
                ** cbn [cur nlits]. split.
                   --- apply Nat.le_0_l.
                   --- assumption.
                ** simpl. rewrite <- (Nat.add_0_l j), fill_spec.
                   --- assumption.
                   --- assumption.
        * reflexivity.
        * assumption.
        * assumption.
        * intros y. simpl. apply tget_tmake.
        * simpl. lia.
        * split.
          -- intros j Hj. simpl in Hj. lia.
          -- intros j1 j2 Hj. simpl in Hj. lia.
          -- intros j Hj. simpl in Hj. lia.
        * (* the literals to decide on of the heuristic are literals of ls *)
          intros a l Hl. cbn [hr] in Hl.
          apply (init_heur_dlit (fun (l': Lit) => l' ∈ f) (fill (tmake (Pos 0)) 0 ls) nv
                   (length ls)) with a.
          -- intros j Hj. rewrite <- (Nat.add_0_l j), fill_spec.
             ++ apply Hls, nth_In. assumption.
             ++ assumption.
          -- assumption.
        * (* no decisions yet *)
          reflexivity.
        * (* no analysis in progress *)
          reflexivity.
      + split.
        * apply initial_well_formed.
        * apply e_nil.
  Qed.

End Initial.

(* An unassigned literal has an atom that is not on the trail. *)
Lemma undef_not_atom: forall (m: PA) (l: Lit),
  l_eval m l = None -> ~ In (extract l) (atoms m).
Proof.
  intros m l Hundef Hin. apply PA.Lemmas.in_atoms in Hin as [y [Hy Hext]].
  apply Neg.extract_eq in Hext.
  assert (Hdef: exists (b: bool), l_eval m l = Some b).
  - apply l_eval_some_iff. destruct Hext as [-> | ->].
    + now left.
    + now right.
  - destruct Hdef as [b Hb]. congruence.
Qed.

(* The atoms of a trail that only assigns unassigned literals are distinct. *)
Lemma fresh_nodup: forall (m: PA), Fresh m -> NoDup (atoms m).
Proof.
  intros m. induction m as [|m IH l|m IH l]; simpl; intros Hfresh.
  - constructor.
  - destruct Hfresh as [Hfresh Hundef]. constructor.
    + now apply undef_not_atom.
    + now apply IH.
  - destruct Hfresh as [Hfresh Hundef]. constructor.
    + now apply undef_not_atom.
    + now apply IH.
Qed.

(* With an unassigned literal, a trail over atoms below N is shorter than N. *)
Lemma trail_shorter: forall (m: PA) (l: Lit) (N: nat),
  Fresh m -> l_eval m l = None -> extract l < N ->
  (forall (y: Lit), y ∈ m -> extract y < N) -> S (PA.length m) <= N.
Proof.
  intros m l N Hfresh Hundef Hl Hatoms.
  rewrite <- PA.Lemmas.length_atoms. rewrite <- (length_seq N 0).
  apply (NoDup_incl_length (l := extract l :: atoms m)).
  - constructor.
    + now apply undef_not_atom.
    + now apply fresh_nodup.
  - intros p [<- | Hp].
    + apply in_seq. lia.
    + apply PA.Lemmas.in_atoms in Hp as [y [Hy <-]]. apply in_seq.
      apply Hatoms in Hy. lia.
Qed.

(* There are at most as many decisions as literals on the trail. *)
Lemma lims_length: forall (lims: list nat) (m: PA),
  LimsOf lims m -> length lims <= PA.length m.
Proof.
  intros lims m. revert lims.
  induction m as [|m IH l|m IH l]; intros lims Hlims; simpl in Hlims |- *.
  - now subst lims.
  - apply IH in Hlims. lia.
  - destruct lims as [|j lims].
    + contradiction.
    + destruct Hlims as [-> Hlims]. apply IH in Hlims. simpl. lia.
Qed.

(* Between steps, the trail and the values agree with m (Core). *)
Lemma core_of_step: forall (m: PA) (f: CNF) (x: Ctx), StepCore m f x -> Core m f x.
Proof.
  intros m f x Hcore. apply pi_core. apply sc_prop. assumption.
Qed.
Arguments core_of_step {m f x}.

(* The context after checking the short clauses of x. *)
Abbreviation after_shorts x := (fst (check_shorts (shorts x) x)).

(* The context after propagating in x1. *)
Abbreviation after_prop x1 := (fst (propagate (S (nvars x1)) (x1 <| shorts := [] |>))).

(* After check_shorts, the context agrees with its trail, which extends m and is
   well-formed; without a conflict, no clause is empty. *)
Lemma check_shorts_trail: forall (m: PA) (f: CNF) (x: Ctx),
  StepInv (state m f) x ->
  StepCore (trail (after_shorts x)) f (after_shorts x) /\
  Extends m (trail (after_shorts x)) /\
  WellFormed (state (trail (after_shorts x)) f) /\
  (snd (check_shorts (shorts x) x) = None -> NoEmpty (after_shorts x)).
Proof.
  intros m f x [Hcore [Hwf _]].
  destruct (check_shorts (shorts x) x) as [x1 r1] eqn:Hcheck. cbn [fst snd].
  destruct (check_shorts_step m f x x1 r1 Hcore Hcheck)
    as (m1 & Hder1 & Hext1 & Hcore1 & Hnone1 & _).
  rewrite <- (step_core_trail Hcore1). split.
  - assumption.
  - split.
    + assumption.
    + split.
      * now apply (derivation_well_formed DPLL_BJ m m1 f f).
      * assumption.
Qed.

(* After propagate, the context agrees with its trail, which extends m1. *)
Lemma propagate_trail: forall (m1: PA) (f: CNF) (x1: Ctx),
  StepCore m1 f x1 -> WellFormed (state m1 f) -> NoEmpty x1 ->
  StepCore (trail (after_prop x1)) f (after_prop x1) /\
  Extends m1 (trail (after_prop x1)).
Proof.
  intros m1 f x1 Hcore1 Hwf1 Hnonempty.
  destruct (propagate (S (nvars x1)) (x1 <| shorts := [] |>))
    as [x2 r2] eqn:Hprop. cbn [fst].
  destruct (propagate_step m1 f x1 x2 r2 Hcore1 Hwf1 Hnonempty Hprop)
    as (m2 & _ & Hext2 & Hcore2 & _).
  rewrite <- (step_core_trail Hcore2). split.
  - assumption.
  - assumption.
Qed.

(* The positions of the decisions are on the trail. *)
Lemma lims_on_trail: forall (m: PA) (f: CNF) (x: Ctx),
  StepCore m f x -> LimsBelow x /\ length (lims x) <= tlen x.
Proof.
  intros m f x Hcore.
  destruct (core_trail (core_of_step Hcore)) as [Hlen _].
  rewrite trail_lits_length in Hlen. split.
  - intros j Hj. rewrite Hlen. now apply (lims_lt (lims x) m j (sc_lims Hcore)).
  - rewrite Hlen. now apply lims_length, (sc_lims Hcore).
Qed.
Arguments lims_on_trail {m f x}.

(* With an unassigned literal of an atom below N, a trail of atoms below N is shorter than
   N. *)
Lemma trail_room: forall (m: PA) (f: CNF) (x: Ctx) (N: nat) (l: Lit),
  StepCore m f x ->
  (forall (j: nat), j < tlen x -> extract (tget (tr x) j) < N) ->
  lookup (vals x) l = None -> extract l < N -> tlen x < N.
Proof.
  intros m f x N l Hcore Hatoms Hl HlN.
  destruct (core_of_step Hcore) as [Hvals Hfresh [Hlen Htr] _ _].
  rewrite trail_lits_length in Hlen. rewrite Hlen. apply (trail_shorter m l N Hfresh).
  - now rewrite <- Hvals.
  - assumption.
  - intros y Hy. apply trail_lits_in in Hy.
    apply In_nth with (d := Pos 0) in Hy as [j [Hj <-]].
    rewrite trail_lits_length in Hj. rewrite <- Htr by lia. apply Hatoms. lia.
Qed.
Arguments trail_room {m f x}.

(* A phase only chooses the sign of a literal. *)
Lemma extract_phase: forall (ph: Values) (l: Lit), extract (phase ph l) = extract l.
Proof.
  intros ph l. destruct (phase_cases ph l) as [-> | ->].
  - reflexivity.
  - now destruct l.
Qed.

(* The literal the heuristic picks is unassigned and of an atom below nvars x. *)
Lemma pick_unassigned: forall (pm: PA) (f: CNF) (x: Ctx) (fuel: nat) (h: Heur) (l0: Lit),
  StepCore pm f x -> pick (vals x) (hr x) fuel = (h, Some l0) ->
  lookup (vals x) l0 = None /\ extract l0 < nvars x.
Proof.
  intros pm f x fuel h l0 Hcore Hpick.
  destruct (pick_some Hpick) as [Hundef [a Ha]].
  pose proof (sc_dlit Hcore a l0 Ha) as Hl0.
  pose proof (max_atom_f_le f l0 (extract l0) Hl0 eq_refl) as Hmax.
  pose proof (sc_bound Hcore) as Hbound.
  split.
  - assumption.
  - lia.
Qed.

(* Unsetting the range [j, q) is unsetting position q - 1 first, then [j, q - 1). *)
Lemma unset_range_last: forall (v: Values) (tr: Table Lit) (j q: nat), j < q ->
  unset_range (unset_value v (tget tr (q - 1))) tr j (q - 1 - j)
  = unset_range v tr j (q - j).
Proof.
  intros v tr j q Hjq. replace (q - j) with (S (q - 1 - j)) by lia. simpl.
  now replace (j + (q - 1 - j)) with (q - 1) by lia.
Qed.
