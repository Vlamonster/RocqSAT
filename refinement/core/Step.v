From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Relations.
From Stdlib Require SetoidList.
From Stdlib Require Import Permutation.
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
From RocqSAT.refinement Require Import Propagate.

(* What the solver steps of SolverStep.v and AnalysisStep.v share, on the context of Propagate.v: the cursor of
   decisions, the invariant between steps (StepCore, StepInv), the checks of the short clauses and propagation
   (front_shorts, front_prop), deciding (decide_spec), jumping back (jump, jump_core), the final states
   (final_state), and the initial context for any clause lists (initial_of, initial_of_inv). *)

Section Cursor.
  (* The literals alls[c..n) are the ones to decide on: all literals of the table are literals of f, and every
     unassigned literal of f is among them. *)
  Definition CursorT (v: Values) (f: CNF) (alls: Table Lit) (n c: nat): Prop :=
    c <= n /\ (forall (j: nat), j < n -> tget alls j ∈ f) /\
    (forall (l: Lit), l ∈ f -> lookup v l = None -> exists (j: nat), c <= j < n /\ tget alls j = l).

  (* The first position from c on whose literal is unassigned, or n; fuel n - c suffices. *)
  Fixpoint skip_from (v: Values) (alls: Table Lit) (n fuel c: nat): nat :=
  match fuel with
  | 0       => c
  | S fuel' => if (c <? n) && negb (lookup_undef v (tget alls c)) then skip_from v alls n fuel' (S c) else c
  end.

  Lemma skip_from_spec: forall (v: Values) (f: CNF) (alls: Table Lit) (n fuel c: nat),
    n - c <= fuel ->
    CursorT v f alls n c ->
    CursorT v f alls n (skip_from v alls n fuel c) /\
    (skip_from v alls n fuel c < n -> lookup v (tget alls (skip_from v alls n fuel c)) = None).
  Proof.
    intros v f alls n fuel. induction fuel as [|fuel IH]; intros c Hfuel [Hc [Hin Hcomplete]]; simpl.
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
                ** exfalso. unfold lookup_undef in Hdef. rewrite Hjl, Hl in Hdef. discriminate.
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
    (forall (l: Lit), lookup v' l = None -> lookup v l = None) -> CursorT v f alls n c -> CursorT v' f alls n c.
  Proof.
    intros v v' f alls n c Hincl [Hc [Hin Hcomplete]]. split.
    - assumption.
    - split.
      + assumption.
      + intros l Hl_in_f Hl. apply Hcomplete.
        * assumption.
        * now apply Hincl.
  Qed.

  Lemma incl_undef: forall (v v': Values) (l: Lit), Incl v v' -> lookup v' l = None -> lookup v l = None.
  Proof.
    intros v v' l Hincl Hl. destruct (lookup v l) as [b|] eqn:Hb.
    - apply Hincl in Hb. congruence.
    - reflexivity.
  Qed.
End Cursor.

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

(* The number of decisions on m. *)
Fixpoint decisions (m: PA): nat :=
match m with
| ⟨⟩     => 0
| ⟨m, _⟩ => decisions m
| ⟨m; _⟩ => S (decisions m)
end.

(* The number of literals after the last decision of m. *)
Fixpoint level_length (m: PA): nat :=
match m with
| ⟨⟩     => 0
| ⟨m, _⟩ => S (level_length m)
| ⟨m; _⟩ => 0
end.

(* The context without short clauses to check. *)
Definition clear_shorts (x: Ctx): Ctx :=
mkCtx (vals x) (cmap x) (wls x) (tr x) (tlen x) (qhead x) [] (alls x) (nlits x) (cur x)
  (saved x) (rsn x) (lvl x) (dl x) (mrk x) (phs x) (nvars x).

(* The context with cursor c. *)
Definition with_cursor (x: Ctx) (c: nat): Ctx :=
mkCtx (vals x) (cmap x) (wls x) (tr x) (tlen x) (qhead x) (shorts x) (alls x) (nlits x) c
  (saved x) (rsn x) (lvl x) (dl x) (mrk x) (phs x) (nvars x).

(* The context before deciding at cursor c: c is saved, and the decision level goes up. *)
Definition open_level (x: Ctx) (c: nat): Ctx :=
mkCtx (vals x) (cmap x) (wls x) (tr x) (tlen x) (qhead x) (shorts x) (alls x) (nlits x) c
  (c :: saved x) (rsn x) (lvl x) (S (dl x)) (mrk x) (phs x) (nvars x).

(* The context after jumping back to a trail of length len with values v, cursor c, saved cursors st, decision
   level d and marks mk; the watches are kept and the queue is empty. *)
Definition jump (x: Ctx) (v: Values) (len c: nat) (st: list nat) (d: nat) (mk: Table bool): Ctx :=
mkCtx v (cmap x) (wls x) (tr x) len len (shorts x) (alls x) (nlits x) c st (rsn x) (lvl x)
  d mk (phs x) (nvars x).

(* The context agrees with the state m f between steps. *)
Record StepCore (m: PA) (f: CNF) (x: Ctx): Prop := {
  sc_prop: PropInv m f x;
  sc_complete: forall (c: Clause), c ∈ f -> exists (i: nat) (ls: list Lit), tget (cmap x) i = Some ls /\ forall (l: Lit), In l ls <-> l ∈ c;
  sc_cursor: CursorT (vals x) f (alls x) (nlits x) (cur x);
  sc_saved: SavedC f (alls x) (nlits x) m (saved x);
  sc_empty: forall (i: nat), tget (cmap x) i = Some [] -> In i (shorts x);
  sc_shorts: forall (i: nat) (ls: list Lit), In i (shorts x) -> tget (cmap x) i = Some ls -> length ls <= 1;
  sc_marks: Unmarked (mrk x);
  sc_bound: S (max_atom_f f) <= nvars x
}.

(* Moreover the state is well-formed and entailed, as every reachable state is. *)
Definition StepInv (s: State) (x: Ctx): Prop :=
match s with
| fail      => True
| state m f => StepCore m f x /\ WellFormed (state m f) /\ Entails f m
end.

Section Split.
  Lemma no_decisions_zero: forall (m: PA), NoDecisions m -> decisions m = 0.
  Proof.
    intros m. induction m as [|m IH l|m IH l]; simpl.
    - reflexivity.
    - assumption.
    - intros [].
  Qed.

  (* The decision l of ⟨m; l ++ n⟩ has its cursor saved after those of n. *)
  Lemma saved_c_split: forall (f: CNF) (alls: Table Lit) (k: nat) (m n: PA) (l: Lit) (st: list nat),
    SavedC f alls k ⟨m; l ++ n⟩ st ->
    exists (c: nat) (st': list nat),
      skipn (decisions n) st = c :: st' /\ CursorT (values m) f alls k c /\ SavedC f alls k m st'.
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

  (* The watches are fine up to an empty queue with respect to the values before the decision l of ⟨m; l ++ n⟩. *)
  Lemma saved_q_split: forall (cm: ClauseMap) (m n: PA) (l: Lit),
    SavedQ cm ⟨m; l ++ n⟩ -> AllWatchQ (values m) (fun (_: Lit) => False) cm /\
      SavedQ cm m.
  Proof.
    intros cm m n l. induction n as [|n IH l'|n IH l']; simpl.
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

  Lemma trail_lits_app: forall (m n: PA), trail_lits ⟨m ++ n⟩ = trail_lits m ++ trail_lits n.
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

  (* The trail before the decision d of ⟨mt; d ++ n⟩ is as long as the trail without d and n. *)
  Lemma length_split: forall (tr: Table Lit) (tlen: nat) (mt n: PA) (d: Lit),
    TrailOf tr tlen ⟨mt; d ++ n⟩ -> tlen - S (PA.length n) = PA.length mt.
  Proof.
    intros tr tlen mt n d [Hlen _]. rewrite Hlen, trail_lits_length. clear Hlen.
    induction n as [|n IH l|n IH l]; simpl in *; lia.
  Qed.

  Lemma level_length_split: forall (m m': PA) (l: Lit) (n: PA),
    m = ⟨m'; l ++ n⟩ -> NoDecisions n -> level_length m = PA.length n.
  Proof.
    intros m m' l n -> Hn. induction n as [|n IH l'|n IH l']; simpl in *.
    - reflexivity.
    - now rewrite IH.
    - destruct Hn.
  Qed.

  (* The saved cursors only depend on the decisions. *)
  Lemma saved_c_extends: forall (f: CNF) (alls: Table Lit) (k: nat) (m n: PA) (st: list nat),
    NoDecisions n -> SavedC f alls k m st -> SavedC f alls k ⟨m ++ n⟩ st.
  Proof.
    intros f alls k m n st. induction n as [|n IH l|n IH l]; simpl.
    - easy.
    - assumption.
    - intros [].
  Qed.

  (* With an empty queue, the watches are fine up to an empty queue. *)
  Lemma watch_q_empty: forall (v: Values) (tr: Table Lit) (q: nat) (cm: ClauseMap),
    AllWatchQ v (Queued tr q q) cm -> AllWatchQ v (fun (_: Lit) => False) cm.
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
    Reordered cm cm' ->
    (forall (c: Clause), c ∈ f -> exists (i: nat) (ls: list Lit), tget cm i = Some ls /\
      forall (l: Lit), In l ls <-> l ∈ c) ->
    forall (c: Clause), c ∈ f -> exists (i: nat) (ls: list Lit), tget cm' i = Some ls /\
      forall (l: Lit), In l ls <-> l ∈ c.
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
End Split.

(* Checking the short clauses keeps the context consistent; if no clause is false, none is empty. *)
Lemma front_shorts: forall (m m1: PA) (f: CNF) (x x1: Ctx) (r: option nat),
  StepCore m f x ->
  check_shorts (shorts x) m x = (m1, x1, r) ->
  state m f ==>*[DPLL_BJ] state m1 f /\ Extends m m1 /\ StepCore m1 f x1 /\
  (r = None -> forall (i: nat), tget (cmap x1) i <> Some []) /\
  (forall (i: nat), r = Some i ->
    exists (ls: list Lit), tget (cmap x1) i = Some ls /\ forall (y: Lit), In y ls -> lookup (vals x1) y = Some false).
Proof.
  intros m m1 f x x1 r [Hprop Hcomplete Hcursor Hsaved Hempty Hshorts Hmarks Hbound] Hcheck.
  pose proof (check_shorts_extends (shorts x) m m1 x x1 r Hcheck) as Hext.
  destruct (check_shorts_spec (shorts x) m m1 f x x1 r Hprop Hshorts Hcheck)
    as (Hder & (Hcm & _ & Hsh & Hal & Hnl & Hcur & Hsv & _ & Hmk & Hnv) & Hincl & Hprop1 & Hnone & Hsome).
  split.
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
      * split.
        -- intros Hr i Hi. apply (Hnone Hr i []).
           ++ apply Hempty. now apply (reordered_empty (cmap x) (cmap x1)).
           ++ assumption.
           ++ reflexivity.
        -- assumption.
Qed.

(* Propagation keeps the context consistent, and empties the queue unless a clause is false. *)
Lemma front_prop: forall (m1 m2: PA) (f: CNF) (x1 x2: Ctx) (r: option nat),
  StepCore m1 f x1 ->
  WellFormed (state m1 f) ->
  (forall (i: nat), tget (cmap x1) i <> Some []) ->
  propagate (S (nvars x1)) m1 (clear_shorts x1) = (m2, x2, r) ->
  state m1 f ==>*[DPLL_BJ] state m2 f /\ Extends m1 m2 /\ StepCore m2 f x2 /\ shorts x2 = [] /\
  (forall (i: nat), tget (cmap x2) i <> Some []) /\ (r = None -> qhead x2 = tlen x2) /\
  (forall (i: nat), r = Some i ->
    exists (ls: list Lit), tget (cmap x2) i = Some ls /\ forall (y: Lit), In y ls -> lookup (vals x2) y = Some false).
Proof.
  intros m1 m2 f x1 x2 r [Hprop Hcomplete Hcursor Hsaved Hempty Hshorts Hmarks Hbound] Hwf Hnonempty Hpropagate.
  pose proof (propagate_extends _ m1 m2 _ x2 r Hpropagate) as Hext.
  destruct (propagate_spec (S (nvars x1)) m1 m2 f (clear_shorts x1) x2 r) as
    (Hder & (Hcm & Hsh & Hal & Hnl & Hcur & Hsv & _ & Hmk & Hnv) & Hincl & Hprop2 & Hnone & Hsome).
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
  - simpl in Hcm, Hsh, Hal, Hnl, Hcur, Hsv, Hmk, Hnv, Hincl. split.
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
           ++ rewrite Hal, Hnl, Hsv. destruct Hext as [n [-> Hn]]. now apply saved_c_extends.
           ++ intros i Hi. apply (reordered_empty (cmap x1) (cmap x2)) in Hi.
              ** now apply Hnonempty in Hi.
              ** assumption.
           ++ rewrite Hsh. intros i ls [].
           ++ now rewrite Hmk.
           ++ now rewrite Hnv.
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
  AllWatchQ v (fun (_: Lit) => False) cm -> AllWatchQ v Q cm.
Proof.
  intros v Q cm Hall i ls Hi w Hw Hf. destruct (Hall i ls Hi w Hw Hf) as [[]|Ht].
  now right.
Qed.

(* After jumping back to before the decision d of ⟨mt; d ++ n⟩ and assigning the unassigned u, the context agrees
   with ⟨mt, u⟩: the watches were fine before d, the queue holds just u, and the saved cursor of d is restored. *)
Lemma jump_core: forall (mt n: PA) (f: CNF) (x: Ctx) (d u: Lit) (v': Values) (c0: nat) (st: list nat) (k: nat)
  (mk: Table bool),
  StepCore ⟨mt; d ++ n⟩ f x ->
  ValuesOf v' mt ->
  lookup v' u = None ->
  CursorT (values mt) f (alls x) (nlits x) c0 ->
  SavedC f (alls x) (nlits x) mt st ->
  Unmarked mk ->
  StepCore ⟨mt, u⟩ f (assign (jump x v' (PA.length mt) c0 st k mk) u 0).
Proof.
  intros mt n f x d u v' c0 st k mk
    [[[Hvals Hfresh Htrail Hsound Hnodup] Hq Hwatch Hsavedq Hlisted Hblocked] Hcomplete
    Hcursor
    Hsaved Hempty Hshorts Hmarks Hbound] Hv' Hu Hc0 Hst Hmk.
  destruct (fresh_split mt n d Hfresh) as [Hfresh' _].
  destruct (saved_q_split (cmap x) mt n d Hsavedq) as [Hok Hsavedq'].
  assert (Hext: forall (y: Lit), lookup (values mt) y = lookup v' y).
  - intros y. now rewrite lookup_values, Hv'.
  - split.
    + apply prop_inv_assign.
      * split.
        -- split.
           ++ assumption.
           ++ assumption.
           ++ apply (trail_of_prefix _ (tlen x) mt (PA.app ⟨; d⟩ n)). now rewrite PA.app_assoc.
           ++ assumption.
           ++ assumption.
        -- simpl. lia.
        -- apply watch_q_weaken. now apply (all_watch_q_ext (values mt)).
        -- assumption.
        -- assumption.
        -- assumption.
      * assumption.
    + assumption.
    + apply (cursor_incl (values mt)).
      * intros l Hl. rewrite Hext. apply (incl_undef v' (set_value v' u)).
        -- apply incl_set_value.
           ++ apply incl_refl.
           ++ assumption.
        -- assumption.
      * assumption.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
Qed.

(* A decision with an empty queue keeps propagation consistent: the watches are fine before it. *)
Lemma prop_inv_decide: forall (m: PA) (f: CNF) (x: Ctx) (l: Lit) (r: nat),
  PropInv m f x -> qhead x = tlen x -> lookup (vals x) l = None -> PropInv ⟨m; l⟩ f (assign x l r).
Proof.
  intros m f x l r Hinv Hq Hl.
  pose proof (prop_inv_assign m f x l r Hinv Hl) as [[Hvals Hfresh Htrail Hsound Hnodup]
    Hq' Hwatch Hsaved Hlisted Hblocked].
  destruct Hinv as [[Hvals0 _ _ _ _] _ Hwatch0 Hsaved0 _ _]. split.
  - now split.
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

(* PropInv only looks at the values, the trail, the queue, the clauses and the watch
   lists. *)
Lemma prop_inv_ext: forall (m: PA) (f: CNF) (x x': Ctx),
  PropInv m f x -> vals x' = vals x -> tr x' = tr x -> tlen x' = tlen x -> qhead x' = qhead x -> cmap x' = cmap x ->
  wls x' = wls x -> PropInv m f x'.
Proof.
  intros m f x x' [Hcore Hq Hwatch Hsaved Hlisted Hblocked] Hv Htr Hlen Hqh Hcm Hwl.
  split.
  - now apply (core_ext m f x).
  - now rewrite Hqh, Hlen.
  - now rewrite Hv, Htr, Hqh, Hlen, Hcm.
  - now rewrite Hcm.
  - now rewrite Hcm, Hwl.
  - now rewrite Hcm, Hwl.
Qed.

(* Deciding the unassigned literal at position c of the cursor, with its phase, is a Decide step, to a consistent
   context. *)
Lemma decide_spec: forall (m: PA) (f: CNF) (x: Ctx) (c: nat),
  StepCore m f x ->
  qhead x = tlen x ->
  shorts x = [] ->
  (forall (i: nat), tget (cmap x) i <> Some []) ->
  CursorT (vals x) f (alls x) (nlits x) c ->
  c < nlits x ->
  lookup (vals x) (tget (alls x) c) = None ->
  state m f ==>[DPLL_BJ] state ⟨m; (phase (phs x) (tget (alls x) c))⟩ f /\
  StepCore ⟨m; (phase (phs x) (tget (alls x) c))⟩ f (assign (open_level x c) (phase (phs x) (tget (alls x) c)) 0).
Proof.
  intros m f x c [Hprop Hcomplete _ Hsaved _ _ Hmarks Hbound] Hq Hshorts Hnonempty Hc Hlt Hundef.
  pose proof Hc as [_ [Hin _]]. pose proof Hprop as [[Hvals _ _ _ _] _ _ _ _ _].
  apply (phase_undef _ (phs x)) in Hundef as Hl.
  assert (Hext: forall (y: Lit), lookup (vals x) y = lookup (values m) y).
  - intros y. now rewrite Hvals, lookup_values.
  - split.
    + apply (t_step Decide).
      * right. right. now left.
      * apply r_decide.
        -- now apply phase_in, Hin.
        -- unfold Undef. now rewrite <- Hvals.
    + split.
      * apply prop_inv_decide.
        -- now apply (prop_inv_ext m f x).
        -- assumption.
        -- assumption.
      * assumption.
      * apply (cursor_incl (vals x)).
        -- intros y Hy. apply (incl_undef (vals x) (set_value (vals x) (phase (phs x) (tget (alls x) c)))).
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
Qed.

(* With an empty queue, no empty clause and nothing left to decide, no clause is false and every literal of f is
   assigned. *)
Lemma final_state: forall (m: PA) (f: CNF) (x: Ctx) (c: nat),
  StepCore m f x ->
  qhead x = tlen x ->
  (forall (i: nat), tget (cmap x) i <> Some []) ->
  CursorT (vals x) f (alls x) (nlits x) c ->
  ~ c < nlits x ->
  (forall (cl: Clause), cl ∈ f -> c_eval m cl <> Some false) /\ (forall (l: Lit), l ∈ f -> ~ Undef m l).
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
    intros rs s1 s2 s3 H12 H23. revert s1 H12. induction H23 as [|s2 s4 s3 H24 _ IH]; intros s1 H12.
    - now apply Relation_Operators.t_step.
    - apply Relation_Operators.t_trans with s2.
      + now apply Relation_Operators.t_step.
      + now apply IH.
  Qed.

  (* A derivation between different states is strict. *)
  Lemma derivation_strict: forall (rs: list Rule) (s s': State), s ==>*[rs] s' -> s <> s' -> s ==>+[rs] s'.
  Proof.
    intros rs s s' H Hneq. apply clos_rt_rt1n in H. destruct H as [|s1 s2 H12 H23].
    - contradiction.
    - now apply (step_then_derivation rs s s1 s2).
  Qed.

  (* A trail extended by propagations only, and as long, is the same trail. *)
  Lemma extends_same_length: forall (m m': PA), Extends m m' -> PA.length m' = PA.length m -> m' = m.
  Proof.
    intros m m' [n [-> _]] Hlen. rewrite <- !trail_lits_length, trail_lits_app, length_app in Hlen.
    destruct n as [|n l|n l].
    - reflexivity.
    - simpl in Hlen. rewrite length_app in Hlen. simpl in Hlen. lia.
    - simpl in Hlen. rewrite length_app in Hlen. simpl in Hlen. lia.
  Qed.

  (* The invariant after a strict derivation to a consistent context. *)
  Lemma step_inv_after: forall (m m': PA) (f: CNF) (x': Ctx),
    WellFormed (state m f) -> Entails f m -> state m f ==>+[DPLL_BJ] state m' f -> StepCore m' f x' ->
    StepInv (state m' f) x'.
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
  (forall (cl: Clause), cl ∈ f -> c_eval m cl <> Some false) -> (forall (l: Lit), l ∈ f -> ~ Undef m l) ->
  Final Basic (state m f).
Proof.
  intros m f Hno_conflict Hno_decision [s' Htrans]. inversion Htrans as [r ? ? s'' Hr Hstep]; subst.
  destruct Hr as [<-|[<-|[<-|[]]]].
  - inversion Hstep as [? ? c Hc_in_f Hc Hno_dec]; subst. now apply (Hno_conflict c).
  - inversion Hstep as [? ? l Hl_in_f Hundef]; subst. destruct Hl_in_f as [Hl_in_f|Hnegl_in_f].
    + now apply (Hno_decision l).
    + apply (Hno_decision (¬l)).
      * assumption.
      * now apply l_eval_neg_none_iff in Hundef.
  - inversion Hstep as [m_split n_split ? c l_split Hc_in_f Hc Hno_dec]; subst. now apply (Hno_conflict c).
Qed.

(* The initial context. *)
Section Initial.
  (* A watcher e is appended to the watch list of z. *)
  Definition add_watcher (wl: WatchLists) (z: Lit) (e: Watcher): WatchLists :=
    tset wl (lit_key z) (watching wl z ++ [e]).

  Lemma add_watcher_keep: forall (wl: WatchLists) (z y: Lit) (e e': Watcher),
    In e' (watching wl y) -> In e' (watching (add_watcher wl z e) y).
  Proof. intros wl z y e e' He'. now apply watching_push. Qed.

  Lemma add_watcher_new: forall (wl: WatchLists) (z: Lit) (e: Watcher), In e
    (watching (add_watcher wl z e) z).
  Proof. intros wl z e. apply watching_push_new. Qed.

  (* The watchers in the list of y after appending e to that of z. *)
  Lemma add_watcher_in: forall (wl: WatchLists) (z y: Lit) (e e': Watcher),
    In e' (watching (add_watcher wl z e) y) -> In e' (watching wl y) \/ e' = e.
  Proof.
    intros wl z y e e' He'. unfold add_watcher in He'. rewrite watching_add in He'.
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

  Lemma watch_first_keep: forall (wl: WatchLists) (k: nat) (ls: list Lit) (y: Lit)
    (e: Watcher),
    In e (watching wl y) -> In e (watching (watch_first wl k ls) y).
  Proof.
    intros wl k [|a [|b ls]] y e He; simpl.
    - assumption.
    - now apply add_watcher_keep.
    - now apply add_watcher_keep, add_watcher_keep.
  Qed.

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

  Lemma index_spec: forall (lss: list (list Lit)) (k: nat) (cm cm': ClauseMap)
    (wl wl': WatchLists)
    (sh sh': list nat),
    (forall (i: nat) (ls: list Lit), tget cm i = Some ls -> i < k) ->
    (forall (l: Lit) (i: nat) (b: Lit), In (i, b) (watching wl l) -> i < k) ->
    Listed cm wl ->
    Blocked cm wl ->
    (forall (i: nat), tget cm i = Some [] -> In i sh) ->
    (forall (i: nat) (ls: list Lit), In i sh -> tget cm i = Some ls -> length ls <= 1) ->
    (forall (i: nat), In i sh -> i < k) ->
    index k lss cm wl sh = (cm', wl', sh') ->
    Listed cm' wl' /\ Blocked cm' wl' /\
      (forall (i: nat), tget cm' i = Some [] -> In i sh') /\
    (forall (i: nat) (ls: list Lit), In i sh' -> tget cm' i = Some ls -> length ls <= 1) /\
    (forall (i: nat) (ls: list Lit), tget cm' i = Some ls -> tget cm i = Some ls \/ In ls lss) /\
    (forall (ls: list Lit), In ls lss -> exists (i: nat), tget cm' i = Some ls) /\
    (forall (i: nat) (ls: list Lit), tget cm i = Some ls -> tget cm' i = Some ls).
  Proof.
    intros lss.
    induction lss as
      [|ls lss IH]; intros k cm cm' wl wl' sh sh' Hfresh Hwfresh Hlisted Hblocked Hempty
      Hshort Hbelow Hindex; simpl in Hindex.
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
        * intros i Hin. destruct (length ls <=? 1).
          -- destruct Hin as [<-|Hin].
             ++ lia.
             ++ apply Hbelow in Hin. lia.
          -- apply Hbelow in Hin. lia.
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

  Lemma fill_below: forall (ls: list Lit) (t: Table Lit) (k j: nat), j < k -> tget (fill t k ls) j = tget t j.
  Proof.
    intros ls. induction ls as [|l ls IH]; intros t k j Hj; simpl.
    - reflexivity.
    - rewrite IH.
      + apply tget_tset_other. lia.
      + lia.
  Qed.

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

  (* The initial context for the clauses lss and the literals ls to decide on, with nv as the bound on the trail:
     no values, an empty trail, and the clauses indexed. *)
  Definition initial_of (lss: list (list Lit)) (ls: list Lit) (nv: nat): Ctx :=
  match index 0 lss (tmake None) (tmake []) [] with
  | (cm, wl, sh) =>
    mkCtx (tmake None) cm wl (tmake (Pos 0)) 0 0 sh (fill (tmake (Pos 0)) 0 ls)
      (length ls) 0 [] (tmake 0) (tmake 0) 0 (tmake false) (tmake None) nv end.

  (* The initial context is consistent with the initial state of f if lss lists the clauses of f, without
     duplicate literals, and ls the literals of f. *)
  Lemma initial_of_inv: forall (f: CNF) (lss: list (list Lit)) (ls: list Lit) (nv: nat),
    (forall (cs: list Lit), In cs lss -> NoDup cs /\ ClauseOf f cs) ->
    (forall (c: Clause), c ∈ f -> exists (cs: list Lit), In cs lss /\ forall (l: Lit), In l cs <-> l ∈ c) ->
    (forall (l: Lit), In l ls <-> l ∈ f) ->
    S (max_atom_f f) <= nv ->
    StepInv (state ⟨⟩ f) (initial_of lss ls nv).
  Proof.
    intros f lss ls nv Hlss Hcovered Hls Hnv. unfold initial_of.
    destruct (index 0 lss (tmake None) (tmake []) []) as [[cm wl] sh] eqn:Hindex.
    destruct (index_spec lss 0 (tmake None) cm (tmake []) wl [] sh)
      as (Hlisted & Hblocked & Hempty & Hshort & Hsound & Hcomplete & _).
    - intros i cs Hi. now rewrite tget_tmake in Hi.
    - intros l i b Hin. unfold watching in Hin. now rewrite tget_tmake in Hin.
    - intros i cs z Hi. now rewrite tget_tmake in Hi.
    - intros l i b cs Hin. unfold watching in Hin. now rewrite tget_tmake in Hin.
    - intros i Hi. now rewrite tget_tmake in Hi.
    - intros i cs [].
    - intros i [].
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
             ++ intros l Hl_in_f _. apply Hls, In_nth with (d := Pos 0) in Hl_in_f as [j [Hj Hl]].
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
      + split.
        * apply initial_well_formed.
        * apply e_nil.
  Qed.

End Initial.
