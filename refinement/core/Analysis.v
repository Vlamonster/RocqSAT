(* Conflict analysis for backjumping, as MiniSat does it: walk the trail back from its
   end, resolving the conflict clause with the reasons of the literals of the current
   decision level, until one literal of that level is left (the first unique implication
   point). The literals of the current level are only counted and marked; the others are
   collected in a list. The functions work on the context, as the C solver does. *)
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import Model.
From RocqSAT.refinement Require Import Tactics.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Search.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import Heur.
From RocqSAT.refinement Require Import Propagate.

Section Entailment.
  (* Some literal of ls is true in every model of f. *)
  Definition Entailed (f: CNF) (ls: list Lit): Prop :=
    forall (m: PA), Model m f -> exists (l: Lit), In l ls /\ l_eval m l = Some true.

  (* Every clause of f is entailed. *)
  Lemma entailed_clause_of: forall (f: CNF) (ls: list Lit), ClauseOf f ls -> Entailed f ls.
  Proof.
    intros f ls [c [Hc_in_f Hiff]] m Hm. unfold Model in Hm. rewrite f_eval_true_iff in Hm. apply Hm in Hc_in_f.
    apply c_eval_true_iff in Hc_in_f as [l [Hl_in_c Hl]]. exists l. split.
    - now apply Hiff.
    - assumption.
  Qed.

  (* A list with all literals of an entailed list is entailed. *)
  Lemma entailed_incl: forall (f: CNF) (ls ls': list Lit),
    Entailed f ls -> (forall (y: Lit), In y ls -> In y ls') -> Entailed f ls'.
  Proof.
    intros f ls ls' Hls Hincl m Hm. destruct (Hls m Hm) as [l [Hin Hl]]. exists l. split.
    - now apply Hincl.
    - assumption.
  Qed.

  (* Resolution is sound: a list with the literals of c other than ¬x and those of r other than x is entailed.
     If ¬x makes c true, x is false, so some other literal makes r true. *)
  Lemma entailed_resolve: forall (f: CNF) (c r ls: list Lit) (x: Lit),
    Entailed f c ->
    Entailed f r ->
    (forall (y: Lit), In y c -> y <> ¬x -> In y ls) ->
    (forall (y: Lit), In y r -> y <> x -> In y ls) ->
    Entailed f ls.
  Proof.
    intros f c r ls x Hc Hr Hc_ls Hr_ls m Hm. destruct (Hc m Hm) as [y [Hy_in Hy]].
    destruct (Lit.eq_dec y (¬x)) as [->|Hneq].
    - destruct (Hr m Hm) as [z [Hz_in Hz]]. exists z. split.
      + apply Hr_ls.
        * assumption.
        * intros ->. apply l_eval_neg_some_iff in Hz. simpl in Hz. congruence.
      + assumption.
    - exists y. split.
      + now apply Hc_ls.
      + assumption.
  Qed.

  (* The clause with the literals of ls. *)
  Definition clause_of (ls: list Lit): Clause := fold_right Clause.add Clause.empty ls.

  Lemma clause_of_spec: forall (ls: list Lit) (l: Lit), l ∈ clause_of ls <-> In l ls.
  Proof.
    intros ls l. induction ls as [|y ls IH]; cbn.
    - split.
      + intros Hin. now apply Clause.empty_spec in Hin.
      + intros [].
    - rewrite Clause.add_spec, IH. split.
      + intros [->|Hin].
        * now left.
        * now right.
      + intros [->|Hin].
        * now left.
        * now right.
  Qed.

  (* An entailed list gives a clause that follows from f. *)
  Lemma entailed_consequence: forall (f: CNF) (ls: list Lit), Entailed f ls -> f ⊨ CNF.singleton (clause_of ls).
  Proof.
    intros f ls Hls m Hm. apply model_singleton_iff, c_eval_true_iff. destruct (Hls m Hm) as [l [Hin Hl]].
    exists l. split.
    - now apply clause_of_spec.
    - assumption.
  Qed.
End Entailment.

(* The level of the atom of y in x. *)
Abbreviation level x y := (tget (lvl x) (extract y)).

Section Levels.
  (* The tables that hold the clauses, reasons and levels of the trail (see TraceOk). *)
  Context (cm: ClauseMap) (rsn: Table Reason) (lv: Table nat) (rcl: Table (list Lit))
    (rps: Table nat) (nr: nat).

  (* A literal and its negation have the same atom. *)
  Lemma extract_neg: forall (y: Lit), extract (¬y) = extract y.
  Proof. intros y. apply Neg.extract_eq. now right. Qed.

  (* The levels and reasons of a trail hold for every prefix of it. *)
  Lemma trace_app: forall (m n: PA),
    TraceOk cm rsn lv rcl rps nr ⟨m ++ n⟩ -> TraceOk cm rsn lv rcl rps nr m.
  Proof.
    intros m n. induction n as [|n IH t|n IH t]; cbn [PA.app TraceOk]; intros Htrace.
    - assumption.
    - destruct Htrace as (_ & _ & Htrace). now apply IH.
    - destruct Htrace as (_ & Htrace). now apply IH.
  Qed.

  (* No literal of m has a level above the number of its decisions. *)
  Lemma trace_le: forall (m: PA) (y: Lit),
    TraceOk cm rsn lv rcl rps nr m -> y ∈ m -> tget lv (extract y) <= decisions m.
  Proof.
    intros m y.
    induction m as [|m IH t|m IH t]; cbn [TraceOk decisions]; intros Htrace Hy.
    - destruct Hy.
    - destruct Htrace as (Hlv & _ & Htrace). destruct Hy as [<- | Hy].
      + lia.
      + now apply IH.
    - destruct Htrace as (Hlv & Htrace). destruct Hy as [<- | Hy].
      + lia.
      + apply IH in Hy.
        * lia.
        * assumption.
  Qed.

  (* The decision l0 of ⟨m0; l0 ++ n0⟩ and the literals propagated after it are at level
     S (decisions m0). *)
  Lemma trace_last_level: forall (m0 n0: PA) (l0 y: Lit),
    TraceOk cm rsn lv rcl rps nr ⟨m0; l0 ++ n0⟩ -> NoDecisions n0 -> y = l0 \/ y ∈ n0 ->
    tget lv (extract y) = S (decisions m0).
  Proof.
    intros m0 n0 l0 y.
    induction n0 as [|n IH t|n IH t]; cbn [PA.app TraceOk NoDecisions];
      intros Htrace Hnd Hy.
    - destruct Htrace as (Hlv & _). destruct Hy as [-> | []]. assumption.
    - destruct Htrace as (Hlv & _ & Htrace). destruct Hy as [-> | [<- | Hy]].
      + apply IH.
        * assumption.
        * assumption.
        * now left.
      + rewrite Hlv, decisions_app, (no_decisions_zero n Hnd). simpl. lia.
      + apply IH.
        * assumption.
        * assumption.
        * now right.
    - destruct Hnd.
  Qed.

  (* The decision d of ⟨mt; d ++ n⟩ and the literals after it have a level above the
     decisions of mt. *)
  Lemma trace_seg_ge: forall (mt n: PA) (d z: Lit),
    TraceOk cm rsn lv rcl rps nr ⟨mt; d ++ n⟩ -> z = d \/ z ∈ n ->
    S (decisions mt) <= tget lv (extract z).
  Proof.
    intros mt n d z.
    induction n as [|n IH t|n IH t]; cbn [PA.app TraceOk]; intros Htrace Hz.
    - destruct Htrace as (Hlv & _). destruct Hz as [-> | []]. lia.
    - destruct Htrace as (Hlv & _ & Htrace). destruct Hz as [-> | [<- | Hz]].
      + apply IH.
        * assumption.
        * now left.
      + rewrite Hlv, decisions_app. simpl. lia.
      + apply IH.
        * assumption.
        * now right.
    - destruct Htrace as (Hlv & Htrace). destruct Hz as [-> | [<- | Hz]].
      + apply IH.
        * assumption.
        * now left.
      + rewrite Hlv, decisions_app. simpl. lia.
      + apply IH.
        * assumption.
        * now right.
  Qed.

  (* A false literal of ⟨mt; d ++ n⟩ of a level up to the decisions of mt is false in
     mt. *)
  Lemma false_before: forall (mt n: PA) (d y: Lit),
    Fresh ⟨mt; d ++ n⟩ -> TraceOk cm rsn lv rcl rps nr ⟨mt; d ++ n⟩ ->
    l_eval ⟨mt; d ++ n⟩ y = Some false -> tget lv (extract y) <= decisions mt ->
    l_eval mt y = Some false.
  Proof.
    intros mt n d y Hfresh Htrace Hy Hlv.
    apply l_eval_false_in in Hy. apply PA.in_app_iff in Hy as [Hin | [Heq | Hin]].
    - exfalso. pose proof (trace_seg_ge mt n d (¬y) Htrace (or_intror Hin)).
      rewrite extract_neg in *. lia.
    - exfalso. assert (Hd: ¬y = d \/ ¬y ∈ n) by (left; now symmetry).
      pose proof (trace_seg_ge mt n d (¬y) Htrace Hd).
      rewrite extract_neg in *. lia.
    - rewrite <- (Neg.involutive y), l_eval_neg, fresh_in_true.
      + reflexivity.
      + apply (fresh_split mt n d Hfresh).
      + assumption.
  Qed.

  (* A false literal of ⟨mt; d ++ n⟩ of a level above the decisions of mt is unassigned
     in mt. *)
  Lemma undef_before: forall (mt n: PA) (d u: Lit),
    Fresh ⟨mt; d ++ n⟩ -> TraceOk cm rsn lv rcl rps nr ⟨mt; d ++ n⟩ ->
    l_eval ⟨mt; d ++ n⟩ u = Some false -> decisions mt < tget lv (extract u) ->
    l_eval mt u = None.
  Proof.
    intros mt n d u Hfresh Htrace Hu Hlv.
    destruct (l_eval mt u) as [[|]|] eqn:Hmt.
    - exfalso. apply l_eval_true_in in Hmt.
      assert (Hin: u ∈ ⟨mt; d ++ n⟩) by (apply PA.in_app_iff; right; now right).
      rewrite fresh_in_true in Hu by assumption. discriminate.
    - exfalso. apply l_eval_false_in in Hmt.
      pose proof (trace_app ⟨mt; d⟩ n Htrace) as [_ Htrace_mt].
      pose proof (trace_le mt (¬u) Htrace_mt Hmt).
      rewrite extract_neg in *. lia.
    - reflexivity.
  Qed.

  (* A literal propagated after the decision l0 of ⟨m0; l0 ++ n0⟩ has a reason that
     justifies it after the trail before it. *)
  Lemma reason_at: forall (tr: Table Lit) (m0 n0: PA) (l0: Lit) (tlen q: nat),
    TraceOk cm rsn lv rcl rps nr ⟨m0; l0 ++ n0⟩ -> TrailOf tr tlen ⟨m0; l0 ++ n0⟩ ->
    NoDecisions n0 -> PA.length m0 < q < tlen ->
    exists (mq: PA), TrailOf tr q mq /\
      ReasonOk cm rcl rps nr mq (tget tr q) (tget rsn (extract (tget tr q))).
  Proof.
    intros tr m0 n0 l0. induction n0 as [|n IH t|n IH t];
      intros tlen q Htrace Htrail Hnd Hq.
    - destruct Htrail as [Hlen _]. cbn [PA.app trail_lits] in Hlen.
      rewrite length_app, trail_lits_length in Hlen. simpl in Hlen. lia.
    - cbn [PA.app TraceOk NoDecisions] in Htrace, Hnd.
      destruct Htrace as (_ & Ht & Htrace).
      destruct (trail_of_snoc tr tlen ⟨m0; l0 ++ n⟩ ⟨m0; l0 ++ (⟨n, t⟩)⟩ t eq_refl
                  Htrail)
        as (Hlen & Htq & Hprefix).
      destruct (Nat.eq_dec q (PA.length ⟨m0; l0 ++ n⟩)) as [-> | Hne].
      + exists ⟨m0; l0 ++ n⟩. split.
        * assumption.
        * now rewrite Htq.
      + apply (IH (PA.length ⟨m0; l0 ++ n⟩)).
        * assumption.
        * assumption.
        * assumption.
        * lia.
    - destruct Hnd.
  Qed.
End Levels.
Arguments trace_app {cm rsn lv rcl rps nr}.
Arguments trace_le {cm rsn lv rcl rps nr}.
Arguments trace_last_level {cm rsn lv rcl rps nr}.
Arguments trace_seg_ge {cm rsn lv rcl rps nr}.
Arguments false_before {cm rsn lv rcl rps nr}.
Arguments undef_before {cm rsn lv rcl rps nr}.
Arguments reason_at {cm rsn lv rcl rps nr}.

Section Positions.
  (* A literal on a trail is in the list of its literals. *)
  Lemma trail_lits_in: forall (m: PA) (y: Lit), y ∈ m -> In y (trail_lits m).
  Proof.
    intros m y. induction m as [|m IH t|m IH t]; cbn [trail_lits]; intros Hy.
    - destruct Hy.
    - apply in_or_app. destruct Hy as [<- | Hy].
      + right. now left.
      + left. now apply IH.
    - apply in_or_app. destruct Hy as [<- | Hy].
      + right. now left.
      + left. now apply IH.
  Qed.

  (* A literal on a trail is at a position of its table below its length. *)
  Lemma pos_of_in: forall (tr: Table Lit) (n: nat) (m: PA) (z: Lit),
    TrailOf tr n m -> z ∈ m -> exists (q: nat), q < n /\ tget tr q = z.
  Proof.
    intros tr n m z [Hlen Hnth] Hz.
    apply trail_lits_in, In_nth with (d := Pos 0) in Hz as (q & Hq & Hz).
    exists q. split.
    - lia.
    - rewrite Hnth.
      + assumption.
      + lia.
  Qed.

  (* The table of ⟨m0; l0 ++ n0⟩ from the position of l0 on holds l0 and then the
     literals of n0. *)
  Lemma seg_nth: forall (tr: Table Lit) (tlen: nat) (m0 n0: PA) (l0: Lit) (q: nat),
    TrailOf tr tlen ⟨m0; l0 ++ n0⟩ -> PA.length m0 <= q < tlen ->
    tget tr q = l0 \/ tget tr q ∈ n0.
  Proof.
    intros tr tlen m0 n0 l0 q [Hlen Hnth] Hq. rewrite Hnth by lia.
    rewrite trail_lits_app in Hlen |- *. cbn [trail_lits] in Hlen |- *.
    rewrite <- app_assoc.
    rewrite !length_app, !trail_lits_length in Hlen. simpl in Hlen.
    rewrite app_nth2 by (rewrite trail_lits_length; lia). rewrite trail_lits_length.
    destruct (q - PA.length m0) as [|k] eqn:Hk.
    - now left.
    - right. simpl. apply in_trail_lits, nth_In. rewrite trail_lits_length. lia.
  Qed.

  (* The decision l0 of ⟨m0; l0 ++ n0⟩ and the literals after it are on its table, from
     the position of l0 on. *)
  Lemma seg_pos: forall (tr: Table Lit) (tlen: nat) (m0 n0: PA) (l0 z: Lit),
    TrailOf tr tlen ⟨m0; l0 ++ n0⟩ -> z = l0 \/ z ∈ n0 ->
    exists (q: nat), PA.length m0 <= q < tlen /\ tget tr q = z.
  Proof.
    intros tr tlen m0 n0 l0 z [Hlen Hnth] Hz.
    assert (Hin: In z ([l0] ++ trail_lits n0)).
    - destruct Hz as [-> | Hz].
      + now left.
      + right. now apply trail_lits_in.
    - apply In_nth with (d := Pos 0) in Hin as (k & Hk & Hz').
      rewrite trail_lits_app in Hlen, Hnth. cbn [trail_lits] in Hlen, Hnth.
      rewrite <- app_assoc in Hnth.
      rewrite !length_app, !trail_lits_length in Hlen. simpl in Hlen, Hk.
      rewrite trail_lits_length in Hk.
      exists (PA.length m0 + k). split.
      + lia.
      + rewrite Hnth.
        * rewrite app_nth2 by (rewrite trail_lits_length; lia).
          rewrite trail_lits_length.
          now replace (PA.length m0 + k - PA.length m0) with k by lia.
        * lia.
  Qed.

  (* Distinct positions of the table of a fresh trail hold distinct atoms. *)
  Lemma fresh_positions: forall (tr: Table Lit) (m: PA) (tlen q1 q2: nat),
    Fresh m -> TrailOf tr tlen m -> q1 < tlen -> q2 < tlen ->
    extract (tget tr q1) = extract (tget tr q2) -> q1 = q2.
  Proof.
    intros tr m.
    induction m as [|m IH t|m IH t]; intros tlen q1 q2 Hfresh Htrail Hq1 Hq2 Heq.
    - destruct Htrail as [Hlen _]. simpl in Hlen. lia.
    - destruct (trail_of_snoc tr tlen m ⟨m, t⟩ t eq_refl Htrail) as (-> & Ht & Hprefix).
      destruct Hfresh as [Hfresh Hundef].
      assert (Hnew: forall (q: nat), q < PA.length m ->
                      extract (tget tr (PA.length m)) <> extract (tget tr q)).
      { intros q Hq Hext. rewrite Ht in Hext.
        apply (undef_atom m t (tget tr q) Hfresh Hundef).
        - now apply (trail_of_in tr (PA.length m)).
        - now symmetry. }
      destruct (Nat.eq_dec q1 (PA.length m)) as [-> | Hne1],
        (Nat.eq_dec q2 (PA.length m)) as [-> | Hne2].
      + reflexivity.
      + exfalso. apply (Hnew q2).
        * lia.
        * assumption.
      + exfalso. apply (Hnew q1).
        * lia.
        * now symmetry.
      + apply (IH (PA.length m)).
        * assumption.
        * assumption.
        * lia.
        * lia.
        * assumption.
    - destruct (trail_of_snoc tr tlen m ⟨m; t⟩ t eq_refl Htrail) as (-> & Ht & Hprefix).
      destruct Hfresh as [Hfresh Hundef].
      assert (Hnew: forall (q: nat), q < PA.length m ->
                      extract (tget tr (PA.length m)) <> extract (tget tr q)).
      { intros q Hq Hext. rewrite Ht in Hext.
        apply (undef_atom m t (tget tr q) Hfresh Hundef).
        - now apply (trail_of_in tr (PA.length m)).
        - now symmetry. }
      destruct (Nat.eq_dec q1 (PA.length m)) as [-> | Hne1],
        (Nat.eq_dec q2 (PA.length m)) as [-> | Hne2].
      + reflexivity.
      + exfalso. apply (Hnew q2).
        * lia.
        * assumption.
      + exfalso. apply (Hnew q1).
        * lia.
        * now symmetry.
      + apply (IH (PA.length m)).
        * assumption.
        * assumption.
        * lia.
        * lia.
        * assumption.
  Qed.

  (* The negation of a trail literal is false. *)
  Lemma trail_neg_false: forall (m: PA) (f: CNF) (x: Ctx) (q: nat),
    Core m f x -> q < tlen x -> l_eval m (¬tget (tr x) q) = Some false.
  Proof.
    intros m f x q Hcore Hq. rewrite l_eval_neg, fresh_in_true.
    - reflexivity.
    - apply Hcore.
    - apply (trail_of_in (tr x) (tlen x)).
      + apply Hcore.
      + assumption.
  Qed.
End Positions.

Section Analysis.
  (* The literals of the reason r, if it has a clause: input clause i, or reason clause j
     if it is one of the nr x of them. *)
  Definition reason_lits (x: Ctx) (r: Reason): option (list Lit) :=
  match r with
  | no_reason => None
  | input i   => tget (cmap x) i
  | learnt j  => if j <? nr x then Some (tget (rcl x) j) else None
  end.

  (* Whether y is the literal t, if there is one. *)
  Definition is_lit (t: option Lit) (y: Lit): bool :=
  match t with
  | Some t' => y =? t'
  | None    => false
  end.

  (* Mark y for the analysis and bump its atom in the heuristic (the C function mark). *)
  Definition mark (x: Ctx) (y: Lit): Ctx :=
    x <| mrk := tset (mrk x) (lit_key y) true |>
      <| hr := bump (hr x) (nvars x) (extract y) |>.

  (* Add the literals ys other than t that are not marked to the analysis at level d:
     mark them, count those of level d in pathc and append the others to the lower
     literals. Both stay below nvars x; at a literal that would pass it, stop with no
     count. *)
  Fixpoint add_lits (x: Ctx) (d: nat) (t: option Lit) (ys: list Lit) (pathc: nat):
    Ctx * option nat :=
  match ys with
  | []       => (x, Some pathc)
  | y :: ys' =>
    if is_lit t y || tget (mrk x) (lit_key y) then add_lits x d t ys' pathc
    else if Nat.eqb (level x y) d then
      if nvars x <=? pathc then (x, None)
      else add_lits (mark x y) d t ys' (S pathc)
    else if nvars x <=? length (lower x) then (x, None)
    else add_lits ((mark x y) <| lower := lower x ++ [y] |>) d t ys' pathc
  end.

  (* The position after the newest of the trail positions lo .. idx - 1 whose literal has
     its negation marked, or lo if there is none (n = idx - lo positions to look at). *)
  Fixpoint prev_marked (tr: Table Lit) (mk: Table bool) (lo idx n: nat): nat :=
  match n with
  | 0    => idx
  | S n' =>
    if tget mk (lit_key (¬tget tr (idx - 1))) then idx
    else prev_marked tr mk lo (idx - 1) n'
  end.

  (* Unmark the negations of the n trail literals below position idx. *)
  Fixpoint unmark_trail (tr: Table Lit) (mk: Table bool) (idx n: nat): Table bool :=
  match n with
  | 0    => mk
  | S n' => unmark_trail tr (tset mk (lit_key (¬tget tr (idx - 1))) false) (idx - 1) n'
  end.

  (* Unmark the negations of the trail literals at positions lo .. idx - 1 (the C
     function unmark_range). *)
  Definition unmark_range (x: Ctx) (idx lo: nat): Ctx :=
    x <| mrk := unmark_trail (tr x) (mrk x) idx (idx - lo) |>.

  (* The walk of the analysis at level d, whose last decision is at trail position lo:
     pathc literals of level d are marked, and the positions from idx on are done. Look
     for the newest marked one, t; if it is the last, ¬t is the literal to assert;
     otherwise resolve with the reason of t. Without a literal to assert, the marks of
     level d are cleared. *)
  Fixpoint analyze_loop (x: Ctx) (d lo fuel idx pathc: nat): Ctx * option Lit :=
  match fuel with
  | 0       => (unmark_range x idx lo, None)
  | S fuel' =>
    if Nat.eqb pathc 0 then (unmark_range x idx lo, None) else
    let idx1 := prev_marked (tr x) (mrk x) lo idx (idx - lo) in
    if idx1 <=? lo then (unmark_range x idx1 lo, None) else
    let t := tget (tr x) (idx1 - 1) in
    if Nat.eqb pathc 1 then (x, Some (¬t)) else
    let x1 := x <| mrk := tset (mrk x) (lit_key (¬t)) false |> in
    match reason_lits x (tget (rsn x) (extract t)) with
    | None    => (unmark_range x1 (idx1 - 1) lo, None)
    | Some ys =>
      match add_lits x1 d (Some t) ys (pathc - 1) with
      | (x2, Some p) => analyze_loop x2 d lo fuel' (idx1 - 1) p
      | (x2, None)   => (unmark_range x2 (idx1 - 1) lo, None)
      end
    end
  end.

  (* Analyse the conflict on clause i at level d, whose last decision is at trail position
     lo: the context with the marks, the lower literals of the analysed clause and the
     bumped heuristic, and the literal to assert, if any. *)
  Definition analyze (x: Ctx) (i d lo: nat): Ctx * option Lit :=
  match tget (cmap x) i with
  | None    => (x, None)
  | Some ls =>
    match add_lits x d None ls 0 with
    | (x1, Some p) => analyze_loop x1 d lo (tlen x1) (tlen x1) p
    | (x1, None)   => (unmark_range x1 (tlen x1) lo, None)
    end
  end.

  (* Unmark the literals ys, and find the highest level among them and mx. *)
  Fixpoint unmark_lits (x: Ctx) (mx: nat) (ys: list Lit): Ctx * nat :=
  match ys with
  | []       => (x, mx)
  | y :: ys' =>
    unmark_lits (x <| mrk := tset (mrk x) (lit_key y) false |>)
      (Nat.max mx (level x y)) ys'
  end.

  (* Unmark the lower literals, and find the highest level among them (0 if there is
     none) (the C function unmark_lower). *)
  Definition unmark_lower (x: Ctx): Ctx * nat := unmark_lits x 0 (lower x).

  (* x' is x with other marks, lower literals and heuristic, but the same literals to
     decide on: what the analysis changes. *)
  Definition Analysed (x x': Ctx): Prop :=
    x' = x <| mrk := mrk x' |> <| lower := lower x' |> <| hr := hr x' |> /\
    dlit (hr x') = dlit (hr x).

  (* Every context is analysed from itself. *)
  Lemma analysed_refl: forall (x: Ctx), Analysed x x.
  Proof.
    intros x. split.
    - destruct x. reflexivity.
    - reflexivity.
  Qed.

  (* Analysed is transitive. *)
  Lemma analysed_trans: forall (x1 x2 x3: Ctx),
    Analysed x1 x2 -> Analysed x2 x3 -> Analysed x1 x3.
  Proof.
    intros x1 x2 x3 [H12 Hd12] [H23 Hd23]. split.
    - rewrite H23 at 1. rewrite H12 at 1. reflexivity.
    - congruence.
  Qed.

  (* Marking only changes the marks and the heuristic, whose literals to decide on
     stay. *)
  Lemma mark_analysed: forall (x: Ctx) (y: Lit), Analysed x (mark x y).
  Proof.
    intros x y. split.
    - reflexivity.
    - apply bump_dlit.
  Qed.

  (* Adding literals only changes the marks, the lower literals and the heuristic. *)
  Lemma add_lits_analysed: forall (d: nat) (t: option Lit) (ys: list Lit) (x x': Ctx)
    (pathc: nat) (r: option nat),
    add_lits x d t ys pathc = (x', r) -> Analysed x x'.
  Proof.
    intros d t ys. induction ys as [|y ys IH]; intros x x' pathc r Hadd;
      cbn [add_lits] in Hadd.
    - injection Hadd as <- _. apply analysed_refl.
    - destruct (is_lit t y || tget (mrk x) (lit_key y)).
      + now apply IH in Hadd.
      + destruct (Nat.eqb (level x y) d).
        * destruct (nvars x <=? pathc).
          -- injection Hadd as <- _. apply analysed_refl.
          -- apply analysed_trans with (mark x y).
             ++ apply mark_analysed.
             ++ now apply IH in Hadd.
        * destruct (nvars x <=? length (lower x)).
          -- injection Hadd as <- _. apply analysed_refl.
          -- apply analysed_trans with (mark x y).
             ++ apply mark_analysed.
             ++ apply analysed_trans with ((mark x y) <| lower := lower x ++ [y] |>).
                ** split; reflexivity.
                ** now apply IH in Hadd.
  Qed.

  (* Unmarking a range only changes the marks. *)
  Lemma unmark_range_analysed: forall (x: Ctx) (idx lo: nat),
    Analysed x (unmark_range x idx lo).
  Proof.
    intros x idx lo. split; reflexivity.
  Qed.

  (* The walk of the analysis only changes the marks, the lower literals and the
     heuristic. *)
  Lemma analyze_loop_analysed: forall (d lo fuel idx pathc: nat) (x x': Ctx)
    (ou: option Lit),
    analyze_loop x d lo fuel idx pathc = (x', ou) -> Analysed x x'.
  Proof.
    intros d lo fuel. induction fuel as [|fuel IH]; intros idx pathc x x' ou Hloop;
      cbn [analyze_loop] in Hloop.
    - injection Hloop as <- _. apply unmark_range_analysed.
    - destruct (Nat.eqb pathc 0).
      + injection Hloop as <- _. apply unmark_range_analysed.
      + destruct (prev_marked (tr x) (mrk x) lo idx (idx - lo) <=? lo).
        * injection Hloop as <- _. apply unmark_range_analysed.
        * destruct (Nat.eqb pathc 1).
          -- injection Hloop as <- _. apply analysed_refl.
          -- set (x1 := x <| mrk := _ |>) in Hloop.
             assert (H1: Analysed x x1) by (split; reflexivity).
             destruct (reason_lits x _) as [ys|].
             ++ destruct (add_lits x1 d _ ys (pathc - 1)) as [x2 [p|]] eqn:Hadd.
                ** apply analysed_trans with x2.
                   --- apply analysed_trans with x1.
                       +++ assumption.
                       +++ now apply add_lits_analysed in Hadd.
                   --- now apply IH in Hloop.
                ** injection Hloop as <- _. apply analysed_trans with x2.
                   --- apply analysed_trans with x1.
                       +++ assumption.
                       +++ now apply add_lits_analysed in Hadd.
                   --- apply unmark_range_analysed.
             ++ injection Hloop as <- _. apply analysed_trans with x1.
                ** assumption.
                ** apply unmark_range_analysed.
  Qed.

  (* The analysis only changes the marks, the lower literals and the heuristic. *)
  Lemma analyze_analysed: forall (x x': Ctx) (i d lo: nat) (ou: option Lit),
    analyze x i d lo = (x', ou) -> Analysed x x'.
  Proof.
    intros x x' i d lo ou Han. unfold analyze in Han.
    destruct (tget (cmap x) i) as [ls|].
    - destruct (add_lits x d None ls 0) as [x1 [p|]] eqn:Hadd.
      + apply analysed_trans with x1.
        * now apply add_lits_analysed in Hadd.
        * now apply analyze_loop_analysed in Han.
      + injection Han as <- _. apply analysed_trans with x1.
        * now apply add_lits_analysed in Hadd.
        * apply unmark_range_analysed.
    - injection Han as <- _. apply analysed_refl.
  Qed.
End Analysis.

Section Marked.
  (* The negations of the trail literals at the n positions from lo on that are marked in
     mk, newest first: the literals of the current level of the analysed clause. *)
  Fixpoint cur_lits (tr: Table Lit) (mk: Table bool) (lo n: nat): list Lit :=
  match n with
  | 0    => []
  | S n' =>
    (if tget mk (lit_key (¬tget tr (lo + n'))) then [¬tget tr (lo + n')] else []) ++
      cur_lits tr mk lo n'
  end.

  (* The literals of cur_lits: the marked negations of the trail literals in range. *)
  Lemma cur_lits_in: forall (tr: Table Lit) (mk: Table bool) (lo n: nat) (y: Lit),
    In y (cur_lits tr mk lo n) <->
    exists (q: nat), lo <= q < lo + n /\ y = ¬tget tr q /\ tget mk (lit_key y) = true.
  Proof.
    intros tr mk lo n y. induction n as [|n IH]; cbn [cur_lits].
    - split.
      + intros [].
      + intros (q & Hq & _). lia.
    - rewrite in_app_iff, IH. split.
      + intros [Hy | (q & Hq & Hy & Hmk)].
        * destruct (tget mk (lit_key (¬tget tr (lo + n)))) eqn:Hmk.
          -- destruct Hy as [<- | []]. exists (lo + n). split.
             ++ lia.
             ++ now split.
          -- destruct Hy.
        * exists q. split.
          -- lia.
          -- now split.
      + intros (q & Hq & Hy & Hmk). destruct (Nat.eq_dec q (lo + n)) as [-> | Hne].
        * left. rewrite <- Hy, Hmk. now left.
        * right. exists q. split.
          -- lia.
          -- now split.
  Qed.

  (* Without marks at the n positions, there are none. *)
  Lemma cur_lits_none: forall (tr: Table Lit) (mk: Table bool) (lo n: nat),
    (forall (q: nat), lo <= q < lo + n -> tget mk (lit_key (¬tget tr q)) = false) ->
    cur_lits tr mk lo n = [].
  Proof.
    intros tr mk lo n. induction n as [|n IH]; cbn [cur_lits]; intros Hnone.
    - reflexivity.
    - rewrite Hnone by lia. apply IH. intros q Hq. apply Hnone. lia.
  Qed.

  (* The marks of literals that are not at the n positions do not matter. *)
  Lemma cur_lits_ext: forall (tr: Table Lit) (mk mk': Table bool) (lo n: nat),
    (forall (q: nat), lo <= q < lo + n ->
       tget mk' (lit_key (¬tget tr q)) = tget mk (lit_key (¬tget tr q))) ->
    cur_lits tr mk' lo n = cur_lits tr mk lo n.
  Proof.
    intros tr mk mk' lo n. induction n as [|n IH]; cbn [cur_lits]; intros Hsame.
    - reflexivity.
    - rewrite Hsame by lia. rewrite IH.
      + reflexivity.
      + intros q Hq. apply Hsame. lia.
  Qed.

  (* Positions above n do not count. *)
  Lemma cur_lits_top: forall (tr: Table Lit) (mk: Table bool) (lo n k: nat),
    (forall (q: nat), lo + n <= q < lo + n + k ->
       tget mk (lit_key (¬tget tr q)) = false) ->
    cur_lits tr mk lo (n + k) = cur_lits tr mk lo n.
  Proof.
    intros tr mk lo n k. induction k as [|k IH]; intros Hnone.
    - now rewrite Nat.add_0_r.
    - rewrite Nat.add_succ_r. cbn [cur_lits]. rewrite Hnone by lia. apply IH.
      intros q Hq. apply Hnone. lia.
  Qed.

  (* Marking the negation of the literal at a position adds it, if it was not marked and
     is at no other position. *)
  Lemma cur_lits_mark: forall (tr: Table Lit) (mk: Table bool) (lo n q0: nat) (y: Lit),
    lo <= q0 < lo + n -> y = ¬tget tr q0 ->
    (forall (q: nat), lo <= q < lo + n -> ¬tget tr q = y -> q = q0) ->
    tget mk (lit_key y) = false ->
    length (cur_lits tr (tset mk (lit_key y) true) lo n) =
      S (length (cur_lits tr mk lo n)) /\
    forall (z: Lit), In z (cur_lits tr (tset mk (lit_key y) true) lo n) <->
      z = y \/ In z (cur_lits tr mk lo n).
  Proof.
    intros tr mk lo n q0 y.
    induction n as [|n IH]; cbn [cur_lits]; intros Hq0 Hy Huniq Hmk.
    - lia.
    - destruct (Nat.eq_dec q0 (lo + n)) as [-> | Hne].
      + rewrite <- Hy, tget_tset_same, Hmk.
        assert (Hrest: cur_lits tr (tset mk (lit_key y) true) lo n =
                       cur_lits tr mk lo n).
        { apply cur_lits_ext. intros q Hq. rewrite tget_tset_other.
          - reflexivity.
          - intros Heq. apply lit_key_inj in Heq.
            assert (Hq_top: q = lo + n).
            { apply Huniq.
              - lia.
              - now symmetry. }
            lia. }
        rewrite Hrest. split.
        * reflexivity.
        * intros z. simpl. split.
          -- intros [<- | Hz].
             ++ now left.
             ++ now right.
          -- intros [<- | Hz].
             ++ now left.
             ++ now right.
      + assert (Hother: ¬tget tr (lo + n) <> y).
        { intros Heq. apply Hne. symmetry. apply Huniq.
          - lia.
          - assumption. }
        rewrite tget_tset_other by (intros Heq; apply lit_key_inj in Heq; congruence).
        assert (Hq0n: lo <= q0 < lo + n) by lia.
        assert (Huniq': forall (q: nat), lo <= q < lo + n -> ¬tget tr q = y -> q = q0).
        { intros q Hq. apply Huniq. lia. }
        destruct (IH Hq0n Hy Huniq' Hmk) as [Hlen Hin].
        rewrite !length_app, Hlen. split.
        * lia.
        * intros z. rewrite !in_app_iff, Hin. split.
          -- intros [Hz | [Hz | Hz]].
             ++ right. now left.
             ++ now left.
             ++ right. now right.
          -- intros [Hz | [Hz | Hz]].
             ++ right. now left.
             ++ now left.
             ++ right. now right.
  Qed.

  (* prev_marked stops at the newest marked position below idx, or at lo. *)
  Lemma prev_marked_spec: forall (tr: Table Lit) (mk: Table bool) (lo n idx: nat),
    idx = lo + n ->
    lo <= prev_marked tr mk lo idx n <= idx /\
    (forall (q: nat), prev_marked tr mk lo idx n <= q < idx ->
       tget mk (lit_key (¬tget tr q)) = false) /\
    (lo < prev_marked tr mk lo idx n ->
       tget mk (lit_key (¬tget tr (prev_marked tr mk lo idx n - 1))) = true).
  Proof.
    intros tr mk lo n. induction n as [|n IH]; intros idx Hidx; cbn [prev_marked].
    - splits.
      + lia.
      + intros q Hq. lia.
      + intros Hlt. lia.
    - destruct (tget mk (lit_key (¬tget tr (idx - 1)))) eqn:Htop.
      + splits.
        * lia.
        * intros q Hq. lia.
        * intros _. assumption.
      + assert (Hidx1: idx - 1 = lo + n) by lia.
        destruct (IH (idx - 1) Hidx1) as (Hrange & Hnone & Hmarked). splits.
        * lia.
        * intros q Hq. destruct (Nat.eq_dec q (idx - 1)) as [-> | Hne].
          -- assumption.
          -- apply Hnone. lia.
        * assumption.
  Qed.

  (* Unmarking only clears marks. *)
  Lemma unmark_trail_false: forall (tr: Table Lit) (mk: Table bool) (idx n k: nat),
    tget mk k = false -> tget (unmark_trail tr mk idx n) k = false.
  Proof.
    intros tr mk idx n. revert mk idx.
    induction n as [|n IH]; intros mk idx k Hk; cbn [unmark_trail].
    - assumption.
    - apply IH. rewrite tget_tset. now destruct (Nat.eq_dec _ k).
  Qed.

  (* The negations of the n literals below idx are unmarked. *)
  Lemma unmark_trail_cleared: forall (tr: Table Lit) (mk: Table bool) (idx n q: nat),
    idx - n <= q < idx -> n <= idx ->
    tget (unmark_trail tr mk idx n) (lit_key (¬tget tr q)) = false.
  Proof.
    intros tr mk idx n. revert mk idx.
    induction n as [|n IH]; intros mk idx q Hq Hn; cbn [unmark_trail].
    - lia.
    - destruct (Nat.eq_dec q (idx - 1)) as [-> | Hne].
      + apply unmark_trail_false. apply tget_tset_same.
      + apply IH; lia.
  Qed.
End Marked.

(* The reasons of an analysed context are those of the context. *)
Lemma reason_lits_analysed: forall (x: Ctx) (mk: Table bool) (lt: list Lit) (h: Heur)
  (r: Reason),
  reason_lits (x <| mrk := mk |> <| lower := lt |> <| hr := h |>) r = reason_lits x r.
Proof. reflexivity. Qed.

Section AnalysisSpec.
  (* The analysis runs on a context x that agrees with the trail ⟨m0; l0 ++ n0⟩: the last
     decision l0 is at position lo, and the current level is d. The reason clauses are
     entailed. *)
  Context (f: CNF) (x: Ctx) (m0 n0: PA) (l0: Lit).
  Hypothesis Hcore: Core ⟨m0; l0 ++ n0⟩ f x.
  Hypothesis Hnd: NoDecisions n0.
  Hypothesis Hslots: forall (j: nat), j < nr x -> Entailed f (tget (rcl x) j).

  Let m := ⟨m0; l0 ++ n0⟩.
  Let lo := PA.length m0.
  Let d := S (decisions m0).

  Let Htrace := core_traced Hcore.
  Let Htrail := core_trail Hcore.

  (* y is the negation of a trail literal of the current level below position idx. *)
  Definition OnLevel (idx: nat) (y: Lit): Prop :=
    exists (q: nat), lo <= q < idx /\ y = ¬tget (tr x) q.

  (* y can be added to the analysis with the positions from idx on done: it is false, and
     on the current level below idx if it is of level d. *)
  Definition Addable (idx: nat) (y: Lit): Prop :=
    l_eval m y = Some false /\ (level x y = d -> OnLevel idx y).

  (* The trail before the last decision. *)
  Lemma trail_m0:
    TrailOf (tr x) lo m0 /\ TraceOk (cmap x) (rsn x) (lvl x) (rcl x) (rps x) (nr x) m0.
  Proof.
    pose proof (trail_of_prefix (tr x) (tlen x) ⟨m0; l0⟩ n0 Htrail) as Hprefix.
    destruct (trail_of_snoc (tr x) _ m0 ⟨m0; l0⟩ l0 eq_refl Hprefix) as (_ & _ & Hm0).
    pose proof (trace_app ⟨m0; l0⟩ n0 Htrace) as [_ Hm0'].
    now split.
  Qed.

  (* The trail literals from lo on have level d. *)
  Lemma seg_level: forall (q: nat),
    lo <= q < tlen x -> level x (tget (tr x) q) = d.
  Proof.
    intros q Hq.
    apply (trace_last_level m0 n0 l0 _ Htrace).
    - assumption.
    - apply (seg_nth (tr x) (tlen x) m0); assumption.
  Qed.

  (* The trail literals before lo have a lower level. *)
  Lemma below_level: forall (q: nat),
    q < lo -> level x (tget (tr x) q) < d.
  Proof.
    intros q Hq. destruct trail_m0 as [Hm0 Htrace0].
    pose proof (trace_le m0 (tget (tr x) q) Htrace0
                  (trail_of_in (tr x) lo m0 q Hm0 Hq)).
    unfold d. lia.
  Qed.

  (* A false literal of level d has its negation on the last level. *)
  Lemma false_pos: forall (y: Lit),
    l_eval m y = Some false -> level x y = d -> OnLevel (tlen x) y.
  Proof.
    intros y Hy Hlv.
    assert (Hseg: ¬y = l0 \/ ¬y ∈ n0).
    { apply l_eval_false_in in Hy. unfold m in Hy.
      apply PA.in_app_iff in Hy as [Hin | [Heq | Hin]].
      - now right.
      - now left.
      - destruct trail_m0 as [_ Htrace0].
        pose proof (trace_le m0 (¬y) Htrace0 Hin) as Hle.
        rewrite extract_neg, Hlv in Hle. unfold d in Hle. lia. }
    destruct (seg_pos (tr x) (tlen x) m0 n0 l0 (¬y) Htrail Hseg) as (q & Hq & Hq_y).
    exists q. split.
    - assumption.
    - now rewrite Hq_y, Neg.involutive.
  Qed.

  (* The reason of a literal propagated on the last level, after its decision: an
     entailed clause with it, whose other literals have their negations before it on the
     trail. *)
  Lemma reason_spec: forall (q: nat) (ys: list Lit), lo < q < tlen x ->
    reason_lits x (tget (rsn x) (extract (tget (tr x) q))) = Some ys ->
    Entailed f ys /\ In (tget (tr x) q) ys /\
    forall (y: Lit), In y ys -> y <> tget (tr x) q ->
      exists (q': nat), q' < q /\ tget (tr x) q' = ¬y.
  Proof.
    intros q ys Hq Hys.
    destruct (reason_at (tr x) m0 n0 l0 (tlen x) q Htrace Htrail Hnd Hq)
      as (mq & Hmq & Hreason).
    assert (Hjust: forall (ls: list Lit), Justifies mq (tget (tr x) q) ls ->
                     In (tget (tr x) q) ls /\
                     forall (y: Lit), In y ls -> y <> tget (tr x) q ->
                       exists (q': nat), q' < q /\ tget (tr x) q' = ¬y).
    { intros ls [Hin Hrest]. split.
      - assumption.
      - intros y Hy Hne. apply (pos_of_in (tr x) q mq).
        + assumption.
        + apply l_eval_false_in. now apply Hrest. }
    destruct (tget (rsn x) (extract (tget (tr x) q))) as [|i|j];
      cbn [reason_lits ReasonOk] in Hys, Hreason.
    - discriminate.
    - destruct Hreason as (ls & Hi & Hls). rewrite Hi in Hys. injection Hys as ->. split.
      + apply entailed_clause_of. now apply (core_sound Hcore i).
      + now apply Hjust.
    - destruct Hreason as (Hj & _ & Hls). apply Nat.ltb_lt in Hj as Hj'.
      rewrite Hj' in Hys.
      injection Hys as <-. split.
      + now apply Hslots.
      + now apply Hjust.
  Qed.

  (* Different trail positions hold different atoms. *)
  Lemma distinct_pos: forall (q1 q2: nat), q1 < tlen x -> q2 < tlen x ->
    extract (tget (tr x) q1) = extract (tget (tr x) q2) -> q1 = q2.
  Proof.
    intros q1 q2 Hq1 Hq2 Heq. apply (fresh_positions (tr x) m (tlen x)).
    - apply Hcore.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
  Qed.

  (* The marks during the analysis with the positions from idx on done and the lower
     literals lt: a marked literal is one of lt, or the negation of a trail literal of
     the current level below idx; the literals of lt are marked, false and of a lower
     level. *)
  Record AMarks {idx: nat} {mk: Table bool} {lt: list Lit}: Prop := {
    am_marked: forall (y: Lit), tget mk (lit_key y) = true ->
      In y lt \/ OnLevel idx y;
    am_lower: forall (y: Lit), In y lt ->
      tget mk (lit_key y) = true /\ l_eval m y = Some false /\
      level x y <> d
  }.
  Arguments AMarks : clear implicits.

  (* Moreover pathc counts the marked literals of the current level below idx. *)
  Record AInv {idx: nat} {mk: Table bool} {lt: list Lit} {pathc: nat}: Prop := {
    ai_range: lo <= idx <= tlen x;
    ai_marks: AMarks idx mk lt;
    ai_count: pathc = length (cur_lits (tr x) mk lo (idx - lo))
  }.
  Arguments AInv : clear implicits.

  (* The analysed clause: the lower literals and the marked ones of the current level
     below idx. *)
  Definition aclause (idx: nat) (mk: Table bool) (lt: list Lit): list Lit :=
    lt ++ cur_lits (tr x) mk lo (idx - lo).

  (* What adding the literals ys other than t to the analysis in the state of mk and lt
     gives in x' with the result r (the conclusion of add_lits_spec): the marks stay as
     they should, the analysed clause only grows, and when no bound was passed
     (r = Some p) the invariant holds with the count p and the analysed clause contains
     ys. *)
  Definition AddOk (idx: nat) (mk: Table bool) (lt: list Lit) (t: option Lit)
    (ys: list Lit) (x': Ctx) (r: option nat): Prop :=
    AMarks idx (mrk x') (lower x') /\
    incl (aclause idx mk lt) (aclause idx (mrk x') (lower x')) /\
    (forall (p: nat), r = Some p -> AInv idx (mrk x') (lower x') p /\
       forall (y: Lit), In y ys -> is_lit t y = false ->
         In y (aclause idx (mrk x') (lower x'))).

  (* Stopping at a bound, with the marks and the lower literals as they are. *)
  Lemma add_ok_stop: forall (idx: nat) (mk: Table bool) (lt: list Lit) (pathc: nat)
    (h: Heur) (t: option Lit) (ys: list Lit),
    AInv idx mk lt pathc ->
    AddOk idx mk lt t ys (x <| mrk := mk |> <| lower := lt |> <| hr := h |>) None.
  Proof.
    intros idx mk lt pathc h t ys Hinv. unfold AddOk. splits.
    - apply Hinv.
    - easy.
    - intros p Hp. discriminate.
  Qed.

  (* The step of the induction: if handling y gives the marks mk1 and the lower literals
     lt1, the analysed clause only grows and contains y (unless y is t), then what adding
     ys from there gives is what adding y :: ys gives. *)
  Lemma add_ok_cons: forall (idx: nat) (mk mk1: Table bool) (lt lt1: list Lit)
    (t: option Lit) (y: Lit) (ys: list Lit) (x': Ctx) (r: option nat),
    incl (aclause idx mk lt) (aclause idx mk1 lt1) ->
    (is_lit t y = false -> In y (aclause idx mk1 lt1)) ->
    AddOk idx mk1 lt1 t ys x' r -> AddOk idx mk lt t (y :: ys) x' r.
  Proof.
    intros idx mk mk1 lt lt1 t y ys x' r Hgrow Hy (Hmarks & Hmono & Hsome).
    unfold AddOk. splits.
    - assumption.
    - intros z Hz. apply Hmono. now apply Hgrow.
    - intros p Hp. destruct (Hsome p Hp) as [Hinv Hin]. split.
      + assumption.
      + intros z [<- | Hz] Hz_t.
        * apply Hmono. now apply Hy.
        * now apply Hin.
  Qed.

  (* A marked literal is in the analysed clause. *)
  Lemma marked_in_aclause: forall (idx: nat) (mk: Table bool) (lt: list Lit) (y: Lit),
    AMarks idx mk lt -> tget mk (lit_key y) = true -> In y (aclause idx mk lt).
  Proof.
    intros idx mk lt y Hmarks Hy. apply in_or_app.
    destruct (am_marked Hmarks y Hy) as [Hlt | (q & Hq & Hy_q)].
    - now left.
    - right. apply cur_lits_in. exists q. split.
      + lia.
      + now split.
  Qed.

  (* Marking an unmarked literal y of the current level below idx counts it: the
     invariant holds with one more, and the analysed clause grows by y. *)
  Lemma ainv_mark_cur: forall (idx: nat) (mk: Table bool) (lt: list Lit) (pathc: nat)
    (y: Lit),
    AInv idx mk lt pathc -> OnLevel idx y -> tget mk (lit_key y) = false ->
    AInv idx (tset mk (lit_key y) true) lt (S pathc) /\
    incl (aclause idx mk lt) (aclause idx (tset mk (lit_key y) true) lt) /\
    In y (aclause idx (tset mk (lit_key y) true) lt).
  Proof.
    intros idx mk lt pathc y [Hrange [Hmarked Hlower] Hcount] (q0 & Hq0 & Hy_q0) Hy_mk.
    (* y is the negation of the trail literal at q0 only *)
    assert (Huniq: forall (q: nat), lo <= q < lo + (idx - lo) ->
                     ¬tget (tr x) q = y -> q = q0).
    { intros q Hq Heq. apply distinct_pos.
      - lia.
      - lia.
      - rewrite <- (extract_neg (tget (tr x) q)).
        rewrite <- (extract_neg (tget (tr x) q0)), Heq, <- Hy_q0. reflexivity. }
    assert (Hq0_range: lo <= q0 < lo + (idx - lo)) by lia.
    destruct (cur_lits_mark (tr x) mk lo (idx - lo) q0 y Hq0_range Hy_q0 Huniq Hy_mk)
      as [Hlen Hin].
    splits.
    - split.
      + assumption.
      + split.
        * intros z Hz. rewrite tget_tset in Hz.
          destruct (Nat.eq_dec (lit_key y) (lit_key z)) as [Heq | Hne].
          -- apply lit_key_inj in Heq as <-. right. exists q0. split.
             ++ lia.
             ++ assumption.
          -- now apply Hmarked.
        * intros z Hz. destruct (Hlower z Hz) as (Hz_mk & Hz_false & Hz_lv). split.
          -- rewrite tget_tset. now destruct (Nat.eq_dec (lit_key y) (lit_key z)).
          -- now split.
      + now rewrite Hlen, Hcount.
    - intros z Hz. unfold aclause in Hz |- *. apply in_app_iff in Hz as [Hz | Hz].
      + apply in_or_app. now left.
      + apply in_or_app. right. apply Hin. now right.
    - unfold aclause. apply in_or_app. right. apply Hin. now left.
  Qed.

  (* Marking a false literal y of a lower level adds it to the lower literals: the
     invariant holds with y added to lt, and the analysed clause grows by y. *)
  Lemma ainv_mark_lower: forall (idx: nat) (mk: Table bool) (lt: list Lit)
    (pathc: nat) (y: Lit),
    AInv idx mk lt pathc -> l_eval m y = Some false -> level x y <> d ->
    AInv idx (tset mk (lit_key y) true) (lt ++ [y]) pathc /\
    incl (aclause idx mk lt) (aclause idx (tset mk (lit_key y) true) (lt ++ [y])) /\
    In y (aclause idx (tset mk (lit_key y) true) (lt ++ [y])).
  Proof.
    intros idx mk lt pathc y [Hrange [Hmarked Hlower] Hcount] Hy_false Hlv.
    (* y is not the negation of a literal of the current level: the count stays *)
    assert (Hnot_cur: forall (q: nat), lo <= q < lo + (idx - lo) ->
              tget (tset mk (lit_key y) true) (lit_key (¬tget (tr x) q)) =
              tget mk (lit_key (¬tget (tr x) q))).
    { intros q Hq. rewrite tget_tset_other.
      - reflexivity.
      - intros Heq. apply lit_key_inj in Heq. apply Hlv.
        rewrite Heq, extract_neg. apply seg_level. lia. }
    pose proof (cur_lits_ext (tr x) mk (tset mk (lit_key y) true) lo (idx - lo)
                  Hnot_cur) as Hsame.
    splits.
    - split.
      + assumption.
      + split.
        * intros z Hz. rewrite tget_tset in Hz.
          destruct (Nat.eq_dec (lit_key y) (lit_key z)) as [Heq | Hne].
          -- apply lit_key_inj in Heq as <-. left. apply in_or_app. right. now left.
          -- destruct (Hmarked z Hz) as [Hlt | Hpos].
             ++ left. apply in_or_app. now left.
             ++ now right.
        * intros z Hz. apply in_app_iff in Hz as [Hz | [<- | []]].
          -- destruct (Hlower z Hz) as (Hz_mk & Hz_false & Hz_lv). split.
             ++ rewrite tget_tset. now destruct (Nat.eq_dec (lit_key y) (lit_key z)).
             ++ now split.
          -- split.
             ++ apply tget_tset_same.
             ++ now split.
      + now rewrite Hsame.
    - intros z Hz. unfold aclause in Hz |- *. rewrite Hsame.
      apply in_app_iff in Hz as [Hz | Hz].
      + apply in_or_app. left. apply in_or_app. now left.
      + apply in_or_app. now right.
    - unfold aclause. apply in_or_app. left. apply in_or_app. right. now left.
  Qed.

  (* Adding the addable literals ys other than t: the marks stay as they should, the
     analysed clause only grows, and when no bound was passed it contains ys too, with
     the count right. By induction on ys: a literal that is t or marked is in the
     analysed clause already; one of the current level is marked and counted
     (ainv_mark_cur), one of a lower level marked and kept in lt (ainv_mark_lower),
     unless that would pass the bound nvars x; add_ok_cons then joins it to the rest. *)
  Lemma add_lits_spec: forall (ys: list Lit) (t: option Lit) (idx: nat)
    (mk: Table bool) (lt: list Lit) (h: Heur) (pathc: nat) (x': Ctx) (r: option nat),
    AInv idx mk lt pathc ->
    (forall (y: Lit), In y ys -> is_lit t y = false -> Addable idx y) ->
    add_lits (x <| mrk := mk |> <| lower := lt |> <| hr := h |>) d t ys pathc = (x', r) ->
    AMarks idx (mrk x') (lower x') /\
    incl (aclause idx mk lt) (aclause idx (mrk x') (lower x')) /\
    (forall (p: nat), r = Some p -> AInv idx (mrk x') (lower x') p /\
       forall (y: Lit), In y ys -> is_lit t y = false ->
         In y (aclause idx (mrk x') (lower x'))).
  Proof.
    intros ys t.
    induction ys as [|y ys IH]; intros idx mk lt h pathc x' r Hinv Hys Hadd;
      cbn [add_lits set_mrk set_lower set_hr mrk lower lvl nvars] in Hadd.
    (* No literal left: the count stays *)
    - injection Hadd as <- <-. splits.
      + apply Hinv.
      + easy.
      + intros p Hp. injection Hp as <-. split.
        * assumption.
        * intros y [].
    - assert (Hys': forall (z: Lit), In z ys -> is_lit t z = false -> Addable idx z).
      { intros z Hz. apply Hys. now right. }
      destruct (is_lit t y || tget mk (lit_key y)) eqn:Hskip.
      (* y is t, or marked already: it is in the analysed clause *)
      + apply (add_ok_cons idx mk mk lt lt).
        * easy.
        * intros Hy_t. rewrite Hy_t in Hskip. cbn [orb] in Hskip.
          apply marked_in_aclause.
          -- apply Hinv.
          -- assumption.
        * apply (IH idx mk lt h pathc x' r Hinv Hys' Hadd).
      + apply orb_false_iff in Hskip as [Hy_t Hy_mk].
        destruct (Hys y (or_introl eq_refl) Hy_t) as [Hy_false Hy_pos].
        destruct (Nat.eqb (level x y) d) eqn:Hlv.
        (* y is of the current level: count it, unless the count would pass nvars x *)
        * apply Nat.eqb_eq in Hlv. destruct (nvars x <=? pathc).
          -- injection Hadd as <- <-. now apply (add_ok_stop idx mk lt pathc).
          -- destruct (ainv_mark_cur idx mk lt pathc y Hinv (Hy_pos Hlv) Hy_mk)
               as (Hinv1 & Hgrow & Hy_in).
             apply (add_ok_cons idx mk (tset mk (lit_key y) true) lt lt).
             ++ assumption.
             ++ intros _. assumption.
             ++ apply (IH idx _ lt _ (S pathc) x' r Hinv1 Hys' Hadd).
        (* y is of a lower level: keep it, unless lt would get longer than nvars x *)
        * apply Nat.eqb_neq in Hlv. destruct (nvars x <=? length lt).
          -- injection Hadd as <- <-. now apply (add_ok_stop idx mk lt pathc).
          -- destruct (ainv_mark_lower idx mk lt pathc y Hinv Hy_false Hlv)
               as (Hinv1 & Hgrow & Hy_in).
             apply (add_ok_cons idx mk (tset mk (lit_key y) true) lt (lt ++ [y])).
             ++ assumption.
             ++ intros _. assumption.
             ++ apply (IH idx _ (lt ++ [y]) _ pathc x' r Hinv1 Hys' Hadd).
  Qed.

  (* Without a literal to assert, clearing the marks of the current level below idx
     leaves only those of lt. *)
  Lemma fail_marks: forall (idx: nat) (mk: Table bool) (lt: list Lit) (y: Lit),
    AMarks idx mk lt -> lo <= idx ->
    tget (unmark_trail (tr x) mk idx (idx - lo)) (lit_key y) = true -> In y lt.
  Proof.
    intros idx mk lt y [Hmarked _] Hidx Hy.
    destruct (tget mk (lit_key y)) eqn:Hmk.
    - destruct (Hmarked y Hmk) as [Hlt | (q & Hq & ->)].
      + assumption.
      + rewrite unmark_trail_cleared in Hy.
        * discriminate.
        * lia.
        * lia.
    - rewrite unmark_trail_false in Hy.
      + discriminate.
      + assumption.
  Qed.

  (* What the analysis gives: marked are only the literals of lt and the literal to
     assert; the literals of lt are false and of a lower level; and with a literal u to
     assert, the clause of lt and u is entailed, and u is the negation of a literal of
     the last level. *)
  Definition AResult (ou: option Lit) (mk: Table bool) (lt: list Lit): Prop :=
    (forall (y: Lit), tget mk (lit_key y) = true -> In y lt \/ ou = Some y) /\
    (forall (y: Lit), In y lt ->
       l_eval m y = Some false /\ level x y <> d) /\
    (forall (u: Lit), ou = Some u ->
       Entailed f (lt ++ [u]) /\ OnLevel (tlen x) u).

  (* Giving up the analysis. *)
  Lemma aresult_fail: forall (idx: nat) (mk: Table bool) (lt: list Lit),
    AMarks idx mk lt -> lo <= idx ->
    AResult None (unmark_trail (tr x) mk idx (idx - lo)) lt.
  Proof.
    intros idx mk lt Hmarks Hidx. split.
    - intros y Hy. left. now apply (fail_marks idx mk).
    - split.
      + intros y Hy. destruct (am_lower Hmarks y Hy) as (_ & Hfalse & Hlv).
        now split.
      + intros u Hu. discriminate.
  Qed.

  (* The marks stay right with the bound lowered from idx to idx1, when the positions
     idx1 .. idx - 1 are not marked. *)
  Lemma amarks_shrink: forall (idx idx1: nat) (mk: Table bool) (lt: list Lit),
    AMarks idx mk lt ->
    (forall (q: nat), idx1 <= q < idx -> tget mk (lit_key (¬tget (tr x) q)) = false) ->
    AMarks idx1 mk lt.
  Proof.
    intros idx idx1 mk lt Hmarks Hnone. split.
    - intros y Hy. destruct (am_marked Hmarks y Hy) as [Hlt | (q & Hq & ->)].
      + now left.
      + right. exists q. split.
        * destruct (Nat.lt_ge_cases q idx1) as [Hlt | Hge].
          -- lia.
          -- rewrite Hnone in Hy.
             ++ discriminate.
             ++ lia.
        * reflexivity.
    - apply Hmarks.
  Qed.

  (* When idx1 - 1 is the newest marked position below idx: the marks are right below
     idx1, and the marked literals of the current level below idx are the negation of
     the literal at idx1 - 1 and those below it. *)
  Lemma newest_marked: forall (idx idx1: nat) (mk: Table bool) (lt: list Lit),
    AMarks idx mk lt -> lo <= idx1 <= idx ->
    (forall (q: nat), idx1 <= q < idx -> tget mk (lit_key (¬tget (tr x) q)) = false) ->
    lo < idx1 -> tget mk (lit_key (¬tget (tr x) (idx1 - 1))) = true ->
    AMarks idx1 mk lt /\
    cur_lits (tr x) mk lo (idx - lo) =
      (¬tget (tr x) (idx1 - 1)) :: cur_lits (tr x) mk lo (idx1 - 1 - lo).
  Proof.
    intros idx idx1 mk lt Hmarks Hrange1 Hnone Hlo Htop. split.
    - now apply (amarks_shrink idx).
    - replace (idx - lo) with (S (idx1 - 1 - lo) + (idx - idx1)) by lia.
      rewrite cur_lits_top.
      + cbn [cur_lits]. replace (lo + (idx1 - 1 - lo)) with (idx1 - 1) by lia.
        now rewrite Htop.
      + intros q Hq. apply Hnone. lia.
  Qed.

  (* When ¬t, of position q on the current level, is the only marked literal of that
     level below S q, and the clause of lt and ¬t is entailed, ¬t is the literal to
     assert. *)
  Lemma aresult_assert: forall (q: nat) (mk: Table bool) (lt: list Lit),
    lo <= q < tlen x -> AMarks (S q) mk lt -> cur_lits (tr x) mk lo (q - lo) = [] ->
    Entailed f (lt ++ [¬tget (tr x) q]) -> AResult (Some (¬tget (tr x) q)) mk lt.
  Proof.
    intros q mk lt Hq Hmarks Hempty Hent. unfold AResult. splits.
    - intros y Hy. destruct (am_marked Hmarks y Hy) as [Hlt | (q' & Hq' & ->)].
      + now left.
      + right. destruct (Nat.eq_dec q' q) as [-> | Hne].
        * reflexivity.
        (* another one would be a marked literal below q *)
        * exfalso.
          assert (Hin: In (¬tget (tr x) q') (cur_lits (tr x) mk lo (q - lo))).
          { apply cur_lits_in. exists q'. split.
            - lia.
            - now split. }
          rewrite Hempty in Hin. destruct Hin.
    - intros y Hy. destruct (am_lower Hmarks y Hy) as (_ & Hfalse & Hlv). now split.
    - intros u Hu. injection Hu as <-. split.
      + assumption.
      + exists q. split.
        * lia.
        * reflexivity.
  Qed.

  (* Unmarking ¬t, of position q on the current level, leaves the marked literals below
     q. *)
  Lemma cur_lits_unmark_top: forall (q: nat) (mk: Table bool), q < tlen x ->
    cur_lits (tr x) (tset mk (lit_key (¬tget (tr x) q)) false) lo (q - lo) =
      cur_lits (tr x) mk lo (q - lo).
  Proof.
    intros q mk Hq. apply cur_lits_ext. intros q' Hq'. rewrite tget_tset_other.
    - reflexivity.
    - intros Heq. apply lit_key_inj in Heq. apply (f_equal Neg.neg) in Heq.
      rewrite !Neg.involutive in Heq. assert (Hsame: q' = q).
      + apply distinct_pos.
        * lia.
        * assumption.
        * now rewrite Heq.
      + lia.
  Qed.

  (* Unmarking ¬t, of position q on the current level, lowers the bound of the marks
     from S q to q. *)
  Lemma amarks_unmark_top: forall (q: nat) (mk: Table bool) (lt: list Lit),
    lo <= q < tlen x -> AMarks (S q) mk lt ->
    AMarks q (tset mk (lit_key (¬tget (tr x) q)) false) lt.
  Proof.
    intros q mk lt Hq Hmarks. split.
    - intros y Hy. rewrite tget_tset in Hy.
      destruct (Nat.eq_dec (lit_key (¬tget (tr x) q)) (lit_key y)) as [Heq | Hne].
      + discriminate.
      + destruct (am_marked Hmarks y Hy) as [Hlt | (q' & Hq' & ->)].
        * now left.
        * right. exists q'. split.
          -- destruct (Nat.eq_dec q' q) as [-> | Hne'].
             ++ exfalso. now apply Hne.
             ++ lia.
          -- reflexivity.
    (* the lower literals are not of the current level, so not ¬t *)
    - intros y Hy. destruct (am_lower Hmarks y Hy) as (Hy_mk & Hfalse & Hlv). split.
      + rewrite tget_tset_other.
        * assumption.
        * intros Heq. apply lit_key_inj in Heq. apply Hlv.
          rewrite <- Heq, extract_neg. apply seg_level. lia.
      + now split.
  Qed.

  (* Resolving away ¬t, of position q on the current level: unmarking it gives the
     invariant below q, with a count one less. *)
  Lemma ainv_unmark_top: forall (q: nat) (mk: Table bool) (lt: list Lit) (pathc: nat),
    lo <= q < tlen x -> AMarks (S q) mk lt ->
    pathc = S (length (cur_lits (tr x) mk lo (q - lo))) ->
    AInv q (tset mk (lit_key (¬tget (tr x) q)) false) lt (pathc - 1).
  Proof.
    intros q mk lt pathc Hq Hmarks Hcount. split.
    - lia.
    - now apply amarks_unmark_top.
    - rewrite cur_lits_unmark_top by lia. lia.
  Qed.

  (* The literals of the reason ys of the literal t at position q, other than t, are
     addable below q: their negations are on the trail before t. *)
  Lemma reason_addable: forall (q: nat) (ys: list Lit), lo < q < tlen x ->
    reason_lits x (tget (rsn x) (extract (tget (tr x) q))) = Some ys ->
    forall (y: Lit), In y ys -> is_lit (Some (tget (tr x) q)) y = false -> Addable q y.
  Proof.
    intros q ys Hq Hreason y Hy Hy_t. cbn [is_lit] in Hy_t. apply Lit.eqb_neq in Hy_t.
    destruct (reason_spec q ys Hq Hreason) as (_ & _ & Hys_pos).
    destruct (Hys_pos y Hy Hy_t) as (q' & Hq' & Hq'y). split.
    - rewrite <- (Neg.involutive y), <- Hq'y. apply (trail_neg_false m f x).
      + apply Hcore.
      + lia.
    (* of level d, ¬y is at or after the decision at lo *)
    - intros Hlv. exists q'. split.
      + split.
        * destruct (Nat.lt_ge_cases q' lo) as [Hlt | Hge].
          -- exfalso. pose proof (below_level q' Hlt) as Hlow.
             rewrite Hq'y, extract_neg, Hlv in Hlow. lia.
          -- assumption.
        * assumption.
      + now rewrite Hq'y, Neg.involutive.
  Qed.

  (* Resolution on the analysed clause: if ¬t, at position q, is its newest literal of
     the current level, and ys is an entailed clause with t, then the analysed clause
     below q is entailed once it has the literals of ys other than t. *)
  Lemma aclause_resolve: forall (idx q: nat) (mk mk': Table bool) (lt lt' ys: list Lit),
    Entailed f (aclause idx mk lt) -> Entailed f ys ->
    cur_lits (tr x) mk lo (idx - lo) =
      (¬tget (tr x) q) :: cur_lits (tr x) mk lo (q - lo) ->
    incl (aclause q mk lt) (aclause q mk' lt') ->
    (forall (y: Lit), In y ys -> y <> tget (tr x) q -> In y (aclause q mk' lt')) ->
    Entailed f (aclause q mk' lt').
  Proof.
    intros idx q mk mk' lt lt' ys Hent Hys Hnewest Hmono Hys_in.
    apply (entailed_resolve f (aclause idx mk lt) ys _ (tget (tr x) q)).
    - assumption.
    - assumption.
    - intros y Hy Hne. apply Hmono. unfold aclause in Hy |- *. rewrite Hnewest in Hy.
      apply in_app_iff in Hy as [Hy | [Hy | Hy]].
      + apply in_or_app. now left.
      + exfalso. apply Hne. now symmetry.
      + apply in_or_app. now right.
    - assumption.
  Qed.

  (* The walk of the analysis, from a state of the invariant whose analysed clause is
     entailed. By induction on the fuel: each step finds the newest marked literal ¬t of
     the current level, at position q (newest_marked). If it is the only one, it is
     asserted (aresult_assert); otherwise ¬t is unmarked (ainv_unmark_top) and the
     literals of the reason of t are added (add_lits_spec), which keeps the analysed
     clause entailed (aclause_resolve), and the walk goes on below q. Out of fuel,
     without a marked literal, a reason or room, it gives up (aresult_fail). *)
  Lemma analyze_loop_spec: forall (fuel idx: nat) (mk: Table bool) (lt: list Lit)
    (h: Heur) (pathc: nat) (x': Ctx) (ou: option Lit),
    AInv idx mk lt pathc -> Entailed f (aclause idx mk lt) -> idx - lo <= fuel ->
    analyze_loop (x <| mrk := mk |> <| lower := lt |> <| hr := h |>) d lo fuel idx pathc =
      (x', ou) ->
    AResult ou (mrk x') (lower x').
  Proof.
    intros fuel.
    induction fuel as [|fuel IH]; intros idx mk lt h pathc x' ou Hinv Hent Hfuel Hloop;
      cbn [analyze_loop] in Hloop; rewrite ?reason_lits_analysed in Hloop;
      cbn [set_mrk set_lower set_hr mrk lower tr rsn] in Hloop.
    (* Out of fuel: give up *)
    - injection Hloop as <- <-. apply (aresult_fail idx); apply Hinv.
    - pose proof Hinv as [Hrange Hmarks Hcount].
      destruct (Nat.eqb pathc 0) eqn:Hzero.
      (* No marked literal of the current level is counted: give up *)
      + injection Hloop as <- <-. now apply (aresult_fail idx).
      + assert (Hidx: idx = lo + (idx - lo)) by lia.
        destruct (prev_marked_spec (tr x) mk lo (idx - lo) idx Hidx)
          as (Hrange1 & Hnone & Htop).
        set (idx1 := prev_marked (tr x) mk lo idx (idx - lo)) in *.
        destruct (idx1 <=? lo) eqn:Hlo.
        (* No marked literal is left: give up *)
        * injection Hloop as <- <-. apply (aresult_fail idx1).
          -- now apply (amarks_shrink idx).
          -- lia.
        (* ¬t, at position q = idx1 - 1, is the newest marked literal *)
        * apply Nat.leb_gt in Hlo. specialize (Htop Hlo).
          destruct (newest_marked idx idx1 mk lt Hmarks Hrange1 Hnone Hlo Htop)
            as [Hmarks1 Hnewest].
          set (q := idx1 - 1) in *.
          assert (Hq: lo <= q < tlen x) by lia.
          replace idx1 with (S q) in Hmarks1 by lia.
          rewrite Hnewest in Hcount. simpl in Hcount.
          destruct (Nat.eqb pathc 1) eqn:Hone.
          (* ¬t is the only one: assert it *)
          -- injection Hloop as <- <-. apply Nat.eqb_eq in Hone.
             assert (Hempty: cur_lits (tr x) mk lo (q - lo) = []).
             { apply length_zero_iff_nil. lia. }
             apply aresult_assert.
             ++ assumption.
             ++ assumption.
             ++ assumption.
             ++ unfold aclause in Hent. rewrite Hnewest, Hempty in Hent. assumption.
          (* Resolve with the reason of t *)
          -- apply Nat.eqb_neq in Hone.
             (* t is not the decision, which would be the only marked literal *)
             assert (Hq_lo: lo < q).
             { destruct (Nat.eq_dec q lo) as [Heq | Hne].
               - exfalso. replace (q - lo) with 0 in Hcount by lia. simpl in Hcount. lia.
               - lia. }
             assert (Hq_range: lo < q < tlen x) by lia.
             pose proof (ainv_unmark_top q mk lt pathc Hq Hmarks1 Hcount) as Hinv1.
             destruct (reason_lits x (tget (rsn x) (extract (tget (tr x) q))))
               as [ys|] eqn:Hreason.
             ++ destruct (reason_spec q ys Hq_range Hreason) as (Hys_ent & _ & _).
                destruct (add_lits _ d (Some (tget (tr x) q)) ys (pathc - 1))
                  as [x2 r] eqn:Hadd.
                destruct (add_lits_spec ys (Some (tget (tr x) q)) q
                            (tset mk (lit_key (¬tget (tr x) q)) false) lt h (pathc - 1)
                            x2 r Hinv1 (reason_addable q ys Hq_range Hreason) Hadd)
                  as (Hmarks2 & Hmono & Hsome).
                apply add_lits_analysed in Hadd as [Hx2 _]. rewrite Hx2 in Hloop.
                destruct r as [p|].
                (* The literals are added: go on below q with the resolvent *)
                ** destruct (Hsome p eq_refl) as [Hinv2 Hys_in].
                   apply (IH q (mrk x2) (lower x2) (hr x2) p x' ou Hinv2).
                   --- apply (aclause_resolve idx q mk (mrk x2) lt (lower x2) ys).
                       +++ assumption.
                       +++ assumption.
                       +++ assumption.
                       +++ intros y Hy. apply Hmono. unfold aclause in Hy |- *.
                           now rewrite cur_lits_unmark_top by lia.
                       +++ intros y Hy Hne. apply Hys_in.
                           *** assumption.
                           *** cbn [is_lit]. now apply Lit.eqb_neq.
                   --- lia.
                   --- assumption.
                (* No room: give up *)
                ** injection Hloop as <- <-. apply (aresult_fail q).
                   --- assumption.
                   --- lia.
             (* t has no reason clause: give up *)
             ++ injection Hloop as <- <-. apply (aresult_fail q).
                ** apply Hinv1.
                ** lia.
  Qed.

  (* The analysis of a false clause of x, with the heuristic h0 and no lower literals
     yet, gives AResult. *)
  Lemma analyze_spec: forall (h0: Heur) (i: nat) (x': Ctx) (ou: option Lit),
    ClauseFalse x i -> Unmarked (mrk x) -> lower x = [] ->
    analyze (x <| hr := h0 |>) i d lo = (x', ou) -> AResult ou (mrk x') (lower x').
  Proof.
    intros h0 i x' ou [ls [Hi Hfalse]] Hunmarked Hlow Han.
    assert (Hx: x <| hr := h0 |> = x <| mrk := mrk x |> <| lower := [] |> <| hr := h0 |>).
    { rewrite <- Hlow. destruct x. reflexivity. }
    rewrite Hx in Han. unfold analyze in Han.
    cbn [set_mrk set_lower set_hr cmap tlen] in Han. rewrite Hi in Han.
    assert (Hlen: lo < tlen x).
    { destruct Htrail as [Hlen _]. rewrite Hlen, trail_lits_length. unfold m.
      rewrite pa_length_app. simpl. unfold lo. lia. }
    assert (Hinv0: AInv (tlen x) (mrk x) [] 0).
    { split.
      - lia.
      - split.
        + intros y Hy. now rewrite Hunmarked in Hy.
        + intros y [].
      - rewrite cur_lits_none.
        + reflexivity.
        + intros q _. apply Hunmarked. }
    assert (Hpre: forall (y: Lit), In y ls -> is_lit None y = false ->
              Addable (tlen x) y).
    { intros y Hy _. assert (Hy_false: l_eval m y = Some false).
      { rewrite <- (core_vals Hcore). now apply Hfalse. }
      split.
      - assumption.
      - intros Hlv. now apply false_pos. }
    destruct (add_lits _ d None ls 0) as [x1 r] eqn:Hadd.
    destruct (add_lits_spec ls None (tlen x) (mrk x) [] h0 0 x1 r Hinv0 Hpre Hadd)
      as (Hmarks1 & _ & Hsome).
    apply add_lits_analysed in Hadd as [Hx1 _]. rewrite Hx1 in Han.
    destruct r as [p|].
    - destruct (Hsome p eq_refl) as [Hinv1 Hls_in].
      apply (analyze_loop_spec (tlen x) (tlen x) (mrk x1) (lower x1) (hr x1) p x' ou
               Hinv1).
      + apply (entailed_incl f ls).
        * apply entailed_clause_of. now apply (core_sound Hcore i).
        * intros y Hy. now apply Hls_in.
      + lia.
      + assumption.
    - injection Han as <- <-. apply (aresult_fail (tlen x)).
      + assumption.
      + lia.
  Qed.
End AnalysisSpec.

Section Reasons.
  (* The number of literals of the reason clauses. *)
  Fixpoint reasons_size (rcl: Table (list Lit)) (n: nat): nat :=
  match n with
  | 0    => 0
  | S n' => reasons_size rcl n' + length (tget rcl n')
  end.

  (* The reason clauses of x and c, as reason clause nr x for the literal at trail
     position tlen x. *)
  Definition add_reason (x: Ctx) (c: list Lit): Ctx :=
  mkCtx (vals x) (cmap x) (wls x) (tr x) (tlen x) (qhead x) (shorts x) (alls x) (nlits x)
    (cur x) (saved x) (lims x) (rsn x) (lvl x) (dl x) (mrk x) (lower x) (phs x) (nvars x)
    (tset (rcl x) (nr x) c) (tset (rps x) (nr x) (tlen x)) (S (nr x)) (rcap x) (hr x).

  (* Store u and the lower literals as reason clause nr x, for the literal at trail
     position tlen x: the context and the reason, or no reason if there is no room
     (nvars x reason clauses, rcap x literals). *)
  Definition push_reason (x: Ctx) (u: Lit): Ctx * Reason :=
  if (nr x <? nvars x) &&
     (reasons_size (rcl x) (nr x) + S (length (lower x)) <=? rcap x) then
    (add_reason x (u :: lower x), learnt (nr x))
  else (x, no_reason).

  (* Storing a reason clause keeps the positions of the decisions and the lower
     literals. *)
  Lemma push_reason_stacks: forall (x x': Ctx) (u: Lit) (r: Reason),
    push_reason x u = (x', r) -> SameStacks x x'.
  Proof.
    intros x x' u r Hpush. unfold push_reason in Hpush. destruct (_ && _).
    - injection Hpush as <- _. split; reflexivity.
    - injection Hpush as <- _. split; reflexivity.
  Qed.

  (* Setting a reason clause from n on leaves the size of the first n. *)
  Lemma reasons_size_tset: forall (rc: Table (list Lit)) (n j: nat) (c: list Lit),
    j <= n -> reasons_size (tset rc n c) j = reasons_size rc j.
  Proof.
    intros rc n j c. induction j as [|j IH]; intros Hj; simpl.
    - reflexivity.
    - rewrite IH by lia. rewrite tget_tset_other by lia. reflexivity.
  Qed.

  (* The first reason clauses take less room than more of them. *)
  Lemma reasons_size_le: forall (rc: Table (list Lit)) (j n: nat), j <= n ->
    reasons_size rc j <= reasons_size rc n.
  Proof.
    intros rc j n Hjn. induction n as [|n IH].
    - assert (j = 0) as -> by lia. lia.
    - destruct (Nat.eq_dec j (S n)) as [-> | Hne].
      + lia.
      + simpl. assert (reasons_size rc j <= reasons_size rc n) by (apply IH; lia). lia.
  Qed.

  (* The reason clauses of the literals below trail position len: pop those at len and
     above. *)
  Fixpoint pop_reasons (rps: Table nat) (len n: nat): nat :=
  match n with
  | 0    => 0
  | S n' => if tget rps n' <? len then n else pop_reasons rps len n'
  end.

  (* Popping keeps at most the reason clauses there are. *)
  Lemma pop_reasons_le: forall (rps: Table nat) (len n: nat), pop_reasons rps len n <= n.
  Proof.
    intros rps len n. induction n as [|n IH]; simpl.
    - lia.
    - destruct (tget rps n <? len); lia.
  Qed.
End Reasons.

Section Results.
  (* unmark_lits unmarks the literals ys and only them, changes nothing else, and gives
     the highest of their levels and mx. *)
  Lemma unmark_lits_spec: forall (ys: list Lit) (x x': Ctx) (mx mx': nat),
    unmark_lits x mx ys = (x', mx') ->
    x' = x <| mrk := mrk x' |> /\
    (forall (y: Lit), In y ys -> tget (mrk x') (lit_key y) = false) /\
    (forall (k: nat), (forall (y: Lit), In y ys -> lit_key y <> k) ->
       tget (mrk x') k = tget (mrk x) k) /\
    (forall (y: Lit), In y ys -> level x y <= mx') /\ mx <= mx' /\
    (forall (b: nat), mx <= b ->
       (forall (y: Lit), In y ys -> level x y <= b) -> mx' <= b).
  Proof.
    intros ys.
    induction ys as [|y ys IH]; intros x x' mx mx' Hun; cbn [unmark_lits] in Hun.
    - injection Hun as <- <-. split.
      + destruct x. reflexivity.
      + split.
        * intros y [].
        * split.
          -- easy.
          -- split.
             ++ intros y [].
             ++ split; easy.
    - destruct (IH _ _ _ _ Hun) as (Hx' & Hcleared & Hother & Hle & Hmx & Hleast).
      cbn [set_mrk mrk lvl] in Hother, Hle, Hleast. splits.
      + rewrite Hx' at 1. reflexivity.
      + intros z [-> | Hz].
        * destruct (in_dec Lit.eq_dec z ys) as [Hin | Hnot_in].
          -- now apply Hcleared.
          -- rewrite Hother.
             ++ apply tget_tset_same.
             ++ intros z' Hz' Heq. apply lit_key_inj in Heq. congruence.
        * now apply Hcleared.
      + intros k Hk. rewrite Hother.
        * apply tget_tset_other. apply Hk. now left.
        * intros z Hz. apply Hk. now right.
      + intros z [-> | Hz].
        * lia.
        * now apply Hle.
      + lia.
      + intros b Hb Hlt. apply Hleast.
        * pose proof (Hlt y (or_introl eq_refl)). lia.
        * intros z Hz. apply Hlt. now right.
  Qed.

  (* With positions in increasing order, pop_reasons keeps exactly the reason clauses
     below len. *)
  Lemma pop_reasons_spec: forall (rps: Table nat) (len n: nat),
    (forall (j1 j2: nat), j1 < j2 < n -> tget rps j1 < tget rps j2) ->
    pop_reasons rps len n <= n /\
    forall (j: nat), j < n -> (j < pop_reasons rps len n <-> tget rps j < len).
  Proof.
    intros rps len n. induction n as [|n IH]; intros Horder; cbn [pop_reasons].
    - split.
      + lia.
      + intros j Hj. lia.
    - destruct (tget rps n <? len) eqn:Htop.
      + apply Nat.ltb_lt in Htop. split.
        * lia.
        * intros j Hj. split.
          -- intros _. destruct (Nat.eq_dec j n) as [-> | Hne].
             ++ assumption.
             ++ assert (Hjn: j < n < S n) by lia.
                pose proof (Horder j n Hjn). lia.
          -- intros _. assumption.
      + apply Nat.ltb_ge in Htop.
        destruct IH as [Hle Hiff].
        * intros j1 j2 Hj. apply Horder. lia.
        * split.
          -- lia.
          -- intros j Hj. destruct (Nat.eq_dec j n) as [-> | Hne].
             ++ split; lia.
             ++ apply Hiff. lia.
  Qed.
End Results.

(* A list from a position before its end starts with the entry there. *)
Lemma skipn_nth: forall {A: Type} (l: list A) (d: A) (k: nat),
  (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof.
  intros A l d. induction l as [|a l IH]; intros k Hk; simpl in Hk.
  - lia.
  - destruct k as [|k].
    + reflexivity.
    + simpl. apply IH. lia.
Qed.

(* Unmarking ys from position q on: unmark the literal at q, take the higher of its level
   and mx, and go on with the rest. *)
Lemma unmark_lits_skipn: forall (x1: Ctx) (mx: nat) (ys: list Lit) (q: nat),
  (q < length ys)%nat ->
  unmark_lits x1 mx (skipn q ys)
  = unmark_lits (x1 <| mrk := tset (mrk x1) (lit_key (nth q ys (Pos 0%nat))) false |>)
      (Nat.max mx (level x1 (nth q ys (Pos 0%nat)))) (skipn (S q) ys).
Proof.
  intros x1 mx ys q Hq. rewrite (skipn_nth ys (Pos 0%nat) q Hq). reflexivity.
Qed.

(* Pushing a reason clause keeps the watch lists. *)
Lemma push_reason_wls: forall (x: Ctx) (u: Lit), wls (fst (push_reason x u)) = wls x.
Proof.
  intros x u. unfold push_reason. destruct (_ && _); reflexivity.
Qed.

(* The highest level unmark_lower finds is at most a bound on the levels of the lower
   literals. *)
Lemma unmark_lower_le: forall (x: Ctx) (B: nat),
  (forall (y: Lit), In y (lower x) -> (level x y <= B)%nat) ->
  (snd (unmark_lower x) <= B)%nat.
Proof.
  intros x B Hlt. unfold unmark_lower.
  destruct (unmark_lits x 0 (lower x)) as [x' mx] eqn:Hun. cbn [snd].
  apply unmark_lits_spec in Hun. destruct Hun as (_ & _ & _ & _ & _ & Hleast).
  apply Hleast.
  - lia.
  - assumption.
Qed.

(* A count add_lits gives stays below the number of atoms. *)
Lemma add_lits_count_le: forall (d: nat) (t: option Lit) (ys: list Lit) (x x': Ctx)
  (p q: nat),
  add_lits x d t ys p = (x', Some q) -> (p <= nvars x)%nat -> (q <= nvars x)%nat.
Proof.
  intros d t ys. induction ys as [|l ys IH]; intros x x' p q Hadd Hp;
    cbn [add_lits] in Hadd.
  - injection Hadd as _ <-. assumption.
  - destruct (is_lit t l || tget (mrk x) (lit_key l)).
    + apply (IH x x' p q Hadd Hp).
    + destruct (Nat.eqb (level x l) d).
      * destruct (Nat.leb_spec (nvars x) p) as [Hle | Hgt].
        -- discriminate.
        -- apply (IH _ x' (S p) q Hadd). cbn [mark set_hr set_mrk nvars]. lia.
      * destruct (nvars x <=? length (lower x))%nat.
        -- discriminate.
        -- apply (IH _ x' p q Hadd Hp).
Qed.
Arguments add_lits_count_le {d t ys x x'}.

(* An analysed context has the trail of the context. *)
Lemma analysed_tlen: forall (x x': Ctx), Analysed x x' -> tlen x' = tlen x.
Proof. intros x x' [Hx _]. rewrite Hx. reflexivity. Qed.

(* The reasons do not depend on the marks. *)
Lemma reason_lits_mrk: forall (x: Ctx) (mk: Table bool) (r: Reason),
  reason_lits (x <| mrk := mk |>) r = reason_lits x r.
Proof. intros x mk r. destruct r; reflexivity. Qed.
