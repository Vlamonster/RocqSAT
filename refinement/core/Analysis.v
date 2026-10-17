(* Conflict analysis for backjumping, as MiniSat does it: walk the trail back from its
   end, resolving the conflict clause with the reasons of the literals of the current
   decision level, until one literal of that level is left (the first unique implication
   point). The literals of the current level are only counted and marked; the others are
   collected in a list. The functions work on the context, as the C solver does. *)
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import Evaluation.
From RocqSAT Require Import Model.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Search.
From RocqSAT.refinement Require Import Watches.
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

Section Levels.
  (* The levels and reasons of a context, in a fixed context. *)
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
End Levels.

Section Positions.
  (* A literal on a trail is on its table, below its length. *)
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

  (* A literal propagated after the decision l0 of ⟨m0; l0 ++ n0⟩ has a reason that
     justifies it after the trail before it. *)
  Lemma reason_at: forall (cm: ClauseMap) (rsn: Table Reason) (lv: Table nat)
    (rcl: Table (list Lit)) (rps: Table nat) (nr: nat) (tr: Table Lit) (m0 n0: PA)
    (l0: Lit) (tlen q: nat),
    TraceOk cm rsn lv rcl rps nr ⟨m0; l0 ++ n0⟩ -> TrailOf tr tlen ⟨m0; l0 ++ n0⟩ ->
    NoDecisions n0 -> PA.length m0 < q < tlen ->
    exists (mq: PA), TrailOf tr q mq /\
      ReasonOk cm rcl rps nr mq (tget tr q) (tget rsn (extract (tget tr q))).
  Proof.
    intros cm rsn lv rcl rps nr tr m0 n0 l0. induction n0 as [|n IH t|n IH t];
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

  (* Add the literals ys other than t that are not marked in mk to the analysis at level
     d, with the levels lv: mark them, count those of level d in pathc and append the
     others to lt. Both stay below bound; at a literal that would pass it, stop with no
     count. *)
  Fixpoint add_lits (lv: Table nat) (d bound: nat) (t: option Lit) (ys: list Lit)
    (mk: Table bool) (lt: list Lit) (pathc: nat): Table bool * list Lit * option nat :=
  match ys with
  | []       => (mk, lt, Some pathc)
  | y :: ys' =>
    if is_lit t y || tget mk (lit_key y) then add_lits lv d bound t ys' mk lt pathc
    else if Nat.eqb (tget lv (extract y)) d then
      if bound <=? pathc then (mk, lt, None)
      else add_lits lv d bound t ys' (tset mk (lit_key y) true) lt (S pathc)
    else if bound <=? length lt then (mk, lt, None)
    else add_lits lv d bound t ys' (tset mk (lit_key y) true) (lt ++ [y]) pathc
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
  Fixpoint unmark_range (tr: Table Lit) (mk: Table bool) (idx n: nat): Table bool :=
  match n with
  | 0    => mk
  | S n' => unmark_range tr (tset mk (lit_key (¬tget tr (idx - 1))) false) (idx - 1) n'
  end.

  (* The walk of the analysis at level d of x, whose last decision is at trail position
     lo: pathc literals of level d are marked, and the positions from idx on are done.
     Look for the newest marked one, t; if it is the last, ¬t is the literal to assert;
     otherwise resolve with the reason of t. Without a literal to assert, the marks of
     level d are cleared. The marks and the literals of the lower levels are returned
     too. *)
  Fixpoint analyze_loop (x: Ctx) (d lo fuel idx: nat) (mk: Table bool) (lt: list Lit)
    (pathc: nat): option Lit * Table bool * list Lit :=
  match fuel with
  | 0       => (None, unmark_range (tr x) mk idx (idx - lo), lt)
  | S fuel' =>
    if Nat.eqb pathc 0 then (None, unmark_range (tr x) mk idx (idx - lo), lt) else
    let idx1 := prev_marked (tr x) mk lo idx (idx - lo) in
    if idx1 <=? lo then (None, unmark_range (tr x) mk idx1 (idx1 - lo), lt) else
    let t := tget (tr x) (idx1 - 1) in
    if Nat.eqb pathc 1 then (Some (¬t), mk, lt) else
    let mk1 := tset mk (lit_key (¬t)) false in
    match reason_lits x (tget (rsn x) (extract t)) with
    | None    => (None, unmark_range (tr x) mk1 (idx1 - 1) (idx1 - 1 - lo), lt)
    | Some ys =>
      match add_lits (lvl x) d (nvars x) (Some t) ys mk1 lt (pathc - 1) with
      | (mk2, lt2, Some p) => analyze_loop x d lo fuel' (idx1 - 1) mk2 lt2 p
      | (mk2, lt2, None)   =>
        (None, unmark_range (tr x) mk2 (idx1 - 1) (idx1 - 1 - lo), lt2)
      end
    end
  end.

  (* Analyse the conflict on clause i at level d of x, whose last decision is at trail
     position lo: the literal to assert, if any, with the marks and the literals of the
     lower levels of the analysed clause. *)
  Definition analyze (x: Ctx) (i d lo: nat): option Lit * Table bool * list Lit :=
  match tget (cmap x) i with
  | None    => (None, mrk x, [])
  | Some ls =>
    match add_lits (lvl x) d (nvars x) None ls (mrk x) [] 0 with
    | (mk, lt, Some p) => analyze_loop x d lo (tlen x) (tlen x) mk lt p
    | (mk, lt, None)   => (None, unmark_range (tr x) mk (tlen x) (tlen x - lo), lt)
    end
  end.

  (* Unmark the literals of lt, and find the highest level among them (0 if there is
     none). *)
  Fixpoint unmark_lower (lv: Table nat) (mk: Table bool) (mx: nat) (lt: list Lit):
    Table bool * nat :=
  match lt with
  | []       => (mk, mx)
  | y :: lt' =>
    unmark_lower lv (tset mk (lit_key y) false) (Nat.max mx (tget lv (extract y))) lt'
  end.
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
    - split.
      + lia.
      + split.
        * intros q Hq. lia.
        * intros Hlt. lia.
    - destruct (tget mk (lit_key (¬tget tr (idx - 1)))) eqn:Htop.
      + split.
        * lia.
        * split.
          -- intros q Hq. lia.
          -- intros _. assumption.
      + assert (Hidx1: idx - 1 = lo + n) by lia.
        destruct (IH (idx - 1) Hidx1) as (Hrange & Hnone & Hmarked). split.
        * lia.
        * split.
          -- intros q Hq. destruct (Nat.eq_dec q (idx - 1)) as [-> | Hne].
             ++ assumption.
             ++ apply Hnone. lia.
          -- assumption.
  Qed.

  (* Unmarking only clears marks. *)
  Lemma unmark_range_false: forall (tr: Table Lit) (mk: Table bool) (idx n k: nat),
    tget mk k = false -> tget (unmark_range tr mk idx n) k = false.
  Proof.
    intros tr mk idx n. revert mk idx.
    induction n as [|n IH]; intros mk idx k Hk; cbn [unmark_range].
    - assumption.
    - apply IH. rewrite tget_tset. now destruct (Nat.eq_dec _ k).
  Qed.

  (* The negations of the n literals below idx are unmarked. *)
  Lemma unmark_range_cleared: forall (tr: Table Lit) (mk: Table bool) (idx n q: nat),
    idx - n <= q < idx -> n <= idx ->
    tget (unmark_range tr mk idx n) (lit_key (¬tget tr q)) = false.
  Proof.
    intros tr mk idx n. revert mk idx.
    induction n as [|n IH]; intros mk idx q Hq Hn; cbn [unmark_range].
    - lia.
    - destruct (Nat.eq_dec q (idx - 1)) as [-> | Hne].
      + apply unmark_range_false. apply tget_tset_same.
      + apply IH.
        * lia.
        * lia.
  Qed.
End Marked.

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

  Let Htrace := core_traced m f x Hcore.
  Let Htrail := core_trail m f x Hcore.

  (* The trail before the last decision. *)
  Lemma trail_m0:
    TrailOf (tr x) lo m0 /\ TraceOk (cmap x) (rsn x) (lvl x) (rcl x) (rps x) (nr x) m0.
  Proof.
    pose proof (trail_of_prefix (tr x) (tlen x) ⟨m0; l0⟩ n0 Htrail) as Hprefix.
    destruct (trail_of_snoc (tr x) _ m0 ⟨m0; l0⟩ l0 eq_refl Hprefix) as (_ & _ & Hm0).
    pose proof (trace_app _ _ _ _ _ _ ⟨m0; l0⟩ n0 Htrace) as [_ Hm0'].
    now split.
  Qed.

  (* The literals of the last level have level d, and those before it a lower one. *)
  Lemma seg_level: forall (q: nat),
    lo <= q < tlen x -> tget (lvl x) (extract (tget (tr x) q)) = d.
  Proof.
    intros q Hq.
    apply (trace_last_level (cmap x) (rsn x) (lvl x) (rcl x) (rps x) (nr x) m0 n0 l0).
    - assumption.
    - assumption.
    - apply (seg_nth (tr x) (tlen x) m0).
      + assumption.
      + assumption.
  Qed.

  (* The literals before the last decision have a lower level. *)
  Lemma below_level: forall (q: nat),
    q < lo -> tget (lvl x) (extract (tget (tr x) q)) < d.
  Proof.
    intros q Hq. destruct trail_m0 as [Hm0 Htrace0].
    pose proof (trace_le _ _ _ _ _ _ m0 (tget (tr x) q) Htrace0
                  (trail_of_in (tr x) lo m0 q Hm0 Hq)).
    unfold d. lia.
  Qed.

  (* The negation of a trail literal is false. *)
  Lemma pos_false: forall (q: nat), q < tlen x -> l_eval m (¬tget (tr x) q) = Some false.
  Proof.
    intros q Hq. rewrite l_eval_neg, fresh_in_true.
    - reflexivity.
    - apply Hcore.
    - now apply (trail_of_in (tr x) (tlen x)).
  Qed.

  (* A false literal has a level of at most d. *)
  Lemma level_le: forall (y: Lit),
    l_eval m y = Some false -> tget (lvl x) (extract y) <= d.
  Proof.
    intros y Hy. apply l_eval_false_in in Hy. rewrite <- extract_neg.
    pose proof (trace_le _ _ _ _ _ _ m (¬y) Htrace Hy) as Hle.
    unfold m in Hle. rewrite decisions_app, (no_decisions_zero n0 Hnd) in Hle.
    simpl in Hle. unfold d. lia.
  Qed.

  (* A false literal of level d has its negation on the last level. *)
  Lemma false_pos: forall (y: Lit),
    l_eval m y = Some false -> tget (lvl x) (extract y) = d ->
    exists (q: nat), lo <= q < tlen x /\ tget (tr x) q = ¬y.
  Proof.
    intros y Hy Hlv. apply l_eval_false_in in Hy. unfold m in Hy.
    apply PA.in_app_iff in Hy as [Hin | Hin].
    - apply (seg_pos (tr x) (tlen x) m0 n0 l0).
      + assumption.
      + now right.
    - destruct Hin as [Heq | Hin].
      + apply (seg_pos (tr x) (tlen x) m0 n0 l0).
        * assumption.
        * now left.
      + destruct trail_m0 as [_ Htrace0].
        pose proof (trace_le _ _ _ _ _ _ m0 (¬y) Htrace0 Hin) as Hle.
        rewrite extract_neg, Hlv in Hle. unfold d in Hle. lia.
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
    destruct (reason_at (cmap x) (rsn x) (lvl x) (rcl x) (rps x) (nr x) (tr x) m0 n0 l0
                (tlen x) q Htrace Htrail Hnd Hq) as (mq & Hmq & Hreason).
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
      + apply entailed_clause_of. now apply (core_sound m f x Hcore i).
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
  Record AMarks (idx: nat) (mk: Table bool) (lt: list Lit): Prop := {
    am_marked: forall (y: Lit), tget mk (lit_key y) = true ->
      In y lt \/ exists (q: nat), lo <= q < idx /\ y = ¬tget (tr x) q;
    am_lower: forall (y: Lit), In y lt ->
      tget mk (lit_key y) = true /\ l_eval m y = Some false /\
      tget (lvl x) (extract y) <> d
  }.

  (* Moreover pathc counts the marked literals of the current level below idx. *)
  Record AInv (idx: nat) (mk: Table bool) (lt: list Lit) (pathc: nat): Prop := {
    ai_range: lo <= idx <= tlen x;
    ai_marks: AMarks idx mk lt;
    ai_count: pathc = length (cur_lits (tr x) mk lo (idx - lo))
  }.

  (* The analysed clause: the lower literals and the marked ones of the current level
     below idx. *)
  Definition aclause (idx: nat) (mk: Table bool) (lt: list Lit): list Lit :=
    lt ++ cur_lits (tr x) mk lo (idx - lo).

  (* Adding the literals ys other than t, each false and, if of level d, with its
     negation on the trail below idx: the marks stay as they should, the analysed clause
     only grows, and when no bound was passed it contains ys too, with the count
     right. *)
  Lemma add_lits_spec: forall (ys: list Lit) (t: option Lit) (idx: nat)
    (mk mk': Table bool) (lt lt': list Lit) (pathc: nat) (r: option nat),
    AInv idx mk lt pathc ->
    (forall (y: Lit), In y ys -> is_lit t y = false -> l_eval m y = Some false /\
       (tget (lvl x) (extract y) = d ->
          exists (q: nat), lo <= q < idx /\ tget (tr x) q = ¬y)) ->
    add_lits (lvl x) d (nvars x) t ys mk lt pathc = (mk', lt', r) ->
    AMarks idx mk' lt' /\
    (forall (z: Lit), In z (aclause idx mk lt) -> In z (aclause idx mk' lt')) /\
    (forall (p: nat), r = Some p -> AInv idx mk' lt' p /\
       forall (y: Lit), In y ys -> is_lit t y = false -> In y (aclause idx mk' lt')).
  Proof.
    intros ys t.
    induction ys as [|y ys IH]; intros idx mk mk' lt lt' pathc r Hinv Hys Hadd;
      cbn [add_lits] in Hadd.
    - injection Hadd as <- <- <-. split.
      + apply Hinv.
      + split.
        * easy.
        * intros p Hp. injection Hp as <-. split.
          -- assumption.
          -- intros y [].
    - assert (Hys': forall (z: Lit), In z ys -> is_lit t z = false ->
                l_eval m z = Some false /\
                (tget (lvl x) (extract z) = d ->
                   exists (q: nat), lo <= q < idx /\ tget (tr x) q = ¬z)).
      { intros z Hz. apply Hys. now right. }
      destruct (is_lit t y || tget mk (lit_key y)) eqn:Hskip.
      (* y is t, or marked already *)
      + destruct (IH idx mk mk' lt lt' pathc r Hinv Hys' Hadd)
          as (Hmarks & Hmono & Hsome).
        split.
        * assumption.
        * split.
          -- assumption.
          -- intros p Hp. destruct (Hsome p Hp) as [Hinv' Hin]. split.
             ++ assumption.
             ++ intros z [<- | Hz] Hz_t.
                ** apply Hmono. rewrite Hz_t in Hskip. cbn [orb] in Hskip.
                   destruct (am_marked _ _ _ (ai_marks _ _ _ _ Hinv) y Hskip)
                     as [Hlt | (q & Hq & Hy)].
                   --- apply in_or_app. now left.
                   --- apply in_or_app. right. apply cur_lits_in. exists q. split.
                       +++ lia.
                       +++ split.
                           *** assumption.
                           *** assumption.
                ** now apply Hin.
      + apply orb_false_iff in Hskip as [Hy_t Hy_mk].
        destruct (Hys y (or_introl eq_refl) Hy_t) as [Hy_false Hy_pos].
        destruct Hinv as [Hrange [Hmarked Hlower] Hcount].
        destruct (Nat.eqb (tget (lvl x) (extract y)) d) eqn:Hlv.
        (* y is of the current level: mark it and count it *)
        * apply Nat.eqb_eq in Hlv. destruct (Hy_pos Hlv) as (q0 & Hq0 & Hq0y).
          destruct (nvars x <=? pathc).
          -- injection Hadd as <- <- <-. split.
             ++ now split.
             ++ split.
                ** easy.
                ** intros p Hp. discriminate.
          -- assert (Hy_q0: y = ¬tget (tr x) q0) by now rewrite Hq0y, Neg.involutive.
             assert (Huniq: forall (q: nat), lo <= q < lo + (idx - lo) ->
                              ¬tget (tr x) q = y -> q = q0).
             { intros q Hq Heq. apply distinct_pos.
               - lia.
               - lia.
               - rewrite Hq0y, <- Heq, Neg.involutive. reflexivity. }
             assert (Hq0_range: lo <= q0 < lo + (idx - lo)) by lia.
             destruct (cur_lits_mark (tr x) mk lo (idx - lo) q0 y Hq0_range Hy_q0 Huniq
                         Hy_mk) as [Hlen Hin].
             assert (Hinv1: AInv idx (tset mk (lit_key y) true) lt (S pathc)).
             { split.
               - assumption.
               - split.
                 + intros z Hz. rewrite tget_tset in Hz.
                   destruct (Nat.eq_dec (lit_key y) (lit_key z)) as [Heq | Hne].
                   * apply lit_key_inj in Heq as <-. right. exists q0. split.
                     -- lia.
                     -- assumption.
                   * now apply Hmarked.
                 + intros z Hz.
                   destruct (Hlower z Hz) as (Hz_mk & Hz_false & Hz_lv). split.
                   * rewrite tget_tset.
                     now destruct (Nat.eq_dec (lit_key y) (lit_key z)).
                   * now split.
               - now rewrite Hlen, Hcount. }
             destruct (IH idx _ mk' lt lt' (S pathc) r Hinv1 Hys' Hadd)
               as (Hmarks & Hmono & Hsome).
             split.
             ++ assumption.
             ++ split.
                ** intros z Hz. apply Hmono. unfold aclause in Hz |- *.
                   apply in_app_iff in Hz as [Hz | Hz].
                   --- apply in_or_app. now left.
                   --- apply in_or_app. right. apply Hin. now right.
                ** intros p Hp. destruct (Hsome p Hp) as [Hinv' Hin']. split.
                   --- assumption.
                   --- intros z [<- | Hz] Hz_t.
                       +++ apply Hmono. apply in_or_app. right. apply Hin. now left.
                       +++ now apply Hin'.
        (* y is of a lower level: mark it and keep it *)
        * apply Nat.eqb_neq in Hlv. destruct (nvars x <=? length lt).
          -- injection Hadd as <- <- <-. split.
             ++ now split.
             ++ split.
                ** easy.
                ** intros p Hp. discriminate.
          -- assert (Hnot_cur: forall (q: nat), lo <= q < lo + (idx - lo) ->
                       tget (tset mk (lit_key y) true) (lit_key (¬tget (tr x) q)) =
                       tget mk (lit_key (¬tget (tr x) q))).
             { intros q Hq. rewrite tget_tset_other.
               - reflexivity.
               - intros Heq. apply lit_key_inj in Heq. apply Hlv.
                 rewrite Heq, extract_neg. apply seg_level. lia. }
             pose proof (cur_lits_ext (tr x) mk (tset mk (lit_key y) true) lo (idx - lo)
                           Hnot_cur) as Hsame.
             assert (Hinv1: AInv idx (tset mk (lit_key y) true) (lt ++ [y]) pathc).
             { split.
               - assumption.
               - split.
                 + intros z Hz. rewrite tget_tset in Hz.
                   destruct (Nat.eq_dec (lit_key y) (lit_key z)) as [Heq | Hne].
                   * apply lit_key_inj in Heq as <-. left. apply in_or_app. right.
                     now left.
                   * destruct (Hmarked z Hz) as [Hlt | Hpos].
                     -- left. apply in_or_app. now left.
                     -- now right.
                 + intros z Hz. apply in_app_iff in Hz as [Hz | [<- | []]].
                   * destruct (Hlower z Hz) as (Hz_mk & Hz_false & Hz_lv). split.
                     -- rewrite tget_tset.
                        now destruct (Nat.eq_dec (lit_key y) (lit_key z)).
                     -- now split.
                   * split.
                     -- apply tget_tset_same.
                     -- now split.
               - now rewrite Hsame. }
             destruct (IH idx _ mk' (lt ++ [y]) lt' pathc r Hinv1 Hys' Hadd)
               as (Hmarks & Hmono & Hsome).
             split.
             ++ assumption.
             ++ split.
                ** intros z Hz. apply Hmono. unfold aclause in Hz |- *. rewrite Hsame.
                   apply in_app_iff in Hz as [Hz | Hz].
                   --- apply in_or_app. left. apply in_or_app. now left.
                   --- apply in_or_app. now right.
                ** intros p Hp. destruct (Hsome p Hp) as [Hinv' Hin']. split.
                   --- assumption.
                   --- intros z [<- | Hz] Hz_t.
                       +++ apply Hmono. apply in_or_app. left. apply in_or_app. right.
                           now left.
                       +++ now apply Hin'.
  Qed.

  (* Without a literal to assert, clearing the marks of the current level below idx
     leaves only those of lt. *)
  Lemma fail_marks: forall (idx: nat) (mk: Table bool) (lt: list Lit) (y: Lit),
    AMarks idx mk lt -> lo <= idx ->
    tget (unmark_range (tr x) mk idx (idx - lo)) (lit_key y) = true -> In y lt.
  Proof.
    intros idx mk lt y [Hmarked _] Hidx Hy.
    destruct (tget mk (lit_key y)) eqn:Hmk.
    - destruct (Hmarked y Hmk) as [Hlt | (q & Hq & ->)].
      + assumption.
      + rewrite unmark_range_cleared in Hy.
        * discriminate.
        * lia.
        * lia.
    - rewrite unmark_range_false in Hy.
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
       l_eval m y = Some false /\ tget (lvl x) (extract y) <> d) /\
    (forall (u: Lit), ou = Some u ->
       Entailed f (lt ++ [u]) /\
       exists (q: nat), lo <= q < tlen x /\ u = ¬tget (tr x) q).

  (* Giving up the analysis. *)
  Lemma aresult_fail: forall (idx: nat) (mk: Table bool) (lt: list Lit),
    AMarks idx mk lt -> lo <= idx ->
    AResult None (unmark_range (tr x) mk idx (idx - lo)) lt.
  Proof.
    intros idx mk lt Hmarks Hidx. split.
    - intros y Hy. left. now apply (fail_marks idx mk).
    - split.
      + intros y Hy. destruct (am_lower _ _ _ Hmarks y Hy) as (_ & Hfalse & Hlv).
        now split.
      + intros u Hu. discriminate.
  Qed.

  (* The walk of the analysis, from a state of the invariant whose analysed clause is
     entailed. Every step resolves away the newest marked literal of the current
     level. *)
  Lemma analyze_loop_spec: forall (fuel idx: nat) (mk mk': Table bool) (lt lt': list Lit)
    (pathc: nat) (ou: option Lit),
    AInv idx mk lt pathc -> Entailed f (aclause idx mk lt) -> idx - lo <= fuel ->
    analyze_loop x d lo fuel idx mk lt pathc = (ou, mk', lt') -> AResult ou mk' lt'.
  Proof.
    intros fuel.
    induction fuel as [|fuel IH];
      intros idx mk mk' lt lt' pathc ou Hinv Hent Hfuel Hloop;
      cbn [analyze_loop] in Hloop.
    - injection Hloop as <- <- <-. apply (aresult_fail idx).
      + apply Hinv.
      + apply Hinv.
    - pose proof Hinv as [Hrange Hmarks Hcount].
      destruct (Nat.eqb pathc 0) eqn:Hzero.
      + injection Hloop as <- <- <-. now apply (aresult_fail idx).
      + assert (Hidx: idx = lo + (idx - lo)) by lia.
        destruct (prev_marked_spec (tr x) mk lo (idx - lo) idx Hidx)
          as (Hrange1 & Hnone & Htop).
        set (idx1 := prev_marked (tr x) mk lo idx (idx - lo)) in *.
        (* The count only looks below idx1. *)
        assert (Hcur1: cur_lits (tr x) mk lo (idx - lo) =
                       cur_lits (tr x) mk lo (idx1 - lo)).
        { replace (idx - lo) with ((idx1 - lo) + (idx - idx1)) by lia.
          apply cur_lits_top.
          intros q Hq. apply Hnone. lia. }
        destruct (idx1 <=? lo) eqn:Hlo.
        (* No marked literal is left: give up *)
        * injection Hloop as <- <- <-. apply Nat.leb_le in Hlo.
          assert (Hmarks1: AMarks idx1 mk lt).
          { split.
            - intros y Hy.
              destruct (am_marked _ _ _ Hmarks y Hy) as [Hlt | (q & Hq & ->)].
              + now left.
              + rewrite Hnone in Hy.
                * discriminate.
                * lia.
            - apply Hmarks. }
          now apply (aresult_fail idx1).
        * apply Nat.leb_gt in Hlo. set (t := tget (tr x) (idx1 - 1)) in *.
          specialize (Htop Hlo).
          (* The marked literals below idx1 are ¬t and those below its position. *)
          assert (Hsplit: cur_lits (tr x) mk lo (idx1 - lo) =
                          [¬t] ++ cur_lits (tr x) mk lo (idx1 - 1 - lo)).
          { replace (idx1 - lo) with (S (idx1 - 1 - lo)) by lia. cbn [cur_lits].
            replace (lo + (idx1 - 1 - lo)) with (idx1 - 1) by lia. fold t.
            now rewrite Htop. }
          destruct (Nat.eqb pathc 1) eqn:Hone.
          (* ¬t is the last literal of the current level: assert it *)
          -- injection Hloop as <- <- <-. apply Nat.eqb_eq in Hone.
             rewrite Hcur1, Hsplit in Hcount. simpl in Hcount.
             assert (Hempty: cur_lits (tr x) mk lo (idx1 - 1 - lo) = []).
             { destruct (cur_lits (tr x) mk lo (idx1 - 1 - lo)).
               - reflexivity.
               - simpl in Hcount. lia. }
             split.
             ++ intros y Hy.
                destruct (am_marked _ _ _ Hmarks y Hy) as [Hlt | (q & Hq & ->)].
                ** now left.
                ** right. destruct (Nat.eq_dec q (idx1 - 1)) as [-> | Hne].
                   --- reflexivity.
                   --- exfalso. destruct (Nat.lt_ge_cases q idx1) as [Hlt | Hge].
                       +++ assert (Hin: In (¬tget (tr x) q)
                                          (cur_lits (tr x) mk lo (idx1 - 1 - lo))).
                           { apply cur_lits_in. exists q. split.
                             - lia.
                             - now split. }
                           now rewrite Hempty in Hin.
                       +++ rewrite Hnone in Hy.
                           *** discriminate.
                           *** lia.
             ++ split.
                ** intros y Hy.
                   destruct (am_lower _ _ _ Hmarks y Hy) as (_ & Hfalse & Hlv).
                   now split.
                ** intros u Hu. injection Hu as <-. split.
                   --- apply (entailed_incl f (aclause idx mk lt)).
                       +++ assumption.
                       +++ intros y Hy. unfold aclause in Hy.
                           rewrite Hcur1, Hsplit, Hempty in Hy.
                           assumption.
                   --- exists (idx1 - 1). split.
                       +++ lia.
                       +++ reflexivity.
          (* Resolve with the reason of t *)
          -- apply Nat.eqb_neq in Hzero, Hone. set (q := idx1 - 1) in *.
             rewrite Hcur1, Hsplit in Hcount. simpl in Hcount.
             (* t is not the decision: that would leave one marked literal *)
             assert (Hq_lo: lo < q).
             { destruct (Nat.eq_dec q lo) as [Heq | Hne].
               - exfalso. replace (q - lo) with 0 in Hcount by lia. simpl in Hcount. lia.
               - lia. }
             set (mk1 := tset mk (lit_key (¬t)) false) in Hloop.
             (* The literals of the current level below q are not ¬t. *)
             assert (Hbelow: forall (q': nat), lo <= q' < lo + (q - lo) ->
                       tget mk1 (lit_key (¬tget (tr x) q')) =
                       tget mk (lit_key (¬tget (tr x) q'))).
             { intros q' Hq'. unfold mk1. rewrite tget_tset_other.
               - reflexivity.
               - intros Heq. apply lit_key_inj in Heq. apply (f_equal Neg.neg) in Heq.
                 rewrite !Neg.involutive in Heq. assert (q' = q).
                 + apply distinct_pos.
                   * lia.
                   * lia.
                   * unfold t in Heq. now rewrite Heq.
                 + lia. }
             pose proof (cur_lits_ext (tr x) mk mk1 lo (q - lo) Hbelow) as Hcur_q.
             assert (Hinv1: AInv q mk1 lt (pathc - 1)).
             { split.
               - lia.
               - split.
                 + intros y Hy. unfold mk1 in Hy. rewrite tget_tset in Hy.
                   destruct (Nat.eq_dec (lit_key (¬t)) (lit_key y)) as [Heq | Hne].
                   * discriminate.
                   * destruct (am_marked _ _ _ Hmarks y Hy) as [Hlt | (q' & Hq' & ->)].
                     -- now left.
                     -- right. exists q'. split.
                        ++ destruct (Nat.eq_dec q' q) as [-> | Hne'].
                           ** exfalso. now apply Hne.
                           ** destruct (Nat.lt_ge_cases q' idx1) as [Hlt | Hge].
                              --- lia.
                              --- rewrite Hnone in Hy.
                                  +++ discriminate.
                                  +++ lia.
                        ++ reflexivity.
                 + intros y Hy.
                   destruct (am_lower _ _ _ Hmarks y Hy) as (Hy_mk & Hfalse & Hlv).
                   split.
                   * unfold mk1. rewrite tget_tset_other.
                     -- assumption.
                     -- intros Heq. apply lit_key_inj in Heq. apply Hlv.
                        rewrite <- Heq, extract_neg.
                        apply seg_level. lia.
                   * now split.
               - rewrite Hcur_q. lia. }
             destruct (reason_lits x (tget (rsn x) (extract t))) as [ys|] eqn:Hreason.
             ++ assert (Hq_range: lo < q < tlen x) by lia.
                destruct (reason_spec q ys Hq_range Hreason)
                  as (Hys_ent & Ht_in & Hys_pos).
                destruct (add_lits (lvl x) d (nvars x) (Some t) ys mk1 lt (pathc - 1))
                  as [[mk2 lt2] r] eqn:Hadd.
                assert (Hpre: forall (y: Lit), In y ys -> is_lit (Some t) y = false ->
                          l_eval m y = Some false /\
                          (tget (lvl x) (extract y) = d ->
                             exists (q': nat), lo <= q' < q /\ tget (tr x) q' = ¬y)).
                { intros y Hy Hy_t. cbn [is_lit] in Hy_t. apply Lit.eqb_neq in Hy_t.
                  destruct (Hys_pos y Hy Hy_t) as (q' & Hq' & Hq'y). split.
                  - rewrite <- (Neg.involutive y), <- Hq'y. apply pos_false. lia.
                  - intros Hlv. exists q'. split.
                    + split.
                      * destruct (Nat.lt_ge_cases q' lo) as [Hlt | Hge].
                        -- exfalso. pose proof (below_level q' Hlt) as Hlow.
                           rewrite Hq'y, extract_neg, Hlv in Hlow. lia.
                        -- assumption.
                      * assumption.
                    + assumption. }
                destruct (add_lits_spec ys (Some t) q mk1 mk2 lt lt2 (pathc - 1) r Hinv1
                            Hpre Hadd)
                  as (Hmarks2 & Hmono & Hsome).
                destruct r as [p|].
                ** destruct (Hsome p eq_refl) as [Hinv2 Hys_in].
                   apply (IH q mk2 mk' lt2 lt' p ou Hinv2).
                   --- apply (entailed_resolve f (aclause idx mk lt) ys
                               (aclause q mk2 lt2) t).
                       +++ assumption.
                       +++ assumption.
                       +++ intros y Hy Hne. apply Hmono. unfold aclause in Hy |- *.
                           rewrite Hcur1, Hsplit in Hy. rewrite Hcur_q.
                           apply in_app_iff in Hy as [Hy | [Hy | Hy]].
                           *** apply in_or_app. now left.
                           *** exfalso. apply Hne. now symmetry.
                           *** apply in_or_app. now right.
                       +++ intros y Hy Hne. apply Hys_in.
                           *** assumption.
                           *** cbn [is_lit]. now apply Lit.eqb_neq.
                   --- lia.
                   --- assumption.
                ** injection Hloop as <- <- <-. apply (aresult_fail q).
                   --- assumption.
                   --- lia.
             ++ injection Hloop as <- <- <-. apply (aresult_fail q).
                ** apply Hinv1.
                ** lia.
  Qed.

  (* The analysis of a false clause of x. *)
  Lemma analyze_spec: forall (i: nat) (ls: list Lit) (ou: option Lit) (mk: Table bool)
    (lt: list Lit),
    tget (cmap x) i = Some ls ->
    (forall (y: Lit), In y ls -> lookup (vals x) y = Some false) ->
    Unmarked (mrk x) -> analyze x i d lo = (ou, mk, lt) -> AResult ou mk lt.
  Proof.
    intros i ls ou mk lt Hi Hfalse Hunmarked Han. unfold analyze in Han.
    rewrite Hi in Han.
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
              l_eval m y = Some false /\
              (tget (lvl x) (extract y) = d ->
                 exists (q: nat), lo <= q < tlen x /\ tget (tr x) q = ¬y)).
    { intros y Hy _. assert (Hy_false: l_eval m y = Some false).
      { rewrite <- (core_vals m f x Hcore). now apply Hfalse. }
      split.
      - assumption.
      - intros Hlv. now apply false_pos. }
    destruct (add_lits (lvl x) d (nvars x) None ls (mrk x) [] 0)
      as [[mk1 lt1] r] eqn:Hadd.
    destruct (add_lits_spec ls None (tlen x) (mrk x) mk1 [] lt1 0 r Hinv0 Hpre Hadd)
      as (Hmarks1 & _ & Hsome).
    destruct r as [p|].
    - destruct (Hsome p eq_refl) as [Hinv1 Hls_in].
      apply (analyze_loop_spec (tlen x) (tlen x) mk1 mk lt1 lt p ou Hinv1).
      + apply (entailed_incl f ls).
        * apply entailed_clause_of. now apply (core_sound m f x Hcore i).
        * intros y Hy. now apply Hls_in.
      + lia.
      + assumption.
    - injection Han as <- <- <-. apply (aresult_fail (tlen x)).
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
    (cur x)
    (saved x) (rsn x) (lvl x) (dl x) (mrk x) (phs x) (nvars x) (tset (rcl x) (nr x) c)
    (tset (rps x) (nr x) (tlen x)) (S (nr x)) (rcap x).

  (* Store u :: lt as reason clause nr x, for the literal at trail position tlen x: the
     context and the reason, or no reason if there is no room (nvars x reason clauses,
     rcap x literals). *)
  Definition push_reason (x: Ctx) (u: Lit) (lt: list Lit): Ctx * Reason :=
  if (nr x <? nvars x) &&
     (reasons_size (rcl x) (nr x) + S (length lt) <=? rcap x) then
    (add_reason x (u :: lt), learnt (nr x))
  else (x, no_reason).

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
    - destruct (tget rps n <? len).
      + lia.
      + lia.
  Qed.
End Reasons.

Section Results.
  (* unmark_lower unmarks the literals of lt and only them, and gives the highest of
     their levels and mx. *)
  Lemma unmark_lower_spec: forall (lv: Table nat) (lt: list Lit) (mk mk': Table bool)
    (mx mx': nat),
    unmark_lower lv mk mx lt = (mk', mx') ->
    (forall (y: Lit), In y lt -> tget mk' (lit_key y) = false) /\
    (forall (k: nat), (forall (y: Lit), In y lt -> lit_key y <> k) ->
       tget mk' k = tget mk k) /\
    (forall (y: Lit), In y lt -> tget lv (extract y) <= mx') /\ mx <= mx' /\
    (forall (b: nat), mx <= b ->
       (forall (y: Lit), In y lt -> tget lv (extract y) <= b) -> mx' <= b).
  Proof.
    intros lv lt.
    induction lt as [|y lt IH]; intros mk mk' mx mx' Hun; cbn [unmark_lower] in Hun.
    - injection Hun as <- <-. split.
      + intros y [].
      + split.
        * easy.
        * split.
          -- intros y [].
          -- split.
             ++ easy.
             ++ easy.
    - destruct (IH _ _ _ _ Hun) as (Hcleared & Hother & Hle & Hmx & Hleast). split.
      + intros z [-> | Hz].
        * destruct (in_dec Lit.eq_dec z lt) as [Hin | Hnot_in].
          -- now apply Hcleared.
          -- rewrite Hother.
             ++ apply tget_tset_same.
             ++ intros z' Hz' Heq. apply lit_key_inj in Heq. congruence.
        * now apply Hcleared.
      + split.
        * intros k Hk. rewrite Hother.
          -- apply tget_tset_other. apply Hk. now left.
          -- intros z Hz. apply Hk. now right.
        * split.
          -- intros z [-> | Hz].
             ++ lia.
             ++ now apply Hle.
          -- split.
             ++ lia.
             ++ intros b Hb Hlt. apply Hleast.
                ** pose proof (Hlt y (or_introl eq_refl)). lia.
                ** intros z Hz. apply Hlt. now right.
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
             ++ split.
                ** lia.
                ** lia.
             ++ apply Hiff. lia.
  Qed.
End Results.

Section Jump.
  (* m split as ⟨mt; d ++ n⟩, where n contains k decisions. *)
  Fixpoint split_levels (k: nat) (m: PA): option (PA * Lit * PA) :=
  match m with
  | ⟨⟩      => None
  | ⟨m', x⟩ =>
    match split_levels k m' with
    | Some (mt, d, n) => Some (mt, d, ⟨n, x⟩)
    | None            => None
    end
  | ⟨m'; x⟩ =>
    match k with
    | 0    => Some (m', x, ⟨⟩)
    | S k' =>
      match split_levels k' m' with
      | Some (mt, d, n) => Some (mt, d, ⟨n; x⟩)
      | None            => None
      end
    end
  end.

  Lemma split_levels_spec: forall (k: nat) (m mt n: PA) (d: Lit),
    split_levels k m = Some (mt, d, n) -> m = ⟨mt; d ++ n⟩.
  Proof.
    intros k m. revert k. induction m as [|m IH x|m IH x]; intros k mt n d Hsplit; simpl in Hsplit.
    - discriminate.
    - destruct (split_levels k m) as [[[mt' d'] n']|] eqn:Hm.
      + injection Hsplit as <- <- <-. apply IH in Hm as ->. reflexivity.
      + discriminate.
    - destruct k as [|k].
      + now injection Hsplit as <- <- <-.
      + destruct (split_levels k m) as [[[mt' d'] n']|] eqn:Hm.
        * injection Hsplit as <- <- <-. apply IH in Hm as ->. reflexivity.
        * discriminate.
  Qed.
End Jump.
