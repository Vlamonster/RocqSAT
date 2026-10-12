From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import State.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import Trans.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Search.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import Analysis.
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement Require Import Step.

(* The step of Step.v computed from the context alone, as C code does: the trail is only used through its table,
   with the positions of its decisions on a stack. *)

Section Free.
  (* The visit of Propagate.v without the trail. *)
  Fixpoint visit_t (p: Lit) (ws kept: list nat) (x: Ctx): Ctx * option nat :=
  match ws with
  | []        => (set_watching x p (rev kept), None)
  | i :: rest =>
    match tget (wat x) i with
    | (w1, w2) =>
      if (w1 =? p) || (w2 =? p) then
        let o := if w1 =? p then w2 else w1 in
        if lookup_true (vals x) o then visit_t p rest (i :: kept) x else
        match tget (cmap x) i with
        | Some ls =>
          match find (fun (r: Lit) => not_false (vals x) r && negb (r =? o)) ls with
          | Some r => visit_t p rest kept (move_watch x i (if w1 =? p then (r, w2) else (w1, r)) r)
          | None   =>
            if lookup_undef (vals x) o then visit_t p rest (i :: kept) (assign x o (S i))
            else (set_watching x p (rev_append kept ws), Some i)
          end
        | None    => visit_t p rest kept x
        end
      else visit_t p rest kept x
    end
  end.

  Lemma visit_free: forall (p: Lit) (ws kept: list nat) (m m': PA) (x x': Ctx) (r: option nat),
    visit p ws kept m x = (m', x', r) -> visit_t p ws kept x = (x', r).
  Proof.
    intros p ws. induction ws as [|i ws IH]; intros kept m m' x x' r Hvisit; simpl in Hvisit |- *.
    - now injection Hvisit as _ <- <-.
    - destruct (tget (wat x) i) as [w1 w2]. destruct ((w1 =? p) || (w2 =? p)).
      + destruct (lookup_true (vals x) (if w1 =? p then w2 else w1)).
        * now apply IH in Hvisit.
        * destruct (tget (cmap x) i) as [ls|].
          -- destruct (find _ ls) as [r'|].
             ++ now apply IH in Hvisit.
             ++ destruct (lookup_undef (vals x) (if w1 =? p then w2 else w1)).
                ** now apply IH in Hvisit.
                ** now injection Hvisit as _ <- <-.
          -- now apply IH in Hvisit.
      + now apply IH in Hvisit.
  Qed.

  (* The propagation of Propagate.v without the trail. *)
  Fixpoint propagate_t (fuel: nat) (x: Ctx): Ctx * option nat :=
  match fuel with
  | 0       => (x, None)
  | S fuel' =>
    if qhead x <? tlen x then
      let p := ¬(tget (tr x) (qhead x)) in
      match visit_t p (watching (wls x) p) [] x with
      | (x', Some i) => (x', Some i)
      | (x', None)   => propagate_t fuel' (advance x')
      end
    else (x, None)
  end.

  Lemma propagate_free: forall (fuel: nat) (m m': PA) (x x': Ctx) (r: option nat),
    propagate fuel m x = (m', x', r) -> propagate_t fuel x = (x', r).
  Proof.
    intros fuel. induction fuel as [|fuel IH]; intros m m' x x' r Hprop; simpl in Hprop |- *.
    - now injection Hprop as _ <- <-.
    - destruct (qhead x <? tlen x).
      + destruct (visit (¬(tget (tr x) (qhead x))) _ [] m x) as [[m1 x1] [i|]] eqn:Hvisit;
          apply visit_free in Hvisit; rewrite Hvisit.
        * now injection Hprop as _ <- <-.
        * now apply IH in Hprop.
      + now injection Hprop as _ <- <-.
  Qed.

  (* The check of the short clauses of Propagate.v without the trail. *)
  Fixpoint check_shorts_t (ss: list nat) (x: Ctx): Ctx * option nat :=
  match ss with
  | []       => (x, None)
  | i :: ss' =>
    match tget (cmap x) i with
    | Some (a :: _) =>
      match lookup (vals x) a with
      | Some true  => check_shorts_t ss' x
      | Some false => (x, Some i)
      | None       => check_shorts_t ss' (assign x a (S i))
      end
    | Some []       => (x, Some i)
    | None          => check_shorts_t ss' x
    end
  end.

  Lemma check_shorts_free: forall (ss: list nat) (m m': PA) (x x': Ctx) (r: option nat),
    check_shorts ss m x = (m', x', r) -> check_shorts_t ss x = (x', r).
  Proof.
    intros ss. induction ss as [|i ss IH]; intros m m' x x' r Hcheck; simpl in Hcheck |- *.
    - now injection Hcheck as _ <- <-.
    - destruct (tget (cmap x) i) as [[|a ls]|].
      + now injection Hcheck as _ <- <-.
      + destruct (lookup (vals x) a) as [[|]|].
        * now apply IH in Hcheck.
        * now injection Hcheck as _ <- <-.
        * now apply IH in Hcheck.
      + now apply IH in Hcheck.
  Qed.
End Free.

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

  (* The position of the first literal of the last decision level. *)
  Definition level_start (lims: list nat): nat :=
  match lims with
  | j :: _ => S j
  | []     => 0
  end.

  Lemma pa_length_app: forall (m n: PA), PA.length ⟨m ++ n⟩ = PA.length m + PA.length n.
  Proof.
    intros m n. induction n as [|n IH l|n IH l]; simpl.
    - lia.
    - rewrite IH. lia.
    - rewrite IH. lia.
  Qed.

  Lemma level_start_le: forall (lims: list nat) (m: PA), LimsOf lims m -> level_start lims <= PA.length m.
  Proof.
    intros lims m. revert lims. induction m as [|m IH l|m IH l]; intros lims Hlims; simpl in Hlims |- *.
    - now subst lims.
    - apply IH in Hlims. lia.
    - destruct lims as [|j lims].
      + contradiction.
      + destruct Hlims as [-> _]. simpl. lia.
  Qed.

  (* Propagations keep the positions of the decisions. *)
  Lemma lims_extends: forall (lims: list nat) (m m': PA), LimsOf lims m -> Extends m m' -> LimsOf lims m'.
  Proof.
    intros lims m m' Hlims [n [-> Hn]]. induction n as [|n IH l|n IH l]; simpl in Hn |- *.
    - assumption.
    - now apply IH.
    - destruct Hn.
  Qed.

  (* No decisions exactly when no positions. *)
  Lemma lims_nil: forall (lims: list nat) (m: PA), LimsOf lims m -> lims = [] -> NoDecisions m.
  Proof.
    intros lims m. revert lims. induction m as [|m IH l|m IH l]; intros lims Hlims Hnil; simpl in Hlims |- *.
    - easy.
    - now apply (IH lims).
    - subst lims. contradiction.
  Qed.

  (* The positions of the decisions of ⟨m; l ++ n⟩: those of n, that of l, then those of m. *)
  Lemma lims_split: forall (lims: list nat) (m n: PA) (l: Lit),
    LimsOf lims ⟨m; l ++ n⟩ ->
    exists (lims': list nat), skipn (decisions n) lims = PA.length m :: lims' /\ LimsOf lims' m /\
      length lims = decisions n + S (length lims').
  Proof.
    intros lims m n l. revert lims. induction n as [|n IH y|n IH y]; intros lims Hlims; simpl in Hlims |- *.
    - destruct lims as [|j lims].
      + contradiction.
      + destruct Hlims as [-> Hlims]. now exists lims.
    - now apply IH.
    - destruct lims as [|j lims].
      + contradiction.
      + destruct Hlims as [_ Hlims]. destruct (IH lims Hlims) as (lims' & Hskip & Hlims' & Hlen). exists lims'.
        simpl. split.
        * assumption.
        * split.
          -- assumption.
          -- lia.
  Qed.

  (* The positions of the decisions on m split as m = ⟨mt; d ++ n⟩ by split_levels. *)
  Lemma split_levels_lims: forall (k: nat) (m mt n: PA) (d: Lit) (lims: list nat),
    LimsOf lims m -> split_levels k m = Some (mt, d, n) -> nth_error lims k = Some (PA.length mt) /\ decisions n = k.
  Proof.
    intros k m. revert k. induction m as [|m IH x|m IH x]; intros k mt n d lims Hlims Hsplit; simpl in Hlims, Hsplit.
    - discriminate.
    - destruct (split_levels k m) as [[[mt' d'] n']|] eqn:Hm.
      + injection Hsplit as -> -> <-. destruct (IH k mt n' d lims Hlims Hm) as [Hnth Hdec]. now split.
      + discriminate.
    - destruct lims as [|j lims].
      + contradiction.
      + destruct Hlims as [-> Hlims]. destruct k as [|k].
        * now injection Hsplit as <- <- <-.
        * destruct (split_levels k m) as [[[mt' d'] n']|] eqn:Hm.
          -- injection Hsplit as -> -> <-. destruct (IH k mt n' d lims Hlims Hm) as [Hnth Hdec]. simpl. split.
             ++ assumption.
             ++ now rewrite Hdec.
          -- discriminate.
  Qed.

  Lemma split_levels_lims_none: forall (k: nat) (m: PA) (lims: list nat),
    LimsOf lims m -> split_levels k m = None -> nth_error lims k = None.
  Proof.
    intros k m. revert k. induction m as [|m IH x|m IH x]; intros k lims Hlims Hsplit; simpl in Hlims, Hsplit.
    - subst lims. now destruct k.
    - destruct (split_levels k m) as [[[mt' d'] n']|] eqn:Hm.
      + discriminate.
      + now apply IH.
    - destruct lims as [|j lims].
      + contradiction.
      + destruct Hlims as [_ Hlims]. destruct k as [|k].
        * discriminate.
        * destruct (split_levels k m) as [[[mt' d'] n']|] eqn:Hm.
          -- discriminate.
          -- simpl. now apply IH.
  Qed.
End Lims.

Section Trail.
  (* The last literal of a trail is at the end of its table. *)
  Lemma trail_of_snoc: forall (tr: Table Lit) (tlen: nat) (m m': PA) (t: Lit),
    trail_lits m' = trail_lits m ++ [t] ->
    TrailOf tr tlen m' ->
    tlen = S (PA.length m) /\ tget tr (PA.length m) = t /\ TrailOf tr (PA.length m) m.
  Proof.
    intros tr tlen m m' t Hlits [Hlen Hnth]. rewrite Hlits, length_app, trail_lits_length in Hlen. simpl in Hlen.
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

  (* Whether l is at a position from j on, for n positions, newest first. *)
  Fixpoint in_range (l: Lit) (tr: Table Lit) (j n: nat): bool :=
  match n with
  | 0    => false
  | S n' => (tget tr (j + n') =? l) || in_range l tr j n'
  end.

  Lemma in_range_spec: forall (tr: Table Lit) (tlen: nat) (a b: PA) (l: Lit),
    TrailOf tr tlen ⟨a ++ b⟩ -> in_range l tr (PA.length a) (PA.length b) = in_trail l b.
  Proof.
    intros tr tlen a b l. revert tlen. induction b as [|b IH x|b IH x]; intros tlen Htrail; simpl.
    - reflexivity.
    - destruct (trail_of_snoc tr tlen ⟨a ++ b⟩ ⟨a ++ b, x⟩ x eq_refl Htrail) as (_ & Hx & Hprefix).
      rewrite pa_length_app in Hx, Hprefix. rewrite Hx. now rewrite (IH _ Hprefix).
    - destruct (trail_of_snoc tr tlen ⟨a ++ b⟩ ⟨a ++ b; x⟩ x eq_refl Htrail) as (_ & Hx & Hprefix).
      rewrite pa_length_app in Hx, Hprefix. rewrite Hx. now rewrite (IH _ Hprefix).
  Qed.

  (* Whether a literal at a position from j on, for n positions, other than nu has its negation marked. *)
  Fixpoint marked_range (mk: Table bool) (nu: Lit) (tr: Table Lit) (j n: nat): bool :=
  match n with
  | 0    => false
  | S n' => (tget mk (neg_key (tget tr (j + n'))) && negb (tget tr (j + n') =? nu)) || marked_range mk nu tr j n'
  end.

  Lemma marked_range_spec: forall (tr: Table Lit) (tlen: nat) (a b: PA) (mk: Table bool) (nu: Lit),
    TrailOf tr tlen ⟨a ++ b⟩ -> marked_range mk nu tr (PA.length a) (PA.length b) = marked_neg mk nu b.
  Proof.
    intros tr tlen a b mk nu. revert tlen. induction b as [|b IH x|b IH x]; intros tlen Htrail; simpl.
    - reflexivity.
    - destruct (trail_of_snoc tr tlen ⟨a ++ b⟩ ⟨a ++ b, x⟩ x eq_refl Htrail) as (_ & Hx & Hprefix).
      rewrite pa_length_app in Hx, Hprefix. rewrite Hx. now rewrite (IH _ Hprefix).
    - destruct (trail_of_snoc tr tlen ⟨a ++ b⟩ ⟨a ++ b; x⟩ x eq_refl Htrail) as (_ & Hx & Hprefix).
      rewrite pa_length_app in Hx, Hprefix. rewrite Hx. now rewrite (IH _ Hprefix).
  Qed.

  (* v without the values of the literals at the n positions from j on, newest first. *)
  Fixpoint unset_range (v: Values) (tr: Table Lit) (j n: nat): Values :=
  match n with
  | 0    => v
  | S n' => unset_range (unset_value v (tget tr (j + n'))) tr j n'
  end.

  Lemma unset_range_spec: forall (tr: Table Lit) (tlen: nat) (mt n: PA) (d: Lit) (v: Values),
    TrailOf tr tlen ⟨mt; d ++ n⟩ -> unset_range v tr (PA.length mt) (S (PA.length n)) = unassign_segment v d n.
  Proof.
    intros tr tlen mt n d. revert tlen. induction n as [|n IH x|n IH x]; intros tlen v Htrail.
    - destruct (trail_of_snoc tr tlen mt ⟨mt; d⟩ d eq_refl Htrail) as (_ & Hd & _). simpl.
      now rewrite Nat.add_0_r, Hd.
    - destruct (trail_of_snoc tr tlen ⟨mt; d ++ n⟩ ⟨mt; d ++ n, x⟩ x eq_refl Htrail) as (_ & Hx & Hprefix).
      cbn [unassign_segment PA.length unset_range]. replace (PA.length mt + S (PA.length n)) with
        (PA.length ⟨mt; d ++ n⟩).
      + rewrite Hx. now apply (IH (PA.length ⟨mt; d ++ n⟩)).
      + rewrite (pa_length_app ⟨mt; d⟩ n). simpl. lia.
    - destruct (trail_of_snoc tr tlen ⟨mt; d ++ n⟩ ⟨mt; d ++ n; x⟩ x eq_refl Htrail) as (_ & Hx & Hprefix).
      cbn [unassign_segment PA.length unset_range]. replace (PA.length mt + S (PA.length n)) with
        (PA.length ⟨mt; d ++ n⟩).
      + rewrite Hx. now apply (IH (PA.length ⟨mt; d ++ n⟩)).
      + rewrite (pa_length_app ⟨mt; d⟩ n). simpl. lia.
  Qed.

  (* Unassigning the last level is unassigning the segment of its decision. *)
  Lemma unassign_level_segment: forall (v: Values) (m n: PA) (l: Lit),
    NoDecisions n -> unassign_level v ⟨m; l ++ n⟩ = unassign_segment v l n.
  Proof.
    intros v m n l. revert v. induction n as [|n IH x|n IH x]; intros v Hn; simpl in Hn |- *.
    - reflexivity.
    - now apply IH.
    - destruct Hn.
  Qed.
End Trail.

Section Analyze.
  Context (cm: ClauseMap) (rsn lv: Table nat) (d: nat) (tr: Table Lit).

  (* The analysis of Analysis.v on the n positions of the trail table from lo on, newest first. *)
  Fixpoint analyze_t (lo n: nat) (mk: Table bool) (c: list Lit) (k: nat): list Lit * Table bool :=
  match n with
  | 0    => (c, mk)
  | S n' =>
    let t := tget tr (lo + n') in
    if Nat.leb k 1 then (c, mk)
    else if tget mk (lit_key (¬t)) then
      match tget rsn (extract t) with
      | 0   => (c, mk)
      | S i =>
        match tget cm i with
        | Some r =>
          match resolve_marked lv d mk c r t k with
          | (c', mk', k') => analyze_t lo n' mk' c' k'
          end
        | None   => (c, mk)
        end
      end
    else analyze_t lo n' mk c k
  end.

  Lemma analyze_t_spec: forall (m: PA) (tlen: nat) (lims: list nat) (mk: Table bool) (c: list Lit) (k: nat),
    TrailOf tr tlen m ->
    LimsOf lims m ->
    analyze_t (level_start lims) (tlen - level_start lims) mk c k = analyze cm rsn lv d m mk c k.
  Proof.
    intros m. induction m as [|m IH t|m IH t]; intros tlen lims mk c k Htrail Hlims.
    - destruct Htrail as [Hlen _]. simpl in Hlen, Hlims. subst tlen lims. reflexivity.
    - destruct (trail_of_snoc tr tlen m ⟨m, t⟩ t eq_refl Htrail) as (-> & Ht & Hprefix). simpl in Hlims.
      pose proof (level_start_le lims m Hlims) as Hle.
      replace (S (PA.length m) - level_start lims) with (S (PA.length m - level_start lims)) by lia.
      cbn [analyze_t analyze]. replace (level_start lims + (PA.length m - level_start lims)) with (PA.length m) by lia.
      rewrite Ht. destruct (Nat.leb k 1).
      + reflexivity.
      + destruct (tget mk (lit_key (¬t))).
        * destruct (tget rsn (extract t)) as [|i].
          -- reflexivity.
          -- destruct (tget cm i) as [r|].
             ++ destruct (resolve_marked lv d mk c r t k) as [[c' mk'] k']. now apply IH.
             ++ reflexivity.
        * now apply IH.
    - destruct (trail_of_snoc tr tlen m ⟨m; t⟩ t eq_refl Htrail) as (-> & _ & _). simpl in Hlims.
      destruct lims as [|j lims].
      + contradiction.
      + destruct Hlims as [-> _]. simpl. now rewrite Nat.sub_diag.
  Qed.
End Analyze.

Section Plan.
  (* The plan of Analysis.v on the trail table: the literal to assert, the position of the decision to jump back
     to, and the number of decisions above it. *)
  Definition plan_t (v: Values) (lv: Table nat) (d: nat) (tr: Table Lit) (tlen: nat) (lims: list nat)
    (mk: Table bool) (c: list Lit): option (Lit * nat * nat) :=
  match find (fun (y: Lit) => Nat.eqb (tget lv (extract y)) d) c with
  | None   => None
  | Some u =>
    let rest := filter (fun (y: Lit) => negb (y =? u)) c in
    let k := d - S (list_max (map (fun (y: Lit) => tget lv (extract y)) rest)) in
    match nth_error lims k with
    | None   => None
    | Some j =>
      let nu := ¬u in
      if forallb (fun (y: Lit) => negb (not_false v y)) c &&
        ((tget tr j =? nu) || in_range nu tr (S j) (tlen - S j)) &&
        negb (marked_neg mk nu ⟨∅; (tget tr j)⟩ || marked_range mk nu tr (S j) (tlen - S j))
      then Some (u, j, k)
      else None
    end
  end.

  (* The parts of a plan of Analysis.v that the trail table determines. *)
  Definition plan_pos (p: Lit * (PA * Lit * PA)): Lit * nat * nat :=
  match p with
  | (u, (mt, _, n)) => (u, PA.length mt, decisions n)
  end.

  Lemma plan_t_spec: forall (v: Values) (lv: Table nat) (d: nat) (m: PA) (tr: Table Lit) (tlen: nat)
    (lims: list nat) (mk: Table bool) (c: list Lit),
    TrailOf tr tlen m ->
    LimsOf lims m ->
    plan_t v lv d tr tlen lims mk c = option_map plan_pos (plan v lv d m mk c).
  Proof.
    intros v lv d m tr tlen lims mk c Htrail Hlims. unfold plan_t, plan.
    destruct (find (fun (y: Lit) => Nat.eqb (tget lv (extract y)) d) c) as [u|].
    2: reflexivity.
    cbv zeta. set (k := d - S (list_max _)).
    destruct (split_levels k m) as [[[mt d'] n]|] eqn:Hsplit.
    - destruct (split_levels_lims k m mt n d' lims Hlims Hsplit) as [Hnth Hdec]. rewrite Hnth.
      apply split_levels_spec in Hsplit. subst m.
      destruct (trail_of_snoc tr _ mt ⟨mt; d'⟩ d' eq_refl (trail_of_prefix tr tlen ⟨mt; d'⟩ n Htrail))
        as (_ & Hd' & _).
      assert (Hlen: tlen - S (PA.length mt) = PA.length n).
      + destruct Htrail as [Hlen _]. rewrite Hlen, trail_lits_length, (pa_length_app ⟨mt; d'⟩ n). simpl. lia.
      + rewrite Hd', Hlen. change (S (PA.length mt)) with (PA.length ⟨mt; d'⟩).
        rewrite (in_range_spec tr tlen ⟨mt; d'⟩ n (¬u) Htrail), (marked_range_spec tr tlen ⟨mt; d'⟩ n mk (¬u) Htrail).
        destruct (_ && _ && _).
        * simpl. now rewrite Hdec.
        * reflexivity.
    - now rewrite (split_levels_lims_none k m lims Hlims Hsplit).
  Qed.
End Plan.

(* The outcome of a step on the context: stop, fail, or the next context with the positions of its decisions. *)
Inductive CResult: Type :=
| CStop
| CFail
| CNext (x: Ctx) (lims: list nat).

(* Resolve the conflict on clause i, as resolve, with lims the positions of the decisions. *)
Definition resolve_t (x: Ctx) (lims: list nat) (i: nat): CResult :=
match tget (cmap x) i with
| None    => CStop
| Some ls =>
  match lims with
  | []          => CFail
  | j0 :: lims0 =>
    match analyze_t (cmap x) (rsn x) (lvl x) (dl x) (tr x) (S j0) (tlen x - S j0) (set_marks (mrk x) ls true) ls
      (count_level (lvl x) (dl x) ls) with
    | (c, mk) =>
      match plan_t (vals x) (lvl x) (dl x) (tr x) (tlen x) lims (set_marks mk c true) c with
      | Some (u, j, k) =>
        match skipn k (saved x) with
        | c0 :: st =>
          CNext (assign (jump x (unset_range (vals x) (tr x) j (tlen x - j)) j c0 st (dl x - S k)
            (set_marks (set_marks mk c true) c false)) u 0) (skipn (S k) lims)
        | []       => CStop
        end
      | None =>
        match saved x with
        | c0 :: st =>
          CNext (assign (jump x (unset_range (vals x) (tr x) j0 (tlen x - j0)) j0 c0 st (dl x - 1)
            (set_marks (set_marks mk c true) c false)) (¬(tget (tr x) j0)) 0) lims0
        | []       => CStop
        end
      end
    end
  end
end.

(* One step on the context, as step, with lims the positions of the decisions. *)
Definition cstep (x: Ctx) (lims: list nat): CResult :=
match check_shorts_t (shorts x) x with
| (x1, Some i) => resolve_t x1 lims i
| (x1, None)   =>
  match propagate_t (S (nvars x1)) (clear_shorts x1) with
  | (x2, Some i) => resolve_t x2 lims i
  | (x2, None)   =>
    let c := skip_from (vals x2) (alls x2) (nlits x2) (nlits x2 - cur x2) (cur x2) in
    if c <? nlits x2 then CNext (assign (open_level x2 c) (phase (phs x2) (tget (alls x2) c)) 0) (tlen x2 :: lims)
    else if Nat.eqb (tlen x2) (tlen x) then CStop else CNext (with_cursor x2 c) lims
  end
end.

(* The outcome on the context agrees with the step r on the state with formula f. *)
Definition Agrees (f: CNF) (r: option (State * Ctx)) (cr: CResult): Prop :=
match cr with
| CStop          => r = None
| CFail          => exists (x': Ctx), r = Some (fail, x')
| CNext x' lims' => exists (m': PA), r = Some (state m' f, x') /\ LimsOf lims' m'
end.

Lemma resolve_t_spec: forall (m: PA) (f: CNF) (x: Ctx) (lims: list nat) (i: nat),
  TrailOf (tr x) (tlen x) m -> LimsOf lims m -> Agrees f (resolve m f x i) (resolve_t x lims i).
Proof.
  intros m f x lims i Htrail Hlims. unfold resolve, resolve_t. destruct (tget (cmap x) i) as [ls|].
  2: reflexivity.
  destruct (split_last_decision m) as [[m' l]|] eqn:Hsplit.
  - apply PA.split_last_decision_some_iff in Hsplit as [n [-> Hn]].
    destruct (lims_split lims m' n l Hlims) as (lims' & Hskip & Hlims' & _).
    rewrite no_decisions_zero in Hskip by assumption. simpl in Hskip. subst lims.
    assert (Hlen: tlen x = S (PA.length m' + PA.length n)).
    + destruct Htrail as [Hlen _]. rewrite Hlen, trail_lits_length, (pa_length_app ⟨m'; l⟩ n). simpl. lia.
    + assert (Hstart: tlen x - S (PA.length m') = tlen x - level_start (PA.length m' :: lims')) by reflexivity.
      rewrite Hstart. change (S (PA.length m')) with (level_start (PA.length m' :: lims')).
      rewrite (analyze_t_spec _ _ _ _ _ _ _ _ _ _ _ Htrail Hlims).
      destruct (analyze (cmap x) (rsn x) (lvl x) (dl x) _ _ ls _) as [c mk].
      rewrite (plan_t_spec _ _ _ _ _ _ _ _ _ Htrail Hlims).
      destruct (plan (vals x) (lvl x) (dl x) _ (set_marks mk c true) c) as [[u [[mt d'] n']]|] eqn:Hplan.
      * simpl. unfold plan_pos in Hplan. unfold plan in Hplan.
        destruct (find _ c) as [u'|] eqn:Hfind.
        2: discriminate.
        cbv zeta in Hplan. destruct (split_levels _ _) as [[[mt'' d''] n'']|] eqn:Hsplit.
        2: discriminate.
        destruct (_ && _ && _).
        2: discriminate.
        injection Hplan as -> -> -> ->. pose proof (split_levels_lims _ _ _ _ _ _ Hlims Hsplit) as [_ Hdec].
        apply split_levels_spec in Hsplit. rewrite Hsplit in Htrail, Hlims.
        destruct (lims_split _ mt n' d' Hlims) as (lims'' & Hskip2 & Hlims'' & _).
        assert (Hlen': tlen x - PA.length mt = S (PA.length n')).
        -- pose proof Htrail as [Hlen' _]. rewrite Hlen', trail_lits_length, (pa_length_app ⟨mt; d'⟩ n'). cbn [PA.length]. lia.
        -- destruct (skipn (decisions n') (saved x)) as [|c0 st] eqn:Hsaved.
           ++ reflexivity.
           ++ exists ⟨mt, u⟩. split.
              ** rewrite Hlen', (unset_range_spec _ _ mt n' d' _ Htrail).
                 rewrite <- (length_split (tr x) (tlen x) mt n' d' Htrail). reflexivity.
              ** cbn [LimsOf]. replace (skipn (decisions n') lims') with (skipn 1 (skipn (decisions n') (PA.length m' :: lims'))).
                 --- rewrite Hskip2. assumption.
                 --- now rewrite skipn_skipn.
      * destruct (saved x) as [|c0 st].
        -- reflexivity.
        -- exists ⟨m', (¬l)⟩. split.
           ++ destruct (trail_of_snoc (tr x) _ m' ⟨m'; l⟩ l eq_refl
                (trail_of_prefix (tr x) (tlen x) ⟨m'; l⟩ n Htrail)) as (_ & Hl & _).
              rewrite Hl. replace (tlen x - PA.length m') with (S (PA.length n)) by lia.
              rewrite (unset_range_spec _ _ m' n l _ Htrail), <- (unassign_level_segment _ m' n l Hn).
              rewrite (level_length_split _ m' l n eq_refl Hn), (length_split (tr x) (tlen x) m' n l Htrail).
              reflexivity.
           ++ assumption.
  - apply PA.split_last_decision_none_iff in Hsplit. destruct lims as [|j lims].
    + now exists x.
    + exfalso. clear - Hlims Hsplit. induction m as [|m IH y|m IH y]; simpl in Hlims, Hsplit.
      * discriminate.
      * now apply IH.
      * destruct Hsplit.
Qed.

(* The step on the context agrees with step. *)
Lemma cstep_spec: forall (m: PA) (f: CNF) (x: Ctx) (lims: list nat),
  StepInv (state m f) x -> LimsOf lims m -> Agrees f (step (state m f, x)) (cstep x lims).
Proof.
  intros m f x lims [Hcore [Hwf Hentails]] Hlims. cbn [step]. unfold cstep.
  destruct (check_shorts (shorts x) m x) as [[m1 x1] r1] eqn:Hcheck.
  destruct (front_shorts m m1 f x x1 r1 Hcore Hcheck) as (Hder1 & Hext1 & Hcore1 & Hnone1 & _).
  rewrite (check_shorts_free _ _ _ _ _ _ Hcheck).
  assert (Hlims1: LimsOf lims m1) by now apply (lims_extends lims m).
  destruct r1 as [i|].
  - apply resolve_t_spec.
    + apply Hcore1.
    + assumption.
  - assert (Hwf1: WellFormed (state m1 f)) by now apply (derivation_well_formed DPLL_BJ m m1 f f).
    destruct (propagate (S (nvars x1)) m1 (clear_shorts x1)) as [[m2 x2] r2] eqn:Hprop.
    destruct (front_prop m1 m2 f x1 x2 r2 Hcore1 Hwf1 (Hnone1 eq_refl) Hprop) as (_ & Hext2 & Hcore2 & _).
    rewrite (propagate_free _ _ _ _ _ _ Hprop).
    assert (Hlims2: LimsOf lims m2) by now apply (lims_extends lims m1).
    destruct r2 as [i|].
    + apply resolve_t_spec.
      * apply Hcore2.
      * assumption.
    + destruct (_ <? nlits x2).
      * exists ⟨m2; (phase (phs x2) (tget (alls x2) (skip_from (vals x2) (alls x2) (nlits x2) (nlits x2 - cur x2)
          (cur x2))))⟩. split.
        -- reflexivity.
        -- simpl. split.
           ++ destruct Hcore2 as [[[_ _ [Hlen _] _ _] _ _ _ _] _ _ _ _ _ _ _]. now rewrite Hlen, trail_lits_length.
           ++ assumption.
      * destruct (Nat.eqb (tlen x2) (tlen x)).
        -- reflexivity.
        -- now exists m2.
Qed.
