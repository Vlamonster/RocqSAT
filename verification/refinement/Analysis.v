(* Conflict analysis for backjumping: resolve the conflict clause with the reasons of propagated literals, and
   find how far to jump back. The reasons and decision levels are only hints: a backjump clause is entailed
   whatever they are, and plan checks everything the jump needs. *)
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
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

Section Analysis.
  (* The number of literals of c at decision level d, according to the levels lv. *)
  Definition count_level (lv: Table nat) (d: nat) (c: list Lit): nat :=
  length (filter (fun (y: Lit) => Nat.eqb (tget lv (extract y)) d) c).

  (* No literal is marked. *)
  Definition Unmarked (mk: Table bool): Prop := forall (y: Lit), tget mk (lit_key y) = false.

  (* Every marked literal is in c. *)
  Definition MarkedIn (mk: Table bool) (c: list Lit): Prop := forall (y: Lit), tget mk (lit_key y) = true -> In y c.

  (* mk with the literals of c marked as b. *)
  Fixpoint set_marks (mk: Table bool) (c: list Lit) (b: bool): Table bool :=
  match c with
  | []      => mk
  | y :: c' => set_marks (tset mk (lit_key y) b) c' b
  end.

  (* A literal keeps its mark unless it is in c. *)
  Lemma set_marks_other: forall (mk: Table bool) (c: list Lit) (b: bool) (y: Lit),
    ~ In y c -> tget (set_marks mk c b) (lit_key y) = tget mk (lit_key y).
  Proof.
    intros mk c b y. revert mk. induction c as [|z c IH]; intros mk Hy; simpl.
    - reflexivity.
    - rewrite IH.
      + apply tget_tset_other. intros Heq. apply lit_key_inj in Heq. apply Hy. now left.
      + intros Hin. apply Hy. now right.
  Qed.

  Lemma set_marks_in: forall (mk: Table bool) (c: list Lit) (b: bool) (y: Lit),
    In y c -> tget (set_marks mk c b) (lit_key y) = b.
  Proof.
    intros mk c b y. revert mk. induction c as [|z c IH]; intros mk Hy; simpl.
    - destruct Hy.
    - destruct (in_dec Lit.eq_dec y c) as [Hin|Hnot_in].
      + now apply IH.
      + rewrite set_marks_other.
        * destruct Hy as [->|Hin].
          -- apply tget_tset_same.
          -- contradiction.
        * assumption.
  Qed.

  (* Marking the literals of c when none are marked marks exactly them. *)
  Lemma set_marks_marked_in: forall (mk: Table bool) (c: list Lit), Unmarked mk -> MarkedIn (set_marks mk c true) c.
  Proof.
    intros mk c Hmk y Hy. destruct (in_dec Lit.eq_dec y c) as [Hin|Hnot_in].
    - assumption.
    - rewrite set_marks_other, Hmk in Hy.
      + discriminate.
      + assumption.
  Qed.

  (* Unmarking the literals of c when only they are marked leaves no literal marked. *)
  Lemma set_marks_unmarked: forall (mk: Table bool) (c: list Lit), MarkedIn mk c -> Unmarked (set_marks mk c false).
  Proof.
    intros mk c Hmk y. destruct (in_dec Lit.eq_dec y c) as [Hin|Hnot_in].
    - now apply set_marks_in.
    - rewrite set_marks_other.
      + destruct (tget mk (lit_key y)) eqn:Hy.
        * now apply Hmk in Hy.
        * reflexivity.
      + assumption.
  Qed.

  (* Marking the literals of c keeps the marks inside c. *)
  Lemma set_marks_true_marked_in: forall (mk: Table bool) (c: list Lit), MarkedIn mk c -> MarkedIn (set_marks mk c true) c.
  Proof.
    intros mk c Hmk y Hy. destruct (in_dec Lit.eq_dec y c) as [Hin|Hnot_in].
    - assumption.
    - rewrite set_marks_other in Hy.
      + now apply Hmk.
      + assumption.
  Qed.

  (* Add the literals of r other than x that are not marked to c, marking them; k counts the literals at level d. *)
  Fixpoint add_unmarked (lv: Table nat) (d: nat) (mk: Table bool) (x: Lit) (r c: list Lit) (k: nat):
    list Lit * Table bool * nat :=
  match r with
  | []      => (c, mk, k)
  | y :: r' =>
    if (y =? x) || tget mk (lit_key y) then add_unmarked lv d mk x r' c k
    else add_unmarked lv d (tset mk (lit_key y) true) x r' (y :: c) (if Nat.eqb (tget lv (extract y)) d then S k else k)
  end.

  (* The result keeps c and the marks inside it, and contains every literal of r other than x. *)
  Lemma add_unmarked_spec: forall (lv: Table nat) (d: nat) (x: Lit) (r c c': list Lit) (mk mk': Table bool) (k k': nat),
    MarkedIn mk c ->
    add_unmarked lv d mk x r c k = (c', mk', k') ->
    (forall (y: Lit), In y c -> In y c') /\ (forall (y: Lit), In y r -> y <> x -> In y c') /\ MarkedIn mk' c'.
  Proof.
    intros lv d x r. induction r as [|y r IH]; intros c c' mk mk' k k' Hmk Hadd; simpl in Hadd.
    - injection Hadd as <- <- _. split.
      + easy.
      + split.
        * intros y [].
        * assumption.
    - destruct ((y =? x) || tget mk (lit_key y)) eqn:Hskip.
      + destruct (IH c c' mk mk' k k' Hmk Hadd) as (Hc & Hr & Hmk'). split.
        * assumption.
        * split.
          -- intros z [<-|Hin] Hneq.
             ++ apply orb_true_iff in Hskip as [Heq|Hmarked].
                ** apply Lit.eqb_eq in Heq. contradiction.
                ** now apply Hc, Hmk.
             ++ now apply Hr.
          -- assumption.
      + assert (Hmk_y: MarkedIn (tset mk (lit_key y) true) (y :: c)).
        * intros z Hz. rewrite tget_tset in Hz. destruct (Nat.eq_dec (lit_key y) (lit_key z)) as [Heq|Hneq].
          -- apply lit_key_inj in Heq as ->. now left.
          -- right. now apply Hmk.
        * destruct (IH _ c' _ mk' _ k' Hmk_y Hadd) as (Hc & Hr & Hmk'). split.
          -- intros z Hz. apply Hc. now right.
          -- split.
             ++ intros z [<-|Hin] Hneq.
                ** apply Hc. now left.
                ** now apply Hr.
             ++ assumption.
  Qed.

  (* Resolve c with r on x using the marks: drop ¬x from c, then add the unmarked literals of r other than x. *)
  Definition resolve_marked (lv: Table nat) (d: nat) (mk: Table bool) (c r: list Lit) (x: Lit) (k: nat):
    list Lit * Table bool * nat :=
  add_unmarked lv d (tset mk (lit_key (¬x)) false) x r (filter (fun (y: Lit) => negb (y =? ¬x)) c) (k - 1).

  (* The resolvent is entailed, and the marks stay inside it. *)
  Lemma resolve_marked_spec: forall (f: CNF) (lv: Table nat) (d: nat) (mk mk': Table bool) (c r c': list Lit)
    (x: Lit) (k k': nat),
    Entailed f c ->
    Entailed f r ->
    MarkedIn mk c ->
    resolve_marked lv d mk c r x k = (c', mk', k') ->
    Entailed f c' /\ MarkedIn mk' c'.
  Proof.
    intros f lv d mk mk' c r c' x k k' Hc Hr Hmk Hres. unfold resolve_marked in Hres.
    assert (Hmk_x: MarkedIn (tset mk (lit_key (¬x)) false) (filter (fun (y: Lit) => negb (y =? ¬x)) c)).
    - intros z Hz. rewrite tget_tset in Hz. destruct (Nat.eq_dec (lit_key (¬x)) (lit_key z)) as [Heq|Hneq].
      + discriminate.
      + apply filter_In. split.
        * now apply Hmk.
        * apply negb_true_iff, Lit.eqb_neq. intros ->. contradiction.
    - destruct (add_unmarked_spec lv d x r _ c' _ mk' (k - 1) k' Hmk_x Hres) as (Hc' & Hr' & Hmk'). split.
      + apply (entailed_resolve f c r c' x Hc Hr).
        * intros y Hy Hneq. apply Hc', filter_In. split.
          -- assumption.
          -- now apply negb_true_iff, Lit.eqb_neq.
        * assumption.
      + assumption.
  Qed.

  (* Resolve c, whose literals are marked, with the reasons of the literals of the last decision level of m,
     newest first, until at most one literal of c is at level d; k is that number of literals. The reason of an
     atom is clause i of cm if rsn gives S i, and none if it gives 0. *)
  Fixpoint analyze (cm: ClauseMap) (rsn lv: Table nat) (d: nat) (m: PA) (mk: Table bool) (c: list Lit) (k: nat):
    list Lit * Table bool :=
  match m with
  | ⟨m', t⟩ =>
    if Nat.leb k 1 then (c, mk)
    else if tget mk (lit_key (¬t)) then
      match tget rsn (extract t) with
      | 0   => (c, mk)
      | S i =>
        match tget cm i with
        | Some r =>
          match resolve_marked lv d mk c r t k with
          | (c', mk', k') => analyze cm rsn lv d m' mk' c' k'
          end
        | None   => (c, mk)
        end
      end
    else analyze cm rsn lv d m' mk c k
  | _ => (c, mk)
  end.

  (* If every clause of cm is entailed, so is the result of the analysis, and the marks stay inside it. *)
  Lemma analyze_spec: forall (f: CNF) (cm: ClauseMap) (rsn lv: Table nat) (d: nat) (m: PA) (mk mk': Table bool)
    (c c': list Lit) (k: nat),
    (forall (i: nat) (r: list Lit), tget cm i = Some r -> Entailed f r) ->
    Entailed f c ->
    MarkedIn mk c ->
    analyze cm rsn lv d m mk c k = (c', mk') ->
    Entailed f c' /\ MarkedIn mk' c'.
  Proof.
    intros f cm rsn lv d m. induction m as [|m IH t|m IH t]; intros mk mk' c c' k Hcm Hc Hmk Hanalyze; simpl in Hanalyze.
    - injection Hanalyze as <- <-. now split.
    - destruct (Nat.leb k 1).
      + injection Hanalyze as <- <-. now split.
      + destruct (tget mk (lit_key (¬t))).
        * destruct (tget rsn (extract t)) as [|i].
          -- injection Hanalyze as <- <-. now split.
          -- destruct (tget cm i) as [r|] eqn:Hr.
             ++ destruct (resolve_marked lv d mk c r t k) as [[c1 mk1] k1] eqn:Hres.
                destruct (resolve_marked_spec f lv d mk mk1 c r c1 t k k1 Hc (Hcm i r Hr) Hmk Hres) as [Hc1 Hmk1].
                now apply (IH mk1 mk' c1 c' k1).
             ++ injection Hanalyze as <- <-. now split.
        * now apply (IH mk mk' c c' k).
    - injection Hanalyze as <- <-. now split.
  Qed.
End Analysis.

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

  (* Whether l is assigned in m. *)
  Fixpoint in_trail (l: Lit) (m: PA): bool :=
  match m with
  | ⟨⟩     => false
  | ⟨m, x⟩ => (x =? l) || in_trail l m
  | ⟨m; x⟩ => (x =? l) || in_trail l m
  end.

  Lemma in_trail_spec: forall (l: Lit) (m: PA), in_trail l m = true <-> l ∈ m.
  Proof.
    intros l m. induction m as [|m IH x|m IH x]; cbn.
    - split.
      + discriminate.
      + intros [].
    - rewrite orb_true_iff, Lit.eqb_eq, IH. reflexivity.
    - rewrite orb_true_iff, Lit.eqb_eq, IH. reflexivity.
  Qed.

  (* The older part of a fresh trail is fresh, and the literals after it were unassigned in it. *)
  Lemma fresh_app: forall (m n: PA), Fresh ⟨m ++ n⟩ -> Fresh m.
  Proof.
    intros m n. induction n as [|n IH x|n IH x]; simpl.
    - easy.
    - intros [Hfresh _]. now apply IH.
    - intros [Hfresh _]. now apply IH.
  Qed.

  Lemma fresh_app_undef: forall (m n: PA) (l: Lit), Fresh ⟨m ++ n⟩ -> l ∈ n -> l_eval m l = None.
  Proof.
    intros m n l. induction n as [|n IH x|n IH x]; simpl.
    - intros _ [].
    - intros [Hfresh Hx] [->|Hin].
      + destruct (l_eval n l) as [b|] eqn:Hn.
        * rewrite (l_eval_app_some m n l b Hn) in Hx. discriminate.
        * now rewrite l_eval_app_undef in Hx.
      + now apply IH.
    - intros [Hfresh Hx] [->|Hin].
      + destruct (l_eval n l) as [b|] eqn:Hn.
        * rewrite (l_eval_app_some m n l b Hn) in Hx. discriminate.
        * now rewrite l_eval_app_undef in Hx.
      + now apply IH.
  Qed.

  (* In a fresh trail, every assigned literal is true. *)
  Lemma fresh_in_true: forall (m: PA) (l: Lit), Fresh m -> l ∈ m -> l_eval m l = Some true.
  Proof.
    intros m l. induction m as [|m IH x|m IH x]; intros Hfresh Hin.
    - destruct Hin.
    - destruct Hfresh as [Hfresh Hx]. destruct Hin as [<-|Hin].
      + simpl. unfold l_eval_step. now rewrite Lit.eqb_refl.
      + apply l_eval_cons_undef.
        * assumption.
        * now apply IH.
    - destruct Hfresh as [Hfresh Hx]. destruct Hin as [<-|Hin].
      + simpl. unfold l_eval_step. now rewrite Lit.eqb_refl.
      + apply (l_eval_cons_undef m l x).
        * assumption.
        * now apply IH.
  Qed.

  (* The key of ¬l, without building ¬l. *)
  Definition neg_key (l: Lit): nat :=
  match l with
  | Pos p => S (2 * p)
  | Neg p => 2 * p
  end.

  Lemma neg_key_spec: forall (l: Lit), neg_key l = lit_key (¬l).
  Proof. now intros [p|p]. Qed.

  (* Whether a literal of n other than nu has its negation marked. *)
  Fixpoint marked_neg (mk: Table bool) (nu: Lit) (n: PA): bool :=
  match n with
  | ⟨⟩     => false
  | ⟨n, x⟩ => (tget mk (neg_key x) && negb (x =? nu)) || marked_neg mk nu n
  | ⟨n; x⟩ => (tget mk (neg_key x) && negb (x =? nu)) || marked_neg mk nu n
  end.

  Lemma marked_neg_spec: forall (mk: Table bool) (nu: Lit) (n: PA) (x: Lit),
    marked_neg mk nu n = false -> x ∈ n -> x <> nu -> tget mk (lit_key (¬x)) = false.
  Proof.
    intros mk nu n x. induction n as [|n IH y|n IH y]; cbn; intros Hmarked Hin Hneq.
    - destruct Hin.
    - apply orb_false_iff in Hmarked as [Hy Hn]. destruct Hin as [<-|Hin].
      + rewrite <- neg_key_spec. apply Lit.eqb_neq in Hneq. now rewrite Hneq, andb_true_r in Hy.
      + now apply IH.
    - apply orb_false_iff in Hmarked as [Hy Hn]. destruct Hin as [<-|Hin].
      + rewrite <- neg_key_spec. apply Lit.eqb_neq in Hneq. now rewrite Hneq, andb_true_r in Hy.
      + now apply IH.
  Qed.

  (* The backjump for the clause c: its literal u at level d according to lv, and m split as ⟨mt; d' ++ n⟩ just
     above the highest level of its other literals, provided that every literal of c is false, ¬u was assigned
     after the split and the negations of the other literals were not; the literals of c are marked in mk, so
     that the latter takes a single pass over the split-off segment. *)
  Definition plan (v: Values) (lv: Table nat) (d: nat) (m: PA) (mk: Table bool) (c: list Lit):
    option (Lit * (PA * Lit * PA)) :=
  match find (fun (y: Lit) => Nat.eqb (tget lv (extract y)) d) c with
  | None   => None
  | Some u =>
    let rest := filter (fun (y: Lit) => negb (y =? u)) c in
    match split_levels (d - S (list_max (map (fun (y: Lit) => tget lv (extract y)) rest))) m with
    | None             => None
    | Some (mt, d', n) =>
      let nu := ¬u in
      if forallb (fun (y: Lit) => negb (not_false v y)) c && ((d' =? nu) || in_trail nu n)
        && negb (marked_neg mk nu ⟨∅; d'⟩ || marked_neg mk nu n)
      then Some (u, (mt, d', n))
      else None
    end
  end.

  (* A planned backjump: after the split, u is unassigned and the other literals of c are false. *)
  Lemma plan_spec: forall (v: Values) (lv: Table nat) (d: nat) (m mt n: PA) (mk: Table bool) (c: list Lit)
    (u d': Lit),
    ValuesOf v m ->
    Fresh m ->
    (forall (y: Lit), In y c -> tget mk (lit_key y) = true) ->
    plan v lv d m mk c = Some (u, (mt, d', n)) ->
    m = ⟨mt; d' ++ n⟩ /\ In u c /\ l_eval m u = Some false /\ l_eval mt u = None /\
    (forall (y: Lit), In y c -> y <> u -> l_eval mt y = Some false).
  Proof.
    intros v lv d m mt n mk c u d' Hv Hfresh Hmk Hplan. unfold plan in Hplan.
    destruct (find (fun (y: Lit) => Nat.eqb (tget lv (extract y)) d) c) as [u'|] eqn:Hfind.
    2: discriminate.
    apply find_some in Hfind as [Hu_in _]. cbv zeta in Hplan.
    destruct (split_levels _ m) as [[[mt' d''] n']|] eqn:Hsplit.
    2: discriminate.
    destruct (forallb _ c && _ && _) eqn:Hchecks.
    2: discriminate.
    injection Hplan as -> -> -> ->. apply split_levels_spec in Hsplit as ->.
    apply andb_true_iff in Hchecks as [Hchecks Hrest]. apply andb_true_iff in Hchecks as [Hfalse Hpopped].
    rewrite forallb_forall in Hfalse. apply negb_true_iff, orb_false_iff in Hrest as [Hrest_d Hrest_n].
    (* Every literal of c is false *)
    assert (Hc_false: forall (y: Lit), In y c -> l_eval ⟨mt; d' ++ n⟩ y = Some false).
    - intros y Hy. apply Hfalse in Hy. rewrite <- Hv. unfold not_false in Hy.
      destruct (lookup v y) as [[|]|]; easy.
    - assert (Hfresh_mt: Fresh ⟨mt; d'⟩).
      + now apply fresh_app in Hfresh.
      + split.
        * reflexivity.
        * split.
          -- assumption.
          -- split.
             ++ now apply Hc_false.
             ++ split.
                (* ¬u was assigned after the split *)
                ** apply l_eval_neg_none_iff. apply orb_true_iff in Hpopped as [Heq|Hin].
                   --- apply Lit.eqb_eq in Heq as <-. now destruct Hfresh_mt.
                   --- apply in_trail_spec in Hin. apply (fresh_app_undef ⟨mt; d'⟩ n (¬u) Hfresh) in Hin.
                       simpl in Hin. unfold l_eval_step in Hin.
                       destruct (¬u =? d'), (¬u =? ¬d'); easy.
                (* The negation of every other literal was assigned before it *)
                ** intros y Hy Hneq. apply Hmk in Hy as Hmarked.
                   assert (Hnot_in: ~ ¬y ∈ ⟨∅; d' ++ n⟩).
                   --- assert (Hneq_u: ¬y <> ¬u).
                       +++ intros Heq. apply Hneq. now rewrite <- (Neg.involutive y), Heq, Neg.involutive.
                       +++ intros Hin. apply PA.in_app_iff in Hin as [Hin|Hin].
                           *** apply (marked_neg_spec mk (¬u) n (¬y)) in Hrest_n.
                               ---- rewrite Neg.involutive in Hrest_n. congruence.
                               ---- assumption.
                               ---- assumption.
                           *** apply (marked_neg_spec mk (¬u) ⟨∅; d'⟩ (¬y)) in Hrest_d.
                               ---- rewrite Neg.involutive in Hrest_d. congruence.
                               ---- assumption.
                               ---- assumption.
                   --- apply Hc_false, l_eval_false_in, PA.in_app_iff in Hy as [Hin|[Heq|Hin]].
                       +++ exfalso. apply Hnot_in, PA.in_app_iff. now left.
                       +++ exfalso. apply Hnot_in, PA.in_app_iff. right. now left.
                       +++ apply l_eval_neg_some_iff. simpl. apply fresh_in_true.
                           *** now destruct Hfresh_mt.
                           *** assumption.
  Qed.

  (* v without the values of the literals of n and then d: the values before the decision d of ⟨mt; d ++ n⟩. *)
  Fixpoint unassign_segment (v: Values) (d: Lit) (n: PA): Values :=
  match n with
  | ⟨⟩     => unset_value v d
  | ⟨n, x⟩ => unassign_segment (unset_value v x) d n
  | ⟨n; x⟩ => unassign_segment (unset_value v x) d n
  end.

  Lemma unassign_segment_spec: forall (v: Values) (mt n: PA) (d: Lit),
    ValuesOf v ⟨mt; d ++ n⟩ -> Fresh ⟨mt; d ++ n⟩ -> ValuesOf (unassign_segment v d n) mt.
  Proof.
    intros v mt n d. revert v. induction n as [|n IH x|n IH x]; intros v Hv Hfresh; simpl in Hfresh |- *.
    - destruct Hfresh as [_ Hd]. apply values_of_unset.
      + intros y. apply Hv.
      + assumption.
    - destruct Hfresh as [Hfresh Hx]. apply IH.
      + apply values_of_unset.
        * intros y. apply Hv.
        * assumption.
      + assumption.
    - destruct Hfresh as [Hfresh Hx]. apply IH.
      + apply values_of_unset.
        * intros y. apply Hv.
        * assumption.
      + assumption.
  Qed.
End Jump.
