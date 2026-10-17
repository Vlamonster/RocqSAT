(* add_lits adds the literals of a part of a clause to the analysis of a conflict: it
   marks them, counts those of the conflict level and appends the others to the lower
   literals, or gives up when a count would reach the number of atoms (add_lits). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Heur Propagate Analysis Step.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep RepReasons RepHeur Mark.
Import ListNotations.

(* The literals with the keys tc q .. tc (e - 1). *)
Definition span_lits (tc: nat -> Z) (q e: nat): list Lit :=
  map (fun (k: nat) => lit_of (tc k)) (seq q (e - q)).

(* A nonempty range starts with the literal at q. *)
Lemma span_lits_cons: forall (tc: nat -> Z) (q e: nat), (q < e)%nat ->
  span_lits tc q e = lit_of (tc q) :: span_lits tc (Datatypes.S q) e.
Proof.
  intros tc q e Hqe. unfold span_lits.
  replace (e - q)%nat with (Datatypes.S (e - Datatypes.S q)) by lia. reflexivity.
Qed.

(* An empty range has no literals. *)
Lemma span_lits_nil: forall (tc: nat -> Z) (e: nat), span_lits tc e e = [].
Proof. intros tc e. unfold span_lits. now rewrite Nat.sub_diag. Qed.

(* The literals add_lits reads are in block clits or rlits. *)
Definition ClauseBlock (S: Shape) (b: block): Prop := b = b_clits S \/ b = b_rlits S.

(* That block is not one that add_lits writes: the marks, the lower literals and the
   struct. *)
Lemma clause_block_other: forall (S: Shape) (b b': block),
  ClauseBlock S b -> NoDup (iblocks S) -> In b' [b_mrk S; b_lt S; b_s S] -> b <> b'.
Proof.
  intros S b b' Hb Hnd Hb'. unfold iblocks in Hnd.
  destruct Hb as [-> | ->], Hb' as [<- | [<- | [<- | []]]]; neq Hnd.
Qed.

(* What add_lits leaves unchanged: all but the marks, the lower literals, the struct and
   the heuristic. *)
Definition AddKept (S: Shape) (b: block) (ofs: Z): Prop :=
  b <> b_lt S /\ MarkFrame S b ofs.

(* A store of add_lits, to one of these blocks, keeps the literals it reads and the rest
   of the memory. *)
Lemma add_frame_store: forall (m m1 m2: mem) (S: Shape) (b b': block) (n: nat)
  (tc: nat -> Z) (ofs: Z) (c: memory_chunk) (v: val),
  ClauseBlock S b -> NoDup (iblocks S) -> In b' [b_mrk S; b_lt S; b_s S] ->
  Arr m1 b n tc -> Mem.unchanged_on (AddKept S) m m1 ->
  Mem.store c m1 b' ofs v = Some m2 ->
  Arr m2 b n tc /\ Mem.unchanged_on (AddKept S) m m2.
Proof.
  intros m m1 m2 S b b' n tc ofs c v Hb Hnd Hb' A Hun Hst. split.
  - apply (arr_store_other _ _ _ _ _ _ _ _ _ A Hst).
    apply (clause_block_other S); assumption.
  - apply (store_unchanged _ _ _ _ _ _ _ _ Hun Hst).
    intros i (Hlt & Hmrk & _ & _ & _ & _ & Hs). destruct Hb' as [<- | [<- | [<- | []]]].
    + now apply Hmrk.
    + now apply Hlt.
    + now apply Hs.
Qed.

(* A call of mark keeps the literals add_lits reads, and the rest of the memory. *)
Lemma add_frame_mark: forall (m m1 m2: mem) (S: Shape) (b: block) (n: nat)
  (tc: nat -> Z),
  ClauseBlock S b -> NoDup (iblocks S) ->
  Arr m1 b n tc -> Mem.unchanged_on (AddKept S) m m1 ->
  Mem.unchanged_on (MarkFrame S) m1 m2 ->
  Arr m2 b n tc /\ Mem.unchanged_on (AddKept S) m m2.
Proof.
  intros m m1 m2 S b n tc Hb Hnd A Hun Hmark. unfold iblocks in Hnd. split.
  - apply (arr_unchanged _ m1 m2 b n tc Hmark).
    + intros ofs. destruct Hb as [-> | ->].
      * repeat split.
        -- neq Hnd.
        -- neq Hnd.
        -- neq Hnd.
        -- neq Hnd.
        -- neq Hnd.
        -- neq Hnd.
      * repeat split.
        -- neq Hnd.
        -- neq Hnd.
        -- neq Hnd.
        -- neq Hnd.
        -- neq Hnd.
        -- neq Hnd.
    + assumption.
  - apply (Mem.unchanged_on_trans _ m m1 m2).
    + assumption.
    + apply (Mem.unchanged_on_implies _ _ _ _ Hmark). intros b' ofs [_ Hb'] _.
      assumption.
Qed.

(* The literal t to skip, as C passes it, is small. *)
Lemma enc_lit_small: forall (t: option Lit) (N: nat),
  (forall (y: Lit), t = Some y -> (extract y < N)%nat) -> Z.of_nat N < 268435456 ->
  Small (enc_lit t).
Proof.
  intros [y|] N Ht HN; unfold Small; cbn [enc_lit].
  - pose proof (key_small y N (Ht y eq_refl) HN). lia.
  - lia.
Qed.

(* C compares keys to see whether y is t: y != t. *)
Lemma enc_lit_ne: forall (t: option Lit) (y: Lit),
  zcmp Cne (key y) (enc_lit t) = negb (is_lit t y).
Proof.
  intros [t'|] y; cbn [zcmp enc_lit is_lit].
  - now rewrite key_eqb.
  - replace (Z.eqb (key y) (-1)) with false
      by (symmetry; apply Z.eqb_neq; unfold key; lia).
    reflexivity.
Qed.

(* The parts of add_lits proved in lemmas of their own: its loop, the body of the loop
   after its test, the statement for one literal in it, the test of the level of an
   unmarked literal in that, and its two branches. *)
Definition add_loop: statement := first_stmt (fn_body f_add_lits).
Definition add_body: statement := drop_stmts 1 (loop_body add_loop).
Definition add_lit: statement := first_stmt (drop_stmts 1 add_body).
Definition add_unmarked: statement :=
  drop_stmts 2 (then_stmt (drop_stmts 2 (then_stmt add_lit))).
Definition add_level: statement := then_stmt add_unmarked.
Definition add_lower: statement := else_stmt add_unmarked.

Section Loop.
  (* A call of add_lits from the memory m on the literals with the keys
     tc q .. tc (e - 1) of block b, which has n entries, for x, skipping t, at level d,
     whose model gives res. *)
  Variables (m: mem) (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
    (lims: list nat) (b: block) (n: nat) (tc: nat -> Z) (e: nat) (t: option Lit)
    (d: nat) (res: Table bool * list Lit * Heur * option nat).

  (* The state of the loop of add_lits at the literal at q, with the temporary q holding
     qt: the temporaries hold the arguments and the count pathc, the literals from q on
     are keys with atoms below N, block b still holds them, only the marks, the lower
     literals, the struct and the heuristic changed since m, the memory represents x
     with the marks mk, the lower literals lt and the heuristic h, and the model gives res
     from q on (the loop follows the recursion of the model). *)
  Record AddInv (qt q: nat) (mk: Table bool) (lt: list Lit) (h: Heur) (pathc: nat)
    (le: temp_env) (m1: mem): Prop := {
    ai_s: le ! _s = Some (sptr S);
    ai_cl: le ! _cl = Some (Vptr b Ptrofs.zero);
    ai_q: le ! _q = Some (vint (Z.of_nat qt));
    ai_e: le ! _e = Some (vint (Z.of_nat e));
    ai_t: le ! _t = Some (vint (enc_lit t));
    ai_d: le ! _d = Some (vint (Z.of_nat d));
    ai_pathc: le ! _pathc = Some (vint (Z.of_nat pathc));
    ai_range: (q <= e <= n)%nat;
    ai_keys: forall (k: nat), (q <= k < e)%nat ->
      exists (y: Lit), tc k = key y /\ (extract y < N)%nat;
    ai_lits: Arr m1 b n tc;
    ai_kept: Mem.unchanged_on (AddKept S) m m1;
    ai_rep: RepL m1 S N lss (with_heur (set_mrk x mk) h) lims lt;
    ai_pathc_le: (pathc <= N)%nat;
    ai_res: add_lits (lvl x) d N t (span_lits tc q e) mk lt h pathc = res;
  }.

  (* The variant and the invariant of the loop. *)
  Definition add_variant: nat -> nat -> Prop := ltof nat (fun (q: nat) => e - q)%nat.
  Definition add_inv (q: nat) (le: temp_env) (m1: mem): Prop :=
    exists (mk: Table bool) (lt: list Lit) (h: Heur) (pathc: nat),
      AddInv q q mk lt h pathc le m1.

  (* What the loop of add_lits ends in, with res = (mk, lt, h, r): the memory represents
     x with the marks mk, the lower literals lt and the heuristic h, and only those and
     the struct changed since m; it ends normally with the count r in pathc, or returns
     -1 for r = None. *)
  Definition AddPost (le: temp_env) (m1: mem) (out: outcome): Prop :=
    match res with
    | (mk, lt, h, r) =>
      RepL m1 S N lss (with_heur (set_mrk x mk) h) lims lt /\
      Mem.unchanged_on (AddKept S) m m1 /\
      ((out = Out_normal /\
        exists (pathc: nat),
          r = Some pathc /\ le ! _pathc = Some (vint (Z.of_nat pathc)))
       \/ (out = Out_return (Some (vint (-1), Ctypesdefs.tint)) /\ r = None))
    end.

  (* What the statement for the literal at q ends in: normally with the state at q + 1
     (q not yet incremented), or returning -1 as the loop does. *)
  Definition AddMid (q: nat) (le: temp_env) (m1: mem) (out: outcome): Prop :=
    (out = Out_normal /\
     exists (mk: Table bool) (lt: list Lit) (h: Heur) (pathc: nat),
       AddInv q (Datatypes.S q) mk lt h pathc le m1) \/
    (out = Out_return (Some (vint (-1), Ctypesdefs.tint)) /\ AddPost le m1 out).

  (* Giving up: when the model stops with no count, returning -1 is what it says. *)
  Lemma add_mid_none: forall (q: nat) (mk: Table bool) (lt: list Lit) (h: Heur)
    (le: temp_env) (m1: mem),
    RepL m1 S N lss (with_heur (set_mrk x mk) h) lims lt ->
    Mem.unchanged_on (AddKept S) m m1 -> (mk, lt, h, None) = res ->
    AddMid q le m1 (Out_return (Some (vint (-1), Ctypesdefs.tint))).
  Proof.
    intros q mk lt h le m1 HRep Hkept Hres. right. split.
    - reflexivity.
    - unfold AddPost. rewrite <- Hres. split.
      + assumption.
      + split.
        * assumption.
        * right. split.
          -- reflexivity.
          -- reflexivity.
  Qed.

  (* The temporaries for the literal y after its loads: y, then the marks pointer and the
     mark of y (v1, v2), then the levels pointer and the level of its atom (v3, v4). *)
  Definition lit_temps (le: temp_env) (y: Lit) (v1 v2 v3 v4: val): temp_env :=
    PTree.set _t'4 v4 (PTree.set _t'3 v3 (PTree.set _t'2 v2 (PTree.set _t'1 v1
      (PTree.set _y (vint (key y)) le)))).

  Hypothesis (Hb: ClauseBlock S b).
  Hypothesis (Ht: forall (y: Lit), t = Some y -> (extract y < N)%nat).
  Hypothesis (Hd: (d <= N)%nat).
  Hypothesis (Hn: Z.of_nat n < 1073741824).

  (* The literal y at q < e, not t, not marked, of level d: it is counted.

       {{ AddInv q q mk lt pathc }}
         if (pathc >= s->nv) return -1;
       {{ result = -1, as the model stops with no count }}
         mark(s, y);                                                        (mark_correct)
         pathc++;
       {{ AddInv q (q + 1) (tset mk (lit_key y) true) lt h' (pathc + 1), for h' the
          heuristic h with the atom of y bumped }}                                    *)
  Lemma add_level_correct: forall (q: nat) (y: Lit) (mk: Table bool) (lt: list Lit)
    (h: Heur) (pathc: nat) (le: temp_env) (m1: mem) (v1 v2 v3 v4: val),
    AddInv q q mk lt h pathc le m1 -> (q < e)%nat -> tc q = key y ->
    (extract y < N)%nat -> is_lit t y = false -> tget mk (lit_key y) = false ->
    tget (lvl x) (extract y) = d ->
    Exec ge (lit_temps le y v1 v2 v3 v4) m1 add_level (AddMid q).
  Proof.
    intros q y mk lt h pathc le m1 v1 v2 v3 v4 HI Hqe Htcq Hy Hist Hmarked Hlv.
    destruct HI as [Hs Hcl Hq He Ht' Hd' Hpc Hrange Hkeys Alits Hkept HRep1 Hpcle Hres].
    pose proof (r_n _ _ _ _ _ _ _ HRep1) as HN.
    pose proof (r_nodup _ _ _ _ _ _ _ HRep1) as Hnd.
    pose proof (r_nv _ _ _ _ _ _ _ HRep1) as Fnv.
    pose proof (key_small _ N Hy HN) as Hky.
    rewrite span_lits_cons, Htcq, lit_of_key in Hres by lia. cbn [add_lits] in Hres.
    rewrite Hist, Hmarked, Hlv, Nat.eqb_refl in Hres. cbn [orb] in Hres.
    unfold add_level, add_unmarked, add_lit, add_body, add_loop, f_add_lits, lit_temps.
    cbn [fn_body drop_stmts first_stmt then_stmt loop_body Swhile].
    (* if (pathc >= s->nv) return -1; *)
    run. eapply (exec_if_cmp _ _ _ Cge).
    - ev.
    - ev.
    - reflexivity.
    - reflexivity.
    - unfold Small. lia.
    - unfold Small. lia.
    - cbn [zcmp]. destruct (Nat.leb_spec N pathc) as [Hfull | Hroom].
      + (* the count would reach N: return -1, as the model says *)
        replace (Z.leb (Z.of_nat N) (Z.of_nat pathc)) with true
          by (symmetry; apply Z.leb_le; lia).
        cbv beta iota. eapply exec_return.
        * ev.
        * ret. apply (add_mid_none q mk lt h).
          -- assumption.
          -- assumption.
          -- assumption.
      + (* mark(s, y); pathc++; *)
        replace (Z.leb (Z.of_nat N) (Z.of_nat pathc)) with false
          by (symmetry; apply Z.leb_gt; lia).
        assert (Hincr: Int.add (Int.repr (Z.of_nat pathc)) (Int.repr 1)
                       = Int.repr (Z.of_nat (Datatypes.S pathc))).
        { rewrite add_repr. f_equal. lia. }
        cbv beta iota. apply exec_skip. normal. run. call mark_fun. eapply call_weaken.
        * apply (mark_correct (lt := lt) S N lss (with_heur (set_mrk x mk) h) lims y).
          split.
          -- assumption.
          -- assumption.
        * intros m2 v [HRep2 Hun2]. normal.
          destruct (add_frame_mark m m1 m2 S b n tc Hb Hnd Alits Hkept Hun2)
            as [Alits2 Hkept2].
          run. ints. left. split.
          -- reflexivity.
          -- exists (tset mk (lit_key y) true), lt, (bump h N (extract y)),
               (Datatypes.S pathc).
             constructor.
             ++ tmp.
             ++ tmp.
             ++ tmp.
             ++ tmp.
             ++ tmp.
             ++ tmp.
             ++ tmp.
             ++ lia.
             ++ intros k Hk. apply Hkeys. lia.
             ++ assumption.
             ++ assumption.
             ++ apply HRep2.
             ++ lia.
             ++ assumption.
  Qed.

  (* The literal y at q < e, not t, not marked, of a lower level: it is appended to the
     lower literals.

       {{ AddInv q q mk lt pathc }}
         int n = s->ltlen;
         if (n >= s->nv) return -1;
       {{ result = -1, as the model stops with no count }}
         mark(s, y);                                                        (mark_correct)
         s->lt[n] = y;
         s->ltlen = n + 1;                                                 (rep_store_lt)
       {{ AddInv q (q + 1) (tset mk (lit_key y) true) (lt ++ [y]) h' pathc, for h' the
          heuristic h with the atom of y bumped }}                                    *)
  Lemma add_lower_correct: forall (q: nat) (y: Lit) (mk: Table bool) (lt: list Lit)
    (h: Heur) (pathc: nat) (le: temp_env) (m1: mem) (v1 v2 v3 v4: val),
    AddInv q q mk lt h pathc le m1 -> (q < e)%nat -> tc q = key y ->
    (extract y < N)%nat -> is_lit t y = false -> tget mk (lit_key y) = false ->
    tget (lvl x) (extract y) <> d ->
    Exec ge (lit_temps le y v1 v2 v3 v4) m1 add_lower (AddMid q).
  Proof.
    intros q y mk lt h pathc le m1 v1 v2 v3 v4 HI Hqe Htcq Hy Hist Hmarked Hlv.
    destruct HI as [Hs Hcl Hq He Ht' Hd' Hpc Hrange Hkeys Alits Hkept HRep1 Hpcle Hres].
    pose proof (r_n _ _ _ _ _ _ _ HRep1) as HN.
    pose proof (r_nodup _ _ _ _ _ _ _ HRep1) as Hnd.
    pose proof (r_nv _ _ _ _ _ _ _ HRep1) as Fnv.
    pose proof (r_ltlen _ _ _ _ _ _ _ HRep1) as Fltlen.
    pose proof (r_lt_le _ _ _ _ _ _ _ HRep1) as Hltle.
    pose proof (key_small _ N Hy HN) as Hky.
    rewrite span_lits_cons, Htcq, lit_of_key in Hres by lia. cbn [add_lits] in Hres.
    apply Nat.eqb_neq in Hlv. rewrite Hist, Hmarked, Hlv in Hres. cbn [orb] in Hres.
    unfold add_lower, add_unmarked, add_lit, add_body, add_loop, f_add_lits, lit_temps.
    cbn [fn_body drop_stmts first_stmt then_stmt else_stmt loop_body Swhile].
    (* int n = s->ltlen; if (n >= s->nv) return -1; *)
    run. eapply (exec_if_cmp _ _ _ Cge).
    - ev.
    - ev.
    - reflexivity.
    - reflexivity.
    - unfold Small. lia.
    - unfold Small. lia.
    - cbn [zcmp]. destruct (Nat.leb_spec N (length lt)) as [Hfull | Hroom].
      + (* the lower literals would reach N: return -1, as the model says *)
        replace (Z.leb (Z.of_nat N) (Z.of_nat (length lt))) with true
          by (symmetry; apply Z.leb_le; lia).
        cbv beta iota. eapply exec_return.
        * ev.
        * ret. apply (add_mid_none q mk lt h).
          -- assumption.
          -- assumption.
          -- assumption.
      + (* mark(s, y); *)
        replace (Z.leb (Z.of_nat N) (Z.of_nat (length lt))) with false
          by (symmetry; apply Z.leb_gt; lia).
        assert (Hincr: Int.add (Int.repr (Z.of_nat (length lt))) (Int.repr 1)
                       = Int.repr (Z.of_nat (Datatypes.S (length lt)))).
        { rewrite add_repr. f_equal. lia. }
        cbv beta iota. apply exec_skip. normal. run. call mark_fun. eapply call_weaken.
        * apply (mark_correct (lt := lt) S N lss (with_heur (set_mrk x mk) h) lims y).
          split.
          -- assumption.
          -- assumption.
        * intros m2 v [HRep2 Hun2]. normal.
          destruct (add_frame_mark m m1 m2 S b n tc Hb Hnd Alits Hkept Hun2)
            as [Alits2 Hkept2].
          set (x2 := with_heur (set_mrk x (tset mk (lit_key y) true))
                       (bump h N (extract y))).
          assert (HRep2': RepL m2 S N lss x2 lims lt) by apply HRep2.
          clear HRep2. rename HRep2' into HRep2.
          keep_mem m2.
          pose proof (r_lt _ _ _ _ _ _ _ HRep2) as Flt.
          pose proof (r_ltlen _ _ _ _ _ _ _ HRep2) as Fltlen.
          pose proof (a_lt _ _ _ _ _ _ _ HRep2) as (tlt & Alt & _).
          (* s->lt[n] = y; *)
          run. eapply exec_store.
          ++ evl.
          ++ ev.
          ++ reflexivity.
          ++ reflexivity.
          ++ ofs. bound.
          ++ ofs. cbn [cast_int_int].
             destruct (arr_storable m2 (b_lt S) N (length lt) tlt (key y) Alt Hroom)
               as [m3 Hst3].
             exists m3. split.
             ** apply Hst3.
             ** normal.
                assert (Hlt_in: In (b_lt S) [b_mrk S; b_lt S; b_s S]).
                { right. now left. }
                destruct (add_frame_store m m2 m3 S b (b_lt S) n tc _ _ _ Hb Hnd
                            Hlt_in Alits2 Hkept2 Hst3) as [Alits3 Hkept3].
                assert (Fltlen3: Fld m3 (b_s S) 184 Mint32
                                   (vint (Z.of_nat (length lt)))).
                { apply (fld_store_other _ _ _ _ _ _ _ _ _ _ Fltlen Hst3). left.
                  neq Hnd. }
                (* s->ltlen = n + 1; *)
                eapply exec_store.
                --- evl.
                --- ev.
                --- reflexivity.
                --- reflexivity.
                --- fofs. bound.
                --- fofs. cbn [cast_int_int]. ints.
                    destruct (fld_storable m3 (b_s S) 184 Mint32 _
                                (vint (Z.of_nat (Datatypes.S (length lt)))) Fltlen3)
                      as [m4 Hst4].
                    exists m4. split.
                    +++ apply Hst4.
                    +++ normal.
                        pose proof (rep_store_lt m2 m3 m4 S N lss x2 lims y HRep2
                                      Hroom Hy Hst3 Hst4) as HRep4.
                        assert (Hs_in: In (b_s S) [b_mrk S; b_lt S; b_s S]).
                        { right. right. now left. }
                        destruct (add_frame_store m m3 m4 S b (b_s S) n tc _ _ _ Hb
                                    Hnd Hs_in Alits3 Hkept3 Hst4) as [Alits4 Hkept4].
                        left. split.
                        *** reflexivity.
                        *** exists (tset mk (lit_key y) true), (lt ++ [y]),
                              (bump h N (extract y)), pathc.
                            constructor.
                            ---- tmp.
                            ---- tmp.
                            ---- tmp.
                            ---- tmp.
                            ---- tmp.
                            ---- tmp.
                            ---- tmp.
                            ---- lia.
                            ---- intros k Hk. apply Hkeys. lia.
                            ---- assumption.
                            ---- assumption.
                            ---- apply HRep4.
                            ---- assumption.
                            ---- assumption.
  Qed.

  (* The statement for the literal y at q < e, whose key is in the temporary y:

       {{ AddInv q q mk lt pathc }}
         if (y != t) {
           if (s->mrk[y] == 0) {
             if (s->lvl[y >> 1] == d) { ... }                         (add_level_correct)
             else { ... }                                             (add_lower_correct)
           }
         }
       {{ y is t or marked: AddInv q (q + 1) mk lt pathc }}

     Both branches end in AddMid q. *)
  Lemma add_lit_correct: forall (q: nat) (y: Lit) (mk: Table bool) (lt: list Lit)
    (h: Heur) (pathc: nat) (le: temp_env) (m1: mem),
    AddInv q q mk lt h pathc le m1 -> (q < e)%nat -> tc q = key y ->
    (extract y < N)%nat ->
    Exec ge (PTree.set _y (vint (key y)) le) m1 add_lit (AddMid q).
  Proof.
    intros q y mk lt h pathc le m1 HI Hqe Htcq Hy.
    pose proof HI as HI'.
    destruct HI' as [Hs Hcl Hq He Ht' Hd' Hpc Hrange Hkeys Alits Hkept HRep1 Hpcle Hres].
    pose proof (r_n _ _ _ _ _ _ _ HRep1) as HN.
    pose proof (key_small _ N Hy HN) as Hky.
    assert (Hkey: (lit_key y < 2 * N)%nat) by (now apply lit_key_lt).
    rewrite span_lits_cons, Htcq, lit_of_key in Hres by lia. cbn [add_lits] in Hres.
    unfold add_lit, add_body, add_loop, f_add_lits.
    cbn [fn_body drop_stmts first_stmt loop_body Swhile].
    (* if (y != t) *)
    eapply (exec_if_cmp _ _ _ Cne _ _ (key y) (enc_lit t)).
    - ev.
    - ev.
    - reflexivity.
    - reflexivity.
    - unfold Small. lia.
    - apply (enc_lit_small t N Ht HN).
    - rewrite enc_lit_ne.
      destruct (is_lit t y) eqn:Hist; cbn [negb orb] in Hres |- *.
      + (* y is t: skip it *)
        apply exec_skip. left. split.
        * reflexivity.
        * exists mk, lt, h, pathc. constructor.
          -- tmp.
          -- tmp.
          -- tmp.
          -- tmp.
          -- tmp.
          -- tmp.
          -- tmp.
          -- lia.
          -- intros k Hk. apply Hkeys. lia.
          -- assumption.
          -- assumption.
          -- assumption.
          -- assumption.
          -- assumption.
      + (* if (s->mrk[y] == 0) *)
        pose proof (r_mrk _ _ _ _ _ _ _ HRep1) as Fmrk.
        pose proof (a_mrk _ _ _ _ _ _ _ HRep1) as Amrk.
        cbn [with_heur set_mrk mrk] in Amrk.
        run. eapply (exec_if_cmp _ _ _ Ceq _ _ (enc_mark (tget mk (lit_key y))) 0).
        * ev.
        * ev.
        * reflexivity.
        * reflexivity.
        * unfold Small, enc_mark. destruct (tget mk (lit_key y)); lia.
        * unfold Small. lia.
        * destruct (tget mk (lit_key y)) eqn:Hmarked; cbn [orb] in Hres.
          -- (* y is marked already: skip it *)
             change (zcmp Ceq (enc_mark true) 0) with false. cbv beta iota.
             apply exec_skip. left. split.
             ++ reflexivity.
             ++ exists mk, lt, h, pathc. constructor.
                ** tmp.
                ** tmp.
                ** tmp.
                ** tmp.
                ** tmp.
                ** tmp.
                ** tmp.
                ** lia.
                ** intros k Hk. apply Hkeys. lia.
                ** assumption.
                ** assumption.
                ** assumption.
                ** assumption.
                ** assumption.
          -- (* if (s->lvl[y >> 1] == d) *)
             change (zcmp Ceq (enc_mark false) 0) with true. cbv beta iota.
             pose proof (r_lvl _ _ _ _ _ _ _ HRep1) as Flvl.
             pose proof (a_lvl _ _ _ _ _ _ _ HRep1) as Alvl.
             cbn [with_heur set_mrk lvl] in Alvl.
             pose proof (r_lvl_le _ _ _ _ _ _ _ HRep1 (extract y) Hy) as Hlvl.
             cbn [with_heur set_mrk lvl] in Hlvl.
             assert (Hshr: Int.shr (Int.repr (key y)) (Int.repr 1)
                           = Int.repr (Z.of_nat (extract y))).
             { apply shr_key. lia. }
             run.
             eapply (exec_if_cmp _ _ _ Ceq _ _ (Z.of_nat (tget (lvl x) (extract y)))
                       (Z.of_nat d)).
             ++ ev.
             ++ ev.
             ++ reflexivity.
             ++ reflexivity.
             ++ unfold Small. lia.
             ++ unfold Small. lia.
             ++ cbn [zcmp].
                destruct (Nat.eq_dec (tget (lvl x) (extract y)) d) as [Hlv | Hlv].
                ** (* level d *)
                   replace (Z.eqb (Z.of_nat (tget (lvl x) (extract y))) (Z.of_nat d))
                     with true by (symmetry; apply Z.eqb_eq; lia).
                   apply (add_level_correct q y mk lt h pathc).
                   --- assumption.
                   --- assumption.
                   --- assumption.
                   --- assumption.
                   --- assumption.
                   --- assumption.
                   --- assumption.
                ** (* a lower level *)
                   replace (Z.eqb (Z.of_nat (tget (lvl x) (extract y))) (Z.of_nat d))
                     with false by (symmetry; apply Z.eqb_neq; lia).
                   apply (add_lower_correct q y mk lt h pathc).
                   --- assumption.
                   --- assumption.
                   --- assumption.
                   --- assumption.
                   --- assumption.
                   --- assumption.
                   --- assumption.
  Qed.

  (* One pass of the loop, at q < e:

       {{ AddInv q q mk lt pathc /\ q < e }}
         int y = cl[q];
         the statement for y;                                           (add_lit_correct)
       {{ result = -1, as the model stops with no count }}
       {{ AddInv q (q + 1) mk' lt' pathc' }}
         q++;
       {{ AddInv (q + 1) (q + 1) mk' lt' pathc' }}                                    *)
  Lemma add_body_correct: forall (q: nat) (le: temp_env) (m1: mem),
    add_inv q le m1 -> (q < e)%nat ->
    Exec ge le m1 add_body (LoopK add_variant add_inv AddPost q).
  Proof.
    intros q le m1 (mk & lt & h & pathc & HI) Hqe.
    pose proof HI as HI'.
    destruct HI' as [Hs Hcl Hq He Ht' Hd' Hpc Hrange Hkeys Alits _ HRep1 _ _].
    pose proof (r_n _ _ _ _ _ _ _ HRep1) as HN.
    destruct (Hkeys q) as (y & Htcq & Hy).
    { lia. }
    assert (Hincr: Int.add (Int.repr (Z.of_nat q)) (Int.repr 1)
                   = Int.repr (Z.of_nat (Datatypes.S q))).
    { rewrite add_repr. f_equal. lia. }
    unfold add_body, add_loop, f_add_lits.
    cbn [fn_body drop_stmts first_stmt loop_body Swhile].
    (* int y = cl[q]; *)
    run. rewrite Htcq.
    apply exec_weaken with (Q := AddMid q).
    - apply (add_lit_correct q y mk lt h pathc le m1).
      + assumption.
      + assumption.
      + assumption.
      + assumption.
    - intros le2 m2 out [(-> & mk2 & lt2 & h2 & pathc2 & HI2) | (-> & Hpost)].
      + (* q++; and the loop goes on *)
        destruct HI2 as [Hs2 Hcl2 Hq2 He2 Ht2 Hd2 Hpc2 Hrange2 Hkeys2 Alits2 Hkept2 HRep2
                         Hpcle2 Hres2].
        normal. run. ints. apply loopk_next with (Datatypes.S q).
        * unfold add_variant, ltof. lia.
        * exists mk2, lt2, h2, pathc2. constructor.
          -- tmp.
          -- tmp.
          -- tmp.
          -- tmp.
          -- tmp.
          -- tmp.
          -- tmp.
          -- assumption.
          -- assumption.
          -- assumption.
          -- assumption.
          -- assumption.
          -- assumption.
          -- assumption.
      + (* return -1 *)
        abrupt. apply loopk_return. assumption.
  Qed.

  (* The loop of add_lits:

       {{ add_inv q }}
         while (q < e) { ... }                                         (add_body_correct)
       {{ add_inv e: res = (mk, lt, Some pathc) }}

     The loop ends: e - q decreases. *)
  Lemma add_loop_correct: forall (q: nat) (le: temp_env) (m1: mem),
    add_inv q le m1 -> Exec ge le m1 add_loop AddPost.
  Proof.
    intros q0 le0 m0 HI0.
    unfold add_loop, f_add_lits. cbn [fn_body first_stmt]. unfold Swhile.
    apply exec_loop with (R := add_variant) (I := add_inv) (a := q0).
    - apply well_founded_ltof.
    - intros q le m1 HI. pose proof HI as (mk & lt & h & pathc & HI').
      destruct HI'
        as [Hs Hcl Hq He Ht' Hd' Hpc Hrange Hkeys Alits Hkept HRep1 Hpcle Hres].
      apply exec_seq.
      (* if (q < e) ... else break; *)
      eapply (exec_if_cmp _ _ _ Clt).
      + ev.
      + ev.
      + reflexivity.
      + reflexivity.
      + unfold Small. lia.
      + unfold Small. lia.
      + destruct (Nat.lt_ge_cases q e) as [Hlt | Hge].
        * (* q < e: the body *)
          replace (zcmp Clt (Z.of_nat q) (Z.of_nat e)) with true
            by (symmetry; cbn [zcmp]; apply Z.ltb_lt; lia).
          cbv beta iota. apply exec_skip. normal.
          apply add_body_correct.
          -- assumption.
          -- assumption.
        * (* q = e: break; no literals are left, and the model gives the count *)
          replace (zcmp Clt (Z.of_nat q) (Z.of_nat e)) with false
            by (symmetry; cbn [zcmp]; apply Z.ltb_ge; lia).
          cbv beta iota. apply exec_break. abrupt. apply loopk_break.
          replace q with e in Hres by lia. rewrite span_lits_nil in Hres.
          cbn [add_lits] in Hres. unfold AddPost. rewrite <- Hres. split.
          -- assumption.
          -- split.
             ++ assumption.
             ++ left. split.
                ** reflexivity.
                ** exists pathc. split.
                   --- reflexivity.
                   --- assumption.
    - assumption.
  Qed.
End Loop.

(* add_lits adds the literals cl[q .. e) to the analysis at level d, skipping t: writing
   ys for these literals and (mk', lt', h', r) for the model,
   add_lits (lvl x) d (nvars x) t ys (mrk x) lt (hr x) pathc:

     {{ RepL m S N lss x lims lt /\ cl is clits or rlits, with n keys tc /\
        q <= e <= n /\ the keys from q to e are literals with atoms below N /\ ... }}
     {{ add_inv q }}
       while (q < e) { ... }                                           (add_loop_correct)
     {{ RepL (with_heur (set_mrk x mk') h') lt' /\ only the marks, lt, the struct and the
        heuristic changed /\
        (the count r in pathc \/ result = -1 /\ r = None) }}
       return pathc;
     {{ result = enc_count r }}

   The block cl has fewer than 2^30 entries (as clits and rlits have), so that q and e
   are small: C compares them and increments q. *)
Lemma add_lits_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (b: block) (n: nat) (tc: nat -> Z) (q e: nat) (t: option Lit)
  (d pathc: nat),
  {{ m | RepL m S N lss x lims lt /\ (b = b_clits S \/ b = b_rlits S) /\ Arr m b n tc /\
         (q <= e <= n)%nat /\
         (forall (k: nat), (q <= k < e)%nat ->
            exists (y: Lit), tc k = key y /\ (extract y < N)%nat) /\
         (forall (y: Lit), t = Some y -> (extract y < N)%nat) /\ (d <= N)%nat /\
         (pathc <= N)%nat /\ Z.of_nat n < 1073741824 }}
    f_add_lits(sptr S, Vptr b Ptrofs.zero, vint (Z.of_nat q), vint (Z.of_nat e),
               vint (enc_lit t), vint (Z.of_nat d), vint (Z.of_nat pathc))
  {{ m', v | match add_lits (lvl x) d (nvars x) t
                   (map (fun (k: nat) => lit_of (tc k)) (seq q (e - q))) (mrk x) lt
                   (hr x) pathc with
             | (mk', lt', h', r) =>
               v = vint (enc_count r) /\
               RepL m' S N lss (with_heur (set_mrk x mk') h') lims lt' /\
               Mem.unchanged_on (AddKept S) m m'
             end }}.
Proof.
  intros S N lss x lims b n tc q e t d pathc m
    (HRep & Hb & Alits & Hrange & Hkeys & Ht & Hd & Hpathc & Hn).
  change (ClauseBlock S b) in Hb.
  pose proof (r_nvars _ _ _ _ _ _ _ HRep) as Hnvars.
  change (map (fun (k: nat) => lit_of (tc k)) (seq q (e - q))) with (span_lits tc q e).
  rewrite Hnvars.
  remember (add_lits (lvl x) d N t (span_lits tc q e) (mrk x) lt (hr x) pathc)
    as res eqn:Hres.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_add_lits. cbn [fn_body fn_return]. apply exec_seq.
    apply exec_weaken with (Q := AddPost m S N lss x lims res).
    + apply (add_loop_correct m S N lss x lims b n tc e t d res Hb Ht Hd Hn q).
      exists (mrk x), lt, (hr x), pathc. constructor.
      * tmp.
      * tmp.
      * tmp.
      * tmp.
      * tmp.
      * tmp.
      * tmp.
      * assumption.
      * assumption.
      * assumption.
      * apply Mem.unchanged_on_refl.
      * destruct x. apply HRep.
      * assumption.
      * symmetry. assumption.
    + intros le' m' out. unfold AddPost. destruct res as [[[mk' lt'] h'] r].
      intros (HRep' & Hkept & [(-> & pathc' & -> & Hpc') | (-> & ->)]).
      * (* the loop ended with the count: return pathc; *)
        normal. eapply exec_return.
        -- ev.
        -- exists (vint (Z.of_nat pathc')). split.
           ++ apply result_int.
           ++ split.
              ** reflexivity.
              ** split.
                 --- assumption.
                 --- apply Hkept.
      * (* the loop gave up: return -1 *)
        abrupt. exists (vint (-1)). split.
        -- apply result_int.
        -- split.
           ++ reflexivity.
           ++ split.
              ** assumption.
              ** apply Hkept.
Qed.

Lemma add_lits_fun: exists (b: block),
  Genv.find_symbol ge _add_lits = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_add_lits).
Proof. apply find_fun. reflexivity. Qed.
