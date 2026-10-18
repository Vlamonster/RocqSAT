(* add_lits adds the literals of a part of a clause to the analysis of a conflict: it
   marks them, counts those of the conflict level and appends the others to the lower
   literals, or gives up when a count would reach the number of atoms (add_lits). *)
From Stdlib Require Import List.
Import ListNotations.

From compcert Require Import Coqlib.
From compcert Require Import Maps.
From compcert Require Import Integers.
From compcert Require Import AST.
From compcert Require Import Values.
From compcert Require Import Memory.
From compcert Require Import Globalenvs.
From compcert Require Import Ctypes.
From compcert Require Import Cop.
From compcert Require Import Clight.
From compcert Require Import ClightBigstep.

From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Tactics.
From RocqSAT.refinement Require Import Table.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import Heur.
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement Require Import Analysis.
From RocqSAT.refinement Require Import Step.
From RocqSAT.refinement.c Require Import Arrays.
From RocqSAT.refinement.c Require Import Logic.
From RocqSAT.refinement.c Require Import Common.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Rep.
From RocqSAT.refinement.c Require Import RepReasons.
From RocqSAT.refinement.c Require Import RepHeur.
From RocqSAT.refinement.c Require Import Mark.

(* The literals with the keys tc q .. tc (e - 1). *)
Definition span_lits (tc: nat -> Z) (q e: nat): list Lit :=
  map (fun (k: nat) => lit_of (tc k)) (seq q (e - q)).

(* The keys tc q .. tc (e - 1) are literals with atoms below N. *)
Abbreviation LitKeys N tc q e :=
  (forall (k: nat), (q <= k < e)%nat ->
     exists (y: Lit), tc k = key y /\ (extract y < N)%nat).

(* The literal t, if any, has its atom below N. *)
Abbreviation OptBelow N t := (forall (y: Lit), t = Some y -> (extract y < N)%nat).

(* A nonempty range starts with the literal at q. *)
Lemma span_lits_cons: forall (tc: nat -> Z) (q e: nat), (q < e)%nat ->
  span_lits tc q e = lit_of (tc q) :: span_lits tc (S q) e.
Proof.
  intros tc q e Hqe. unfold span_lits.
  replace (e - q)%nat with (S (e - S q)) by lia. reflexivity.
Qed.

(* An empty range has no literals. *)
Lemma span_lits_nil: forall (tc: nat -> Z) (e: nat), span_lits tc e e = [].
Proof. intros tc e. unfold span_lits. now rewrite Nat.sub_diag. Qed.

(* The literals add_lits reads are in block clits or rlits. *)
Definition ClauseBlock (sh: Shape) (b: block): Prop := b = b_clits sh \/ b = b_rlits sh.

(* That block is not one that add_lits writes: the marks, the lower literals and the
   struct. *)
Lemma clause_block_other: forall (sh: Shape) (b b': block),
  ClauseBlock sh b -> NoDup (iblocks sh) -> In b' [b_mrk sh; b_lt sh; b_s sh] -> b <> b'.
Proof.
  intros sh b b' Hb Hnd Hb'. unfold iblocks in Hnd.
  destruct Hb as [-> | ->], Hb' as [<- | [<- | [<- | []]]]; neq Hnd.
Qed.

(* Every block but those add_lits writes: the marks, the lower literals, the struct and
   the heuristic. *)
Definition AddFrame (sh: Shape) (b: block) (ofs: Z): Prop :=
  b <> b_lt sh /\ MarkFrame sh b ofs.

(* A store of add_lits, to one of these blocks, keeps the literals it reads and the rest
   of the memory. *)
Lemma add_frame_store: forall (m m1 m2: mem) (sh: Shape) (b b': block) (n: nat)
  (tc: nat -> Z) (ofs: Z) (c: memory_chunk) (v: val),
  ClauseBlock sh b -> NoDup (iblocks sh) -> In b' [b_mrk sh; b_lt sh; b_s sh] ->
  Arr m1 b n tc -> Mem.unchanged_on (AddFrame sh) m m1 ->
  Mem.store c m1 b' ofs v = Some m2 ->
  Arr m2 b n tc /\ Mem.unchanged_on (AddFrame sh) m m2.
Proof.
  intros m m1 m2 sh b b' n tc ofs c v Hb Hnd Hb' A Hun Hst. split.
  - apply (arr_store_other A Hst).
    apply (clause_block_other sh); assumption.
  - apply (store_unchanged _ _ _ _ _ _ _ _ Hun Hst).
    intros i (Hlt & Hmrk & _ & _ & _ & _ & Hs). destruct Hb' as [<- | [<- | [<- | []]]].
    + now apply Hmrk.
    + now apply Hlt.
    + now apply Hs.
Qed.

(* A call of mark keeps the literals add_lits reads, and the rest of the memory. *)
Lemma add_frame_mark: forall (m m1 m2: mem) (sh: Shape) (b: block) (n: nat)
  (tc: nat -> Z),
  ClauseBlock sh b -> NoDup (iblocks sh) ->
  Arr m1 b n tc -> Mem.unchanged_on (AddFrame sh) m m1 ->
  Mem.unchanged_on (MarkFrame sh) m1 m2 ->
  Arr m2 b n tc /\ Mem.unchanged_on (AddFrame sh) m m2.
Proof.
  intros m m1 m2 sh b n tc Hb Hnd A Hun Hmark. unfold iblocks in Hnd. split.
  - apply (arr_unchanged _ m1 m2 b n tc Hmark).
    + intros ofs. destruct Hb as [-> | ->]; repeat split; neq Hnd.
    + assumption.
  - frame.
Qed.

(* The literal t to skip, as C passes it, is small. *)
Lemma enc_lit_small: forall (t: option Lit) (N: nat),
  OptBelow N t -> Z.of_nat N < atom_bound ->
  Small (enc_lit t).
Proof.
  intros [y|] N Ht HN; cbn [enc_lit].
  - pose proof (key_small y N (Ht y eq_refl) HN). lia.
  - lia.
Qed.

(* C compares keys to see whether y is t: y == t. *)
Lemma enc_lit_eq: forall (t: option Lit) (y: Lit),
  key y = enc_lit t <-> is_lit t y = true.
Proof.
  intros [t'|] y; cbn [enc_lit is_lit].
  - rewrite <- key_eqb. symmetry. apply Z.eqb_eq.
  - split.
    + intros Hkey. unfold key in Hkey. lia.
    + discriminate.
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
     tc q .. tc (e - 1) of block b, which has n entries, skipping t, at level d, whose
     model gives res. *)
  Variables (m: mem) (sh: Shape) (N: nat) (lss: list (list Lit))
    (b: block) (n: nat) (tc: nat -> Z) (e: nat) (t: option Lit)
    (d: nat) (res: Ctx * option nat).

  (* The state of the loop of add_lits at the literal at q, with the temporary q holding
     qt: the model from the context x1 and q on gives res. *)
  Record AddInv (qt q: nat) (x1: Ctx) (pathc: nat) (le: temp_env) (m1: mem): Prop := {
    ai_s: le ! _s = Some (sptr sh);
    ai_cl: le ! _cl = Some (Vptr b Ptrofs.zero);
    ai_q: le ! _q = Some (vnat qt);
    ai_e: le ! _e = Some (vnat e);
    ai_t: le ! _t = Some (vint (enc_lit t));
    ai_d: le ! _d = Some (vnat d);
    ai_pathc: le ! _pathc = Some (vnat pathc);
    ai_range: (q <= e <= n)%nat;
    ai_keys: LitKeys N tc q e;
    ai_lits: Arr m1 b n tc;
    ai_kept: Mem.unchanged_on (AddFrame sh) m m1;
    ai_rep: RepL m1 sh N lss x1;
    ai_pathc_le: (pathc <= N)%nat;
    ai_res: add_lits x1 d t (span_lits tc q e) pathc = res;
  }.

  (* The variant and the invariant of the loop. *)
  Definition add_variant: nat -> nat -> Prop := ltof nat (fun (q: nat) => e - q)%nat.
  Definition add_inv (q: nat) (le: temp_env) (m1: mem): Prop :=
    exists (x1: Ctx) (pathc: nat), AddInv q q x1 pathc le m1.

  (* What the loop of add_lits ends in, for res = (x', r): the memory represents x', and
     it ends normally with the count r in pathc, or returns -1 for r = None. *)
  Definition AddPost (le: temp_env) (m1: mem) (out: outcome): Prop :=
    match res with
    | (x', r) =>
      RepL m1 sh N lss x' /\
      Mem.unchanged_on (AddFrame sh) m m1 /\
      ((out = Out_normal /\
        exists (pathc: nat),
          r = Some pathc /\ le ! _pathc = Some (vnat pathc))
       \/ (out = ret_int (-1) /\ r = None))
    end.

  (* What the statement for the literal at q ends in: normally with the state at q + 1
     (q not yet incremented), or returning -1 as the loop does. *)
  Definition AddLitPost (q: nat) (le: temp_env) (m1: mem) (out: outcome): Prop :=
    (out = Out_normal /\
     exists (x1: Ctx) (pathc: nat), AddInv q (S q) x1 pathc le m1) \/
    (out = ret_int (-1) /\ AddPost le m1 out).

  (* Giving up: when the model stops with no count, returning -1 is what it says. *)
  Lemma add_lit_post_none: forall (q: nat) (x1: Ctx) (le: temp_env) (m1: mem),
    RepL m1 sh N lss x1 -> Mem.unchanged_on (AddFrame sh) m m1 -> (x1, None) = res ->
    AddLitPost q le m1 (ret_int (-1)).
  Proof.
    intros q x1 le m1 HRep Hkept Hres. right. split.
    - reflexivity.
    - unfold AddPost. rewrite <- Hres. splits.
      + assumption.
      + assumption.
      + right. split; reflexivity.
  Qed.

  (* The temporaries for the literal y after its loads: y, then the marks pointer and the
     mark of y (v1, v2), then the levels pointer and the level of its atom (v3, v4). *)
  Definition lit_temps (le: temp_env) (y: Lit) (v1 v2 v3 v4: val): temp_env :=
    PTree.set _t'4 v4 (PTree.set _t'3 v3 (PTree.set _t'2 v2 (PTree.set _t'1 v1
      (PTree.set _y (vint (key y)) le)))).

  Hypothesis (Hb: ClauseBlock sh b).
  Hypothesis (Ht: OptBelow N t).
  Hypothesis (Hd: (d <= N)%nat).
  Hypothesis (Hn: Z.of_nat n < small_bound).

  (* The literal y at q < e, not t, not marked, of level d: it is counted.

       {{ AddInv q q x1 pathc }}
         if (pathc >= s->nv) return -1;
       {{ result = -1, as the model stops with no count }}
         mark(s, y);                                                        (mark_correct)
         pathc++;
       {{ AddInv q (q + 1) (mark x1 y) (pathc + 1) }}                                  *)
  Lemma add_level_correct: forall (q: nat) (y: Lit) (x1: Ctx) (pathc: nat)
    (le: temp_env) (m1: mem) (v1 v2 v3 v4: val),
    AddInv q q x1 pathc le m1 -> (q < e)%nat -> tc q = key y ->
    (extract y < N)%nat -> is_lit t y = false -> tget (mrk x1) (lit_key y) = false ->
    level x1 y = d ->
    Exec ge (lit_temps le y v1 v2 v3 v4) m1 add_level (AddLitPost q).
  Proof.
    intros q y x1 pathc le m1 v1 v2 v3 v4 HI Hqe Htcq Hy Hist Hmarked Hlv.
    destruct HI as [Hs Hcl Hq He Ht' Hd' Hpc Hrange Hkeys Alits Hkept HRep1 Hpcle Hres].
    pose proof (r_n HRep1) as HN.
    pose proof (r_nodup HRep1) as Hnd.
    pose proof (r_nv HRep1) as Fnv.
    pose proof (key_small _ N Hy HN) as Hky.
    rewrite span_lits_cons, Htcq, lit_of_key in Hres by lia. cbn [add_lits] in Hres.
    rewrite Hist, Hmarked, Hlv, Nat.eqb_refl, (r_nvars HRep1) in Hres.
    cbn [orb] in Hres.
    unfold add_level, add_unmarked, add_lit, add_body, add_loop, f_add_lits, lit_temps.
    cbn [fn_body drop_stmts first_stmt then_stmt loop_body Swhile].
    (* if (pathc >= s->nv) return -1; *)
    run. branch.
    - (* the count would reach N: return -1, as the model says *)
      intros Hfull.
      replace (N <=? pathc)%nat with true in Hres by (symmetry; apply Nat.leb_le; lia).
      eapply exec_return.
      + ev.
      + ret. apply (add_lit_post_none q x1); assumption.
    - (* mark(s, y); pathc++; *)
      intros Hroom.
      replace (N <=? pathc)%nat with false in Hres by (symmetry; apply Nat.leb_gt; lia).
      assert (Hincr: Int.add (Int.repr (Z.of_nat pathc)) (Int.repr 1)
                     = Int.repr (Z.of_nat (S pathc))).
      { rewrite add_repr. f_equal. lia. }
      apply exec_skip. normal. run.
      call mark_fun (mark_correct sh N lss x1 y) by (split; assumption).
      intros m2 v [HRep2 Hun2]. normal.
      destruct (add_frame_mark m m1 m2 sh b n tc Hb Hnd Alits Hkept Hun2)
        as [Alits2 Hkept2].
      run. ints. left. split.
      + reflexivity.
      + exists (mark x1 y), (S pathc).
        constructor.
        * tmp.
        * tmp.
        * tmp.
        * tmp.
        * tmp.
        * tmp.
        * tmp.
        * lia.
        * intros k Hk. apply Hkeys. lia.
        * assumption.
        * assumption.
        * apply HRep2.
        * lia.
        * assumption.
  Qed.

  (* The literal y at q < e, not t, not marked, of a lower level: it is appended to the
     lower literals.

       {{ AddInv q q x1 pathc }}
         int n = s->ltlen;
         if (n >= s->nv) return -1;
       {{ result = -1, as the model stops with no count }}
         mark(s, y);                                                        (mark_correct)
       {{ RepL (mark x1 y) }}
         s->lt[n] = y;
         s->ltlen = n + 1;                                                 (rep_store_lt)
       {{ AddInv q (q + 1) ((mark x1 y) <| lower := lower x1 ++ [y] |>) pathc }}    *)
  Lemma add_lower_correct: forall (q: nat) (y: Lit) (x1: Ctx) (pathc: nat)
    (le: temp_env) (m1: mem) (v1 v2 v3 v4: val),
    AddInv q q x1 pathc le m1 -> (q < e)%nat -> tc q = key y ->
    (extract y < N)%nat -> is_lit t y = false -> tget (mrk x1) (lit_key y) = false ->
    level x1 y <> d ->
    Exec ge (lit_temps le y v1 v2 v3 v4) m1 add_lower (AddLitPost q).
  Proof.
    intros q y x1 pathc le m1 v1 v2 v3 v4 HI Hqe Htcq Hy Hist Hmarked Hlv.
    destruct HI as [Hs Hcl Hq He Ht' Hd' Hpc Hrange Hkeys Alits Hkept HRep1 Hpcle Hres].
    pose proof (r_n HRep1) as HN.
    pose proof (r_nodup HRep1) as Hnd.
    pose proof (r_nv HRep1) as Fnv.
    pose proof (r_ltlen HRep1) as Fltlen.
    pose proof (r_lt_le HRep1) as Hltle.
    pose proof (key_small _ N Hy HN) as Hky.
    rewrite span_lits_cons, Htcq, lit_of_key in Hres by lia. cbn [add_lits] in Hres.
    apply Nat.eqb_neq in Hlv. rewrite Hist, Hmarked, Hlv, (r_nvars HRep1) in Hres.
    cbn [orb] in Hres.
    unfold add_lower, add_unmarked, add_lit, add_body, add_loop, f_add_lits, lit_temps.
    cbn [fn_body drop_stmts first_stmt then_stmt else_stmt loop_body Swhile].
    (* int n = s->ltlen; if (n >= s->nv) return -1; *)
    run. branch.
    - (* the lower literals would reach N: return -1, as the model says *)
      intros Hfull.
      replace (N <=? length (lower x1))%nat with true in Hres
        by (symmetry; apply Nat.leb_le; lia).
      eapply exec_return.
      + ev.
      + ret. apply (add_lit_post_none q x1); assumption.
    - (* mark(s, y); *)
      intros Hroom_z. assert (Hroom: (length (lower x1) < N)%nat) by lia.
      replace (N <=? length (lower x1))%nat with false in Hres
        by (symmetry; apply Nat.leb_gt; lia).
      assert (Hincr: Int.add (Int.repr (Z.of_nat (length (lower x1)))) (Int.repr 1)
                     = Int.repr (Z.of_nat (S (length (lower x1))))).
      { rewrite add_repr. f_equal. lia. }
      apply exec_skip. normal. run.
      call mark_fun (mark_correct sh N lss x1 y) by (split; assumption).
      intros m2 v [HRep2 Hun2]. normal.
      destruct (add_frame_mark m m1 m2 sh b n tc Hb Hnd Alits Hkept Hun2)
        as [Alits2 Hkept2].
      keep_mem m2.
      pose proof (r_lt HRep2) as Flt.
      pose proof (r_ltlen HRep2) as Fltlen.
      pose proof (a_lt HRep2) as (tlt & Alt & _).
      (* s->lt[n] = y; *)
      run. store Alt Hroom as m3 Hst3.
      assert (Hlt_in: In (b_lt sh) [b_mrk sh; b_lt sh; b_s sh]).
      { right. now left. }
      destruct (add_frame_store m m2 m3 sh b (b_lt sh) n tc _ _ _ Hb Hnd
                  Hlt_in Alits2 Hkept2 Hst3) as [Alits3 Hkept3].
      assert (Fltlen3: IntAt m3 sh o_ltlen (length (lower x1))).
      { apply (fld_store_other Fltlen Hst3). left. neq Hnd. }
      (* s->ltlen = n + 1; *)
      store Fltlen3 as m4 Hst4.
      cbn [cast_int_int] in Hst4. rewrite Hincr in Hst4.
      pose proof (rep_store_lt m2 m3 m4 y HRep2
                    Hroom Hy Hst3 Hst4) as HRep4.
      assert (Hs_in: In (b_s sh) [b_mrk sh; b_lt sh; b_s sh]).
      { right. right. now left. }
      destruct (add_frame_store m m3 m4 sh b (b_s sh) n tc _ _ _ Hb
                  Hnd Hs_in Alits3 Hkept3 Hst4) as [Alits4 Hkept4].
      left. split.
      + reflexivity.
      + exists ((mark x1 y) <| lower := lower x1 ++ [y] |>), pathc.
        constructor.
        * tmp.
        * tmp.
        * tmp.
        * tmp.
        * tmp.
        * tmp.
        * tmp.
        * lia.
        * intros k Hk. apply Hkeys. lia.
        * assumption.
        * assumption.
        * apply HRep4.
        * assumption.
        * assumption.
  Qed.

  (* The statement for the literal y at q < e, whose key is in the temporary y:

       {{ AddInv q q x1 pathc }}
         if (y != t) {
           if (s->mrk[y] == 0) {
             if (s->lvl[y >> 1] == d) { ... }                         (add_level_correct)
             else { ... }                                             (add_lower_correct)
           }
         }
       {{ y is t or marked: AddInv q (q + 1) x1 pathc }}

     Both branches end in AddLitPost q. *)
  Lemma add_lit_correct: forall (q: nat) (y: Lit) (x1: Ctx) (pathc: nat)
    (le: temp_env) (m1: mem),
    AddInv q q x1 pathc le m1 -> (q < e)%nat -> tc q = key y ->
    (extract y < N)%nat ->
    Exec ge (PTree.set _y (vint (key y)) le) m1 add_lit (AddLitPost q).
  Proof.
    intros q y x1 pathc le m1 HI Hqe Htcq Hy.
    pose proof HI as HI'.
    destruct HI' as [Hs Hcl Hq He Ht' Hd' Hpc Hrange Hkeys Alits Hkept HRep1 Hpcle Hres].
    pose proof (r_n HRep1) as HN.
    pose proof (key_small _ N Hy HN) as Hky.
    assert (Hkey: (lit_key y < 2 * N)%nat) by (now apply lit_key_lt).
    rewrite span_lits_cons, Htcq, lit_of_key in Hres by lia. cbn [add_lits] in Hres.
    unfold add_lit, add_body, add_loop, f_add_lits.
    cbn [fn_body drop_stmts first_stmt loop_body Swhile].
    (* if (y != t) *)
    eapply (exec_if_ne (key y) (enc_lit t)).
    - ev.
    - ev.
    - reflexivity.
    - split.
      + lia.
      + apply (enc_lit_small t N Ht HN).
    - (* if (s->mrk[y] == 0) *)
      intros Hne.
      assert (Hist: is_lit t y = false).
      { apply not_true_iff_false. rewrite <- enc_lit_eq. assumption. }
      pose proof (r_mrk HRep1) as Fmrk.
      pose proof (a_mrk HRep1) as Amrk.
      run. eapply (exec_if_eq (enc_mark (tget (mrk x1) (lit_key y))) 0).
      + ev.
      + ev.
      + reflexivity.
      + unfold enc_mark. destruct (tget (mrk x1) (lit_key y)); lia.
      + (* if (s->lvl[y >> 1] == d) *)
        intros Hzero.
        assert (Hmarked: tget (mrk x1) (lit_key y) = false).
        { unfold enc_mark in Hzero. destruct (tget (mrk x1) (lit_key y)).
          - lia.
          - reflexivity. }
        pose proof (r_lvl HRep1) as Flvl.
        pose proof (a_lvl HRep1) as Alvl.
        pose proof (r_lvl_le HRep1 (extract y) Hy) as Hlvl.
        assert (Hshr: Int.shr (Int.repr (key y)) (Int.repr 1)
                      = Int.repr (Z.of_nat (extract y))).
        { apply shr_key. lia. }
        run.
        branch (Z.of_nat (level x1 y)) (Z.of_nat d).
        * (* level d *)
          intros Hlv. apply (add_level_correct q y x1 pathc).
          -- assumption.
          -- assumption.
          -- assumption.
          -- assumption.
          -- assumption.
          -- assumption.
          -- lia.
        * (* a lower level *)
          intros Hlv. apply (add_lower_correct q y x1 pathc).
          -- assumption.
          -- assumption.
          -- assumption.
          -- assumption.
          -- assumption.
          -- assumption.
          -- lia.
      + (* y is marked already: skip it *)
        intros Hnonzero.
        assert (Hmarked: tget (mrk x1) (lit_key y) = true).
        { unfold enc_mark in Hnonzero. destruct (tget (mrk x1) (lit_key y)).
          - reflexivity.
          - lia. }
        rewrite Hist, Hmarked in Hres. cbn [orb] in Hres.
        apply exec_skip. left. split.
        * reflexivity.
        * exists x1, pathc. constructor.
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
    - (* y is t: skip it *)
      intros Heq. apply enc_lit_eq in Heq as Hist.
      rewrite Hist in Hres. cbn [orb] in Hres.
      apply exec_skip. left. split.
      + reflexivity.
      + exists x1, pathc. constructor.
        * tmp.
        * tmp.
        * tmp.
        * tmp.
        * tmp.
        * tmp.
        * tmp.
        * lia.
        * intros k Hk. apply Hkeys. lia.
        * assumption.
        * assumption.
        * assumption.
        * assumption.
        * assumption.
  Qed.

  (* One pass of the loop, at q < e:

       {{ AddInv q q x1 pathc /\ q < e }}
         int y = cl[q];
         the statement for y;                                           (add_lit_correct)
       {{ result = -1, as the model stops with no count }}
       {{ AddInv q (q + 1) x2 pathc2 }}
         q++;
       {{ AddInv (q + 1) (q + 1) x2 pathc2 }}                                    *)
  Lemma add_body_correct: forall (q: nat) (le: temp_env) (m1: mem),
    add_inv q le m1 -> (q < e)%nat ->
    Exec ge le m1 add_body (LoopK add_variant add_inv AddPost q).
  Proof.
    intros q le m1 (x1 & pathc & HI) Hqe.
    pose proof HI as HI'.
    destruct HI' as [Hs Hcl Hq He Ht' Hd' Hpc Hrange Hkeys Alits _ HRep1 _ _].
    pose proof (r_n HRep1) as HN.
    destruct (Hkeys q) as (y & Htcq & Hy).
    { lia. }
    assert (Hincr: Int.add (Int.repr (Z.of_nat q)) (Int.repr 1)
                   = Int.repr (Z.of_nat (S q))).
    { rewrite add_repr. f_equal. lia. }
    unfold add_body, add_loop, f_add_lits.
    cbn [fn_body drop_stmts first_stmt loop_body Swhile].
    (* int y = cl[q]; *)
    run. rewrite Htcq.
    apply exec_weaken with (Q := AddLitPost q).
    - apply (add_lit_correct q y x1 pathc le m1); assumption.
    - intros le2 m2 out [(-> & x2 & pathc2 & HI2) | (-> & Hpost)].
      + (* q++; and the loop goes on *)
        destruct HI2 as [Hs2 Hcl2 Hq2 He2 Ht2 Hd2 Hpc2 Hrange2 Hkeys2 Alits2 Hkept2 HRep2
                         Hpcle2 Hres2].
        normal. run. ints. apply loopk_next with (S q).
        * unfold add_variant, ltof. lia.
        * exists x2, pathc2. constructor.
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
       {{ add_inv e: res = (x1, Some pathc) }}

     The loop ends: e - q decreases. *)
  Lemma add_loop_correct: forall (q: nat) (le: temp_env) (m1: mem),
    add_inv q le m1 -> Exec ge le m1 add_loop AddPost.
  Proof.
    intros q0 le0 m0 HI0.
    unfold add_loop, f_add_lits. cbn [fn_body first_stmt]. unfold Swhile.
    apply exec_loop with (R := add_variant) (I := add_inv) (a := q0).
    - apply well_founded_ltof.
    - intros q le m1 HI. pose proof HI as (x1 & pathc & HI').
      destruct HI'
        as [Hs Hcl Hq He Ht' Hd' Hpc Hrange Hkeys Alits Hkept HRep1 Hpcle Hres].
      apply exec_seq.
      (* if (q < e) ... else break; *)
      branch.
      + (* q < e: the body *)
        intros Hlt. apply exec_skip. normal.
        apply add_body_correct.
        * assumption.
        * lia.
      + (* q = e: break; no literals are left, and the model gives the count *)
        intros Hge. apply exec_break. abrupt. apply loopk_break.
        replace q with e in Hres by lia. rewrite span_lits_nil in Hres.
        cbn [add_lits] in Hres. unfold AddPost. rewrite <- Hres. splits.
        * assumption.
        * assumption.
        * left. split.
          -- reflexivity.
          -- exists pathc. split.
             ++ reflexivity.
             ++ assumption.
    - assumption.
  Qed.
End Loop.

(* add_lits adds the literals cl[q .. e) to the analysis at level d, skipping t: writing
   (x', r) for the model add_lits x d t (span_lits tc q e) pathc:

     {{ the precondition }}
     {{ add_inv q }}
       while (q < e) { ... }                                           (add_loop_correct)
     {{ RepL x' /\ m' is m on AddFrame /\
        (the count r in pathc \/ result = -1 /\ r = None) }}
       return pathc;
     {{ result = enc_count r }}

   The block cl has fewer than small_bound entries (as clits and rlits have), so that q
   and e are small: C compares them and increments q. *)
Lemma add_lits_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (b: block) (n: nat) (tc: nat -> Z) (q e: nat) (t: option Lit)
  (d pathc: nat),
  {{ m | RepL m sh N lss x /\ ClauseBlock sh b /\ Arr m b n tc /\ (q <= e <= n)%nat /\
         LitKeys N tc q e /\ OptBelow N t /\ (d <= N)%nat /\ (pathc <= N)%nat /\
         Z.of_nat n < small_bound }}
    f_add_lits(sptr sh, Vptr b Ptrofs.zero, vnat q, vnat e,
               vint (enc_lit t), vnat d, vnat pathc)
  {{ m', v | match add_lits x d t (span_lits tc q e) pathc with
             | (x', r) =>
               Gives sh N lss (AddFrame sh) x' (vint (enc_count r)) m m' v
             end }}.
Proof.
  intros sh N lss x b n tc q e t d pathc m
    (HRep & Hb & Alits & Hrange & Hkeys & Ht & Hd & Hpathc & Hn).
  remember (add_lits x d t (span_lits tc q e) pathc) as res eqn:Hres.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_add_lits. cbn [fn_body fn_return]. apply exec_seq.
    apply exec_weaken with (Q := AddPost m sh N lss res).
    + apply (add_loop_correct m sh N lss b n tc e t d res Hb Ht Hd Hn q).
      exists x, pathc. constructor.
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
      * frame.
      * assumption.
      * assumption.
      * symmetry. assumption.
    + intros le' m' out. unfold AddPost. destruct res as [x' r].
      intros (HRep' & Hkept & [(-> & pathc' & -> & Hpc') | (-> & ->)]).
      * (* the loop ended with the count: return pathc; *)
        normal. return_int.
        splits.
        -- reflexivity.
        -- assumption.
        -- apply Hkept.
      * (* the loop gave up: return -1 *)
        abrupt. exists (vint (-1)). splits.
        -- apply result_int.
        -- reflexivity.
        -- assumption.
        -- apply Hkept.
Qed.

Lemma add_lits_fun: FunAt _add_lits f_add_lits.
Proof. apply find_fun. reflexivity. Qed.
