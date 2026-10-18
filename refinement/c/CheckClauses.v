(* check_clauses checks that the literals of the clauses have atoms below N, and that no
   clause has a literal twice. *)
From Stdlib Require Import Bool.
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
From RocqSAT.refinement.c Require Import Arrays.
From RocqSAT.refinement.c Require Import Logic.
From RocqSAT.refinement.c Require Import Common.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Rep.

(* The marks tm, by key below 2 N, are 1 exactly for the literals ls. *)
Definition Marks (N: nat) (tm: nat -> Z) (ls: list Lit): Prop :=
  forall (k: nat), (k < 2 * N)%nat ->
    tm k = if existsb (fun (l: Lit) => Nat.eqb (lit_key l) k) ls then 1 else 0.

(* A literal is among ls exactly when one of them has its key. *)
Lemma existsb_key: forall (ls: list Lit) (l: Lit),
  existsb (fun (y: Lit) => Nat.eqb (lit_key y) (lit_key l)) ls = true <-> In l ls.
Proof.
  intros ls l. rewrite existsb_exists. split.
  - intros [y [Hy Hk]]. apply Nat.eqb_eq, lit_key_inj in Hk. now subst y.
  - intros Hl. exists l. split.
    + assumption.
    + apply Nat.eqb_refl.
Qed.

(* Marking a literal. *)
Lemma marks_add: forall (N: nat) (tm: nat -> Z) (ls: list Lit) (l: Lit),
  Marks N tm ls ->
  Marks N (fun (j: nat) => if Nat.eqb (lit_key l) j then 1 else tm j) (ls ++ [l]).
Proof.
  intros N tm ls l Hm k Hk. rewrite existsb_app. cbn [existsb]. rewrite orb_false_r.
  destruct (Nat.eqb_spec (lit_key l) k) as [<- | Hne].
  - now rewrite orb_true_r.
  - rewrite orb_false_r. now apply Hm.
Qed.

(* Unmarking the first literal of a list without duplicates. *)
Lemma marks_remove: forall (N: nat) (tm: nat -> Z) (ls: list Lit) (l: Lit),
  Marks N tm (l :: ls) -> ~ In l ls ->
  Marks N (fun (j: nat) => if Nat.eqb (lit_key l) j then 0 else tm j) ls.
Proof.
  intros N tm ls l Hm Hl k Hk. destruct (Nat.eqb_spec (lit_key l) k) as [<- | Hne].
  - destruct (existsb _ ls) eqn:Hex.
    + apply existsb_key in Hex. contradiction.
    + reflexivity.
  - rewrite (Hm k Hk). cbn [existsb].
    replace (Nat.eqb (lit_key l) k) with false by (symmetry; now apply Nat.eqb_neq).
    reflexivity.
Qed.

(* The clause literals at the positions a .. b - 1. *)
Definition span (sh: Shape) (a b: nat): list Lit := map (lits sh) (seq a (b - a)).

(* A span extended by the next position. *)
Lemma span_snoc: forall (sh: Shape) (a q: nat), (a <= q)%nat ->
  span sh a (S q) = span sh a q ++ [lits sh q].
Proof.
  intros sh a q Haq. unfold span.
  replace (S q - a)%nat with (S (q - a)) by lia.
  rewrite seq_S, map_app. cbn [map]. now replace (a + (q - a))%nat with q by lia.
Qed.

(* An empty span. *)
Lemma span_nil: forall (sh: Shape) (a: nat), span sh a a = [].
Proof. intros sh a. unfold span. now rewrite Nat.sub_diag. Qed.

(* A span starting with its first position. *)
Lemma span_cons: forall (sh: Shape) (q e: nat), (q < e)%nat ->
  span sh q e = lits sh q :: span sh (S q) e.
Proof.
  intros sh q e Hq. unfold span.
  replace (e - q)%nat with (S (e - S q)) by lia.
  reflexivity.
Qed.

(* A span without duplicates has none in its end either. *)
Lemma span_nodup_tail: forall (sh: Shape) (a q e: nat), (a <= q <= e)%nat ->
  NoDup (span sh a e) -> NoDup (span sh q e).
Proof.
  intros sh a q e Hq Hnd. unfold span in *.
  replace (e - a)%nat with ((q - a) + (e - q))%nat in Hnd by lia.
  rewrite seq_app, map_app in Hnd. apply NoDup_app_remove_l in Hnd.
  now replace (a + (q - a))%nat with q in Hnd by lia.
Qed.

(* The clauses lss lie one after the other in the clause literals of sh, from position 0
   to the end. *)
Record Layout {sh: Shape} {lss: list (list Lit)}: Prop := {
  ly_clause: forall (i: nat), (i < length lss)%nat ->
    (starts sh i <= starts sh (S i) <= nclits sh)%nat /\
    nth i lss [] = span sh (starts sh i) (starts sh (S i));
  ly_first: starts sh 0%nat = 0%nat;
  ly_end: starts sh (length lss) = nclits sh;
}.
Arguments Layout : clear implicits.

(* The sizes of the checks: N atoms below atom_bound, and the clause literals, their keys
   and the clauses below small_bound. *)
Record Sizes {sh: Shape} {N: nat} {lss: list (list Lit)}: Prop := {
  sz_n: Z.of_nat N < atom_bound;
  sz_nclits: Z.of_nat (nclits sh) < small_bound;
  sz_keys: forall (q: nat), (q < nclits sh)%nat -> key (lits sh q) < small_bound;
  sz_lss: Z.of_nat (length lss) < small_bound;
}.
Arguments Sizes : clear implicits.

(* The literals ls have atoms below N. *)
Definition AtomsBelow (N: nat) (ls: list Lit): Prop :=
  forall (l: Lit), In l ls -> (extract l < N)%nat.

(* A literal with atom below N added to literals with atoms below N. *)
Lemma atoms_below_snoc: forall (N: nat) (ls: list Lit) (l: Lit),
  AtomsBelow N ls -> (extract l < N)%nat -> AtomsBelow N (ls ++ [l]).
Proof.
  intros N ls l Hls Hl l' Hl'. apply in_app_or in Hl' as [Hl' | [<- | []]].
  - apply Hls. assumption.
  - assumption.
Qed.

(* A new literal added to distinct literals. *)
Lemma nodup_snoc: forall (ls: list Lit) (l: Lit),
  NoDup ls -> ~ In l ls -> NoDup (ls ++ [l]).
Proof.
  intros ls l Hnd Hl. apply NoDup_app.
  - assumption.
  - constructor.
    + easy.
    + constructor.
  - intros l' Hl' [<- | []]. contradiction.
Qed.

(* A property of the clauses below i and of clause i holds below i + 1. *)
Lemma below_succ: forall (P: nat -> Prop) (i: nat),
  (forall (i': nat), (i' < i)%nat -> P i') -> P i ->
  forall (i': nat), (i' < S i)%nat -> P i'.
Proof.
  intros P i Hbelow Hi i' Hi'. destruct (Nat.eq_dec i' i) as [-> | Hne].
  - assumption.
  - apply Hbelow. lia.
Qed.

(* The fields and arrays of the clauses in the memory m1, and the field of the marks. *)
Record ClauseFlds {sh: Shape} {N: nat} {lss: list (list Lit)} {m1: mem}: Prop := {
  cf_nv: IntAt m1 sh o_nv N;
  cf_ncl: IntAt m1 sh o_ncl (length lss);
  cf_cstart: PtrAt m1 sh o_cstart (b_cstart sh);
  cf_clits: PtrAt m1 sh o_clits (b_clits sh);
  cf_mrk: PtrAt m1 sh o_mrk (b_mrk sh);
  cf_starts: Arr m1 (b_cstart sh) (S (length lss))
    (fun (i: nat) => Z.of_nat (starts sh i));
  cf_lits: Arr m1 (b_clits sh) (nclits sh) (fun (q: nat) => key (lits sh q));
}.
Arguments ClauseFlds : clear implicits.

(* The memory m1 during check_clauses (and check_lits), from the memory m of the call:
   the clauses are in place, and only the marks (b_mrk sh) changed since m. *)
Record ClauseMem {m: mem} {sh: Shape} {N: nat} {lss: list (list Lit)}
  {m1: mem}: Prop := {
  cm_flds: ClauseFlds sh N lss m1;
  cm_frame: Mem.unchanged_on (AllBut (b_mrk sh)) m m1;
}.
Arguments ClauseMem : clear implicits.

(* A store to the marks keeps the memory facts of check_clauses. *)
Lemma clause_mem_store: forall (m m1 m2: mem) (sh: Shape) (N: nat)
  (lss: list (list Lit)) (ofs: Z) (v: val),
  NoDup (iblocks sh) -> ClauseMem m sh N lss m1 ->
  Mem.store Mint32 m1 (b_mrk sh) ofs v = Some m2 -> ClauseMem m sh N lss m2.
Proof.
  intros m m1 m2 sh N lss ofs v Hnd HM Hst. unfold iblocks in Hnd.
  destruct HM as [[Fnv Fncl Fcs Fcl Fm As Al] Hun]. constructor.
  - constructor.
    + apply (fld_store_other Fnv Hst). left. neq Hnd.
    + apply (fld_store_other Fncl Hst). left. neq Hnd.
    + apply (fld_store_other Fcs Hst). left. neq Hnd.
    + apply (fld_store_other Fcl Hst). left. neq Hnd.
    + apply (fld_store_other Fm Hst). left. neq Hnd.
    + apply (arr_store_other As Hst). neq Hnd.
    + apply (arr_store_other Al Hst). neq Hnd.
  - frame.
Qed.

(* The parts of check_clauses proved in lemmas of their own: the loop over the clauses,
   the statements for one clause in it, the marking and the unmarking loop in those, the
   body of the marking loop after its test, and the statements for a clause from the
   unmarking on. *)
Definition clauses_loop: statement :=
  first_stmt (drop_stmts 2 (fn_body f_check_clauses)).
Definition clause_part: statement := drop_stmts 1 (loop_body clauses_loop).
Definition mark_loop: statement := first_stmt (drop_stmts 3 clause_part).
Definition mark_body: statement := drop_stmts 1 (loop_body mark_loop).
Definition unmark_loop: statement := first_stmt (drop_stmts 5 clause_part).
Definition unmark_part: statement := drop_stmts 4 clause_part.

(* The variant of the marking and unmarking loops of clause i. *)
Definition clause_variant (sh: Shape) (i: nat): nat -> nat -> Prop :=
  ltof nat (fun (q: nat) => starts sh (S i) - q)%nat.

Section Loops.
  (* A call of check_clauses from the memory m, for the clauses lss of N atoms. *)
  Variables (m: mem) (sh: Shape) (N: nat) (lss: list (list Lit)).

  (* The invariant of the loop over the clauses at i: the temporaries hold s, n = 2 N
     and i; the clauses before i have atoms below N and no literal twice; nothing is
     marked. *)
  Record ClausesInv (i: nat) (le: temp_env) (m1: mem): Prop := {
    ki_s: le ! _s = Some (sptr sh);
    ki_n: le ! _n = Some (vnat (2 * N));
    ki_i: le ! _i = Some (vnat i);
    ki_le: (i <= length lss)%nat;
    ki_atoms: forall (i': nat), (i' < i)%nat -> AtomsBelow N (nth i' lss []);
    ki_nodup: forall (i': nat), (i' < i)%nat -> NoDup (nth i' lss []);
    ki_mem: ClauseMem m sh N lss m1;
    ki_marks: exists (tm: nat -> Z), Arr m1 (b_mrk sh) (2 * N) tm /\ Marks N tm [];
  }.

  (* The invariant of the marking loop of clause i at q: also b and e hold the bounds of
     the clause and q; the literals of the clause before q have atoms below N, are
     distinct, and are the marked ones. *)
  Record MarkInv (i q: nat) (le: temp_env) (m2: mem): Prop := {
    mi_s: le ! _s = Some (sptr sh);
    mi_n: le ! _n = Some (vnat (2 * N));
    mi_i: le ! _i = Some (vnat i);
    mi_b: le ! _b = Some (vnat (starts sh i));
    mi_e: le ! _e = Some (vnat (starts sh (S i)));
    mi_q: le ! _q = Some (vnat q);
    mi_range: (starts sh i <= q <= starts sh (S i))%nat;
    mi_atoms: AtomsBelow N (span sh (starts sh i) q);
    mi_nodup: NoDup (span sh (starts sh i) q);
    mi_mem: ClauseMem m sh N lss m2;
    mi_marks: exists (tm: nat -> Z), Arr m2 (b_mrk sh) (2 * N) tm /\
      Marks N tm (span sh (starts sh i) q);
  }.

  (* The invariant of the unmarking loop of clause i at q: the literals of the clause
     from q on are the marked ones. *)
  Record UnmarkInv (i q: nat) (le: temp_env) (m3: mem): Prop := {
    ui_s: le ! _s = Some (sptr sh);
    ui_n: le ! _n = Some (vnat (2 * N));
    ui_i: le ! _i = Some (vnat i);
    ui_e: le ! _e = Some (vnat (starts sh (S i)));
    ui_q: le ! _q = Some (vnat q);
    ui_range: (starts sh i <= q <= starts sh (S i))%nat;
    ui_mem: ClauseMem m sh N lss m3;
    ui_marks: exists (tm: nat -> Z), Arr m3 (b_mrk sh) (2 * N) tm /\
      Marks N tm (span sh q (starts sh (S i)));
  }.

  (* What the marking loop of clause i ends in: all of it marked, or a return of 0. *)
  Definition MarkPost (i: nat) (le: temp_env) (m2: mem) (out: outcome): Prop :=
    (out = Out_normal /\ MarkInv i (starts sh (S i)) le m2) \/
    out = ret_int 0.

  (* The blocks are distinct, and the clauses are laid out with the sizes of the
     checks. *)
  Hypothesis (Hnd: NoDup (iblocks sh)).
  Hypothesis (Hsz: Sizes sh N lss).
  Hypothesis (Hly: Layout sh lss).

  (* One pass of the marking loop, at q < e:

       {{ MarkInv i q /\ q < e }}
         int y = s->clits[q];
         if (y < 0) return 0;
         if (y >= n) return 0;
         if (s->mrk[y] != 0) return 0;
       {{ result = 0 (rejected) }}
       {{ MarkInv i q /\ y is a literal with atom below N, not marked }}
         s->mrk[y] = 1;
         q++;
       {{ MarkInv i (q + 1) }}                                                        *)
  Lemma mark_body_correct: forall (i q: nat) (le: temp_env) (m2: mem),
    (i < length lss)%nat -> MarkInv i q le m2 -> (q < starts sh (S i))%nat ->
    Exec ge le m2 mark_body (LoopK (clause_variant sh i) (MarkInv i) (MarkPost i) q).
  Proof.
    intros i q le m2 Hi HI Hqlt.
    destruct (ly_clause Hly i Hi) as [Hrange _]. pose proof Hsz as [HN Hncl Hkeys _].
    destruct HI as [Hs2 Hn2 Hi2 Hb2 He2 Hq2 Hqr Hat2 Hnd2 HM2 (tm2 & Am2 & Hm2)].
    pose proof HM2 as [[Fnv2 Fncl2 Fcs2 Fcl2 Fm2 As2 Al2] Hun2].
    unfold mark_body, mark_loop, clause_part, clauses_loop, f_check_clauses.
    cbn [fn_body drop_stmts first_stmt loop_body Swhile].
    assert (Hqn: (q < nclits sh)%nat) by lia.
    pose proof (Hkeys q Hqn) as Hkq.
    assert (Haddq: Int.add (Int.repr (Z.of_nat q)) (Int.repr 1)
                   = Int.repr (Z.of_nat (S q))).
    { rewrite add_repr by lia. f_equal. lia. }
    (* Keys are not negative. *)
    assert (Hkq0: 0 <= key (lits sh q)) by (unfold key; lia).
    (* int y = s->clits[q]; *)
    run.
    (* if (y < 0) return 0; never, as keys are not negative *)
    take_else (key (lits sh q)) 0 by lia.
    intros _. run.
    (* if (y >= n) return 0; *)
    eapply exec_if_ge.
    - ev.
    - ev.
    - reflexivity.
    - unfold key in *. lia.
    - (* the atom is not below N: return 0; *)
      intros Hge. eapply exec_return.
      + ev.
      + ret. now right.
    - (* the atom is below N: if (s->mrk[y] != 0) return 0; *)
      intros Hlt.
      assert (Hy: (extract (lits sh q) < N)%nat)
        by (unfold key in Hlt; destruct (lits sh q); simpl in *; lia).
      assert (Hky: (lit_key (lits sh q) < 2 * N)%nat) by (now apply lit_key_lt).
      run. rewrite (Hm2 _ Hky).
      eapply (exec_if_ne _ 0).
      + ev.
      + ev.
      + reflexivity.
      + destruct (existsb _ _); lia.
      + (* y is marked: a duplicate, return 0; *)
        intros Hmarked. eapply exec_return.
        * ev.
        * ret. now right.
      + (* y is new: s->mrk[y] = 1; q++; and the loop goes on *)
        intros Hunmarked.
        assert (Hnew: ~ In (lits sh q) (span sh (starts sh i) q)).
        { intros Hin. apply existsb_key in Hin. rewrite Hin in Hunmarked. lia. }
        run. store Am2 Hky as m3 Hst.
        run. ints. apply loopk_next with (S q).
        * unfold clause_variant, ltof. lia.
        * constructor.
          -- tmp.
          -- tmp.
          -- tmp.
          -- tmp.
          -- tmp.
          -- tmp.
          -- lia.
          -- rewrite span_snoc by lia. apply atoms_below_snoc.
             ++ assumption.
             ++ assumption.
          -- rewrite span_snoc by lia. apply nodup_snoc.
             ++ assumption.
             ++ assumption.
          -- apply (clause_mem_store m m2 m3 sh N lss _ _ Hnd HM2 Hst).
          -- eexists. split.
             ++ apply (arr_store Am2 Hky Hst).
             ++ rewrite span_snoc by lia. apply marks_add. assumption.
  Qed.

  (* The marking loop of clause i, from b = starts sh i to e = starts sh (i + 1):

       {{ MarkInv i b }}
         while (q < e) { ... }                                        (mark_body_correct)
       {{ MarkInv i e }}

     The loop ends: e - q decreases. *)
  Lemma mark_loop_correct: forall (i: nat) (le: temp_env) (m1: mem),
    (i < length lss)%nat -> MarkInv i (starts sh i) le m1 ->
    Exec ge le m1 mark_loop (MarkPost i).
  Proof.
    intros i le m1 Hi HI0.
    destruct (ly_clause Hly i Hi) as [Hrange _]. pose proof Hsz as [_ Hncl _ _].
    unfold mark_loop, clause_part, clauses_loop, f_check_clauses.
    cbn [fn_body drop_stmts first_stmt loop_body]. unfold Swhile.
    apply exec_loop with (R := clause_variant sh i) (I := MarkInv i)
      (a := starts sh i).
    - apply well_founded_ltof.
    - intros q le2 m2 HI. pose proof HI as HI'.
      destruct HI' as [Hs2 Hn2 Hi2 Hb2 He2 Hq2 Hqr Hat2 Hnd2 HM2 (tm2 & Am2 & Hm2)].
      pose proof HM2 as [[Fnv2 Fncl2 Fcs2 Fcl2 Fm2 As2 Al2] Hun2].
      apply exec_seq.
      (* if (q < e) ... else break; *)
      branch.
      + (* q < e: the body *)
        intros Hqlt. apply exec_skip. normal.
        apply (mark_body_correct i q le2 m2).
        * assumption.
        * assumption.
        * lia.
      + (* q >= e: break; the whole clause is marked *)
        intros Hqge. apply exec_break. abrupt. apply loopk_break. left.
        replace q with (starts sh (S i)) in HI by lia. split.
        * reflexivity.
        * assumption.
    - assumption.
  Qed.

  (* The unmarking loop of clause i, which has atoms below N and no literal twice:

       {{ UnmarkInv i b }}
         while (q < e) {
       {{ UnmarkInv i q /\ q < e }}
           s->mrk[s->clits[q]] = 0;
           q++;
       {{ UnmarkInv i (q + 1) }}               (marks_remove: the clause is distinct)
         }
       {{ UnmarkInv i e: nothing is marked }}

     The loop ends: e - q decreases. *)
  Lemma unmark_loop_correct: forall (i: nat) (le: temp_env) (m1: mem),
    (i < length lss)%nat -> AtomsBelow N (nth i lss []) -> NoDup (nth i lss []) ->
    UnmarkInv i (starts sh i) le m1 ->
    Exec ge le m1 unmark_loop (fun (le': temp_env) (m': mem) (out: outcome) =>
      out = Out_normal /\ UnmarkInv i (starts sh (S i)) le' m').
  Proof.
    intros i le m1 Hi Hat Hndc HI0.
    destruct (ly_clause Hly i Hi) as [Hrange Hclause].
    pose proof Hsz as [HN Hncl Hkeys _].
    unfold unmark_loop, clause_part, clauses_loop, f_check_clauses.
    cbn [fn_body drop_stmts first_stmt loop_body]. unfold Swhile.
    apply exec_loop with (R := clause_variant sh i) (I := UnmarkInv i)
      (a := starts sh i).
    - apply well_founded_ltof.
    - intros q le3 m3 HI. pose proof HI as HI'.
      destruct HI' as [Hs3 Hn3 Hi3 He3 Hq3 Hqr HM3 (tm3 & Am3 & Hm3)].
      pose proof HM3 as [[Fnv3 Fncl3 Fcs3 Fcl3 Fm3 As3 Al3] Hun3].
      apply exec_seq.
      (* if (q < e) ... else break; *)
      branch.
      + (* q < e: s->mrk[s->clits[q]] = 0; q++; *)
        intros Hqlt.
        assert (Hin: In (lits sh q) (nth i lss [])).
        { rewrite Hclause. unfold span. apply in_map, in_seq. lia. }
        assert (Hky: (lit_key (lits sh q) < 2 * N)%nat).
        { apply lit_key_lt. apply Hat. assumption. }
        assert (Hqn: (q < nclits sh)%nat) by lia.
        pose proof (Hkeys q Hqn) as Hkq.
        assert (Haddq: Int.add (Int.repr (Z.of_nat q)) (Int.repr 1)
                       = Int.repr (Z.of_nat (S q))).
        { rewrite add_repr by lia. f_equal. lia. }
        (* The literal at q is not in the rest of the clause. *)
        assert (Hnd3: NoDup (span sh q (starts sh (S i)))).
        { apply (span_nodup_tail sh (starts sh i)).
          - lia.
          - rewrite <- Hclause. assumption. }
        rewrite span_cons in Hnd3 by lia.
        run. store Am3 Hky as m4 Hst.
        run. ints. apply loopk_next with (S q).
        * unfold clause_variant, ltof. lia.
        * constructor.
          -- tmp.
          -- tmp.
          -- tmp.
          -- tmp.
          -- tmp.
          -- lia.
          -- apply (clause_mem_store m m3 m4 sh N lss _ _ Hnd HM3 Hst).
          -- eexists. split.
             ++ apply (arr_store Am3 Hky Hst).
             ++ apply marks_remove.
                ** rewrite <- span_cons by lia. assumption.
                ** inversion Hnd3. assumption.
      + (* q >= e: break; nothing is marked *)
        intros Hqge. apply exec_break. abrupt. apply loopk_break.
        replace q with (starts sh (S i)) in HI by lia. split.
        * reflexivity.
        * assumption.
    - assumption.
  Qed.
  (* The variant of the loop over the clauses. *)
  Abbreviation clauses_variant := (ltof nat (fun (i: nat) => length lss - i)%nat).

  (* Setting a temporary other than s, n and i keeps the invariant of the loop over the
     clauses. *)
  Lemma clauses_inv_set: forall (i: nat) (le: temp_env) (m1: mem) (j: ident) (v: val),
    j <> _s -> j <> _n -> j <> _i -> ClausesInv i le m1 ->
    ClausesInv i (PTree.set j v le) m1.
  Proof.
    intros i le m1 j v Hs Hn Hi [Hs1 Hn1 Hi1 Hile Hat Hnd' HM1 Hmarks]. constructor.
    - rewrite PTree.gso by congruence. assumption.
    - rewrite PTree.gso by congruence. assumption.
    - rewrite PTree.gso by congruence. assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
  Qed.

  (* The statements for clause i from the unmarking on, once all of it is marked (and so
     has atoms below N and no literal twice):

       {{ MarkInv i e }}
         q = b;
       {{ UnmarkInv i b }}
         while (q < e) { ... }                                    (unmark_loop_correct)
       {{ UnmarkInv i e: nothing is marked }}
         i++;
       {{ ClausesInv (i + 1) }}                                           (below_succ) *)
  Lemma unmark_part_correct: forall (i: nat) (le: temp_env) (m2: mem)
    (K: temp_env -> mem -> outcome -> Prop),
    (i < length lss)%nat ->
    (forall (i': nat), (i' < i)%nat -> AtomsBelow N (nth i' lss [])) ->
    (forall (i': nat), (i' < i)%nat -> NoDup (nth i' lss [])) ->
    MarkInv i (starts sh (S i)) le m2 ->
    Exec ge le m2 unmark_part (LoopK clauses_variant ClausesInv K i).
  Proof.
    intros i le m2 K Hi Hat Hnd' HA.
    destruct HA as [Hs2 Hn2 Hi2 Hb2 He2 _ _ Hat2 Hnd2 HM2 (tm2 & Am2 & Hm2)].
    destruct (ly_clause Hly i Hi) as [Hrange Hclause].
    pose proof Hsz as [_ _ _ Hlss].
    rewrite <- Hclause in Hat2, Hnd2, Hm2.
    assert (Hadd: Int.add (Int.repr (Z.of_nat i)) (Int.repr 1)
                  = Int.repr (Z.of_nat (S i))).
    { rewrite add_repr by lia. f_equal. lia. }
    unfold unmark_part, clause_part, clauses_loop, f_check_clauses.
    cbn [fn_body drop_stmts first_stmt loop_body].
    (* q = b; *)
    run.
    apply exec_weaken
      with (Q := fun (le: temp_env) (m3: mem) (out: outcome) =>
                   out = Out_normal /\ UnmarkInv i (starts sh (S i)) le m3).
    - apply unmark_loop_correct.
      + assumption.
      + assumption.
      + assumption.
      + (* The unmarking invariant holds at q = b. *)
        constructor.
        * tmp.
        * tmp.
        * tmp.
        * tmp.
        * tmp.
        * lia.
        * assumption.
        * exists tm2. split.
          -- assumption.
          -- rewrite <- Hclause. assumption.
    - (* nothing is marked: i++; and the invariant holds for i + 1 *)
      intros le3 m3 out (-> & HC).
      destruct HC as [Hs3 Hn3 Hi3 _ _ _ HM3 (tm3 & Am3 & Hm3)].
      normal. run. ints. apply loopk_next with (S i).
      + unfold ltof. lia.
      + constructor.
        * tmp.
        * tmp.
        * tmp.
        * lia.
        * apply below_succ.
          -- assumption.
          -- assumption.
        * apply below_succ.
          -- assumption.
          -- assumption.
        * assumption.
        * exists tm3. split.
          -- assumption.
          -- rewrite span_nil in Hm3. assumption.
  Qed.

  (* The statements for clause i < ncl: the marking loop rejects the clause or marks all
     of it, and then the unmarking follows. The continuation K of the loop over the
     clauses accepts a return of 0:

       {{ ClausesInv i /\ i < ncl }}
         int b = s->cstart[i];
         int e = s->cstart[i + 1];
         int q = b;
       {{ MarkInv i b }}
         while (q < e) { ... }                                      (mark_loop_correct)
       {{ MarkInv i e, or result = 0 (rejected) }}
         q = b; ...; i++;                                         (unmark_part_correct)
       {{ ClausesInv (i + 1) }}                                                       *)
  Lemma clause_part_correct: forall (i: nat) (le: temp_env) (m1: mem)
    (K: temp_env -> mem -> outcome -> Prop),
    (forall (le': temp_env) (m': mem), K le' m' (ret_int 0)) ->
    (i < length lss)%nat -> ClausesInv i le m1 ->
    Exec ge le m1 clause_part (LoopK clauses_variant ClausesInv K i).
  Proof.
    intros i le m1 K HK Hi HI.
    destruct HI as [Hs Hn Hi1 Hile Hat Hnd' HM1 (tm1 & Am1 & Hm1)].
    pose proof HM1 as [[Fnv1 Fncl1 Fcs1 Fcl1 Fm1 As1 Al1] Hun1].
    destruct (ly_clause Hly i Hi) as [Hrange _].
    pose proof Hsz as [HN Hncl Hkeys Hlss].
    assert (Hadd: Int.add (Int.repr (Z.of_nat i)) (Int.repr 1)
                  = Int.repr (Z.of_nat (S i))).
    { rewrite add_repr by lia. f_equal. lia. }
    unfold clause_part, clauses_loop, f_check_clauses.
    cbn [fn_body drop_stmts first_stmt loop_body].
    (* int b = s->cstart[i]; int e = s->cstart[i + 1]; int q = b; *)
    run.
    (* The marking loop: all of clause i marked, or a return of 0. *)
    apply exec_weaken with (Q := MarkPost i).
    - apply mark_loop_correct.
      + assumption.
      + (* The marking invariant holds at q = b, with nothing marked. *)
        constructor.
        * tmp.
        * tmp.
        * tmp.
        * tmp.
        * tmp.
        * tmp.
        * lia.
        * rewrite span_nil. intros l [].
        * rewrite span_nil. constructor.
        * assumption.
        * exists tm1. split.
          -- assumption.
          -- rewrite span_nil. assumption.
    - intros le2 m2 out [[-> HA] | ->].
      + (* all of clause i is marked: the unmarking *)
        normal. apply unmark_part_correct.
        * assumption.
        * assumption.
        * assumption.
        * assumption.
      + (* return 0 from the marking loop *)
        ret. apply HK.
  Qed.
End Loops.

(* check_clauses marks the literals of each clause in turn, rejecting a literal out of
   range or marked already (a duplicate), and then unmarks them again:

     {{ ClauseFlds m /\ Layout /\ Sizes /\ nothing is marked }}
       int n = 2 * s->nv;
       int i = 0;
     {{ ClausesInv 0 }}
       while (i < s->ncl) {
     {{ ClausesInv i /\ i < ncl }}
         int b = s->cstart[i];                                    (clause_part_correct)
         int e = s->cstart[i + 1];
         int q = b;
     {{ MarkInv i b }}
         while (q < e) {
     {{ MarkInv i q /\ q < e }}
           int y = s->clits[q];                                     (mark_body_correct)
           if (y < 0) return 0;
           if (y >= n) return 0;
           if (s->mrk[y] != 0) return 0;
     {{ result = 0 (rejected) }}
     {{ MarkInv i q /\ y is a literal with atom below N, not marked }}
           s->mrk[y] = 1;
           q++;
     {{ MarkInv i (q + 1) }}
         }
     {{ MarkInv i e }}
         q = b;                                                   (unmark_part_correct)
     {{ UnmarkInv i b }}
         while (q < e) {
           s->mrk[s->clits[q]] = 0;
           q++;
     {{ UnmarkInv i (q + 1) }}
         }
     {{ UnmarkInv i e: nothing is marked }}
         i++;
     {{ ClausesInv (i + 1) }}
       }
     {{ ClausesInv ncl }}
       return 1;
     {{ result = 1 /\ every clause has atoms below N and no literal twice }}

   The loops end: length lss - i and starts sh (i + 1) - q decrease. *)
Lemma check_clauses_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (tm: nat -> Z),
  {{ m | NoDup (iblocks sh) /\ ClauseFlds sh N lss m /\ Layout sh lss /\
         Sizes sh N lss /\ Arr m (b_mrk sh) (2 * N) tm /\ Marks N tm [] }}
    f_check_clauses(sptr sh)
  {{ m', v | v = vint 0 \/
             (v = vint 1 /\
              (forall (i: nat), (i < length lss)%nat -> AtomsBelow N (nth i lss [])) /\
              (forall (i: nat), (i < length lss)%nat -> NoDup (nth i lss [])) /\
              (exists (tm': nat -> Z),
                 Arr m' (b_mrk sh) (2 * N) tm' /\ Marks N tm' []) /\
              Mem.unchanged_on (AllBut (b_mrk sh)) m m') }}.
Proof.
  intros sh N lss tm m (Hnd & HF & Hly & Hsz & Amrk & Hm0).
  pose proof HF as [Fnv Fncl Fcstart Fclits Fmrk Astarts Alits].
  pose proof Hsz as [HN Hncl Hkeys Hlss].
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_check_clauses. cbn [fn_body fn_return].
    assert (Hmul: Int.mul (Int.repr 2) (Int.repr (Z.of_nat N))
                  = Int.repr (Z.of_nat (2 * N))).
    { rewrite mul_repr. f_equal. lia. }
    (* int n = 2 * s->nv; int i = 0; *)
    run. ints.
    apply exec_loop with (R := ltof nat (fun (i: nat) => length lss - i)%nat)
      (I := ClausesInv m sh N lss) (a := 0%nat).
    + apply well_founded_ltof.
    + intros i le1 m1 HI.
      pose proof HI as [Hs Hn Hi Hile Hat Hnd' HM1 (tm1 & Am1 & Hm1)].
      pose proof HM1 as [[Fnv1 Fncl1 Fcs1 Fcl1 Fm1 As1 Al1] Hun1].
      clear Fnv Fncl Fcstart Fclits Fmrk Astarts Alits Amrk.
      (* if (i < s->ncl) ... else break; *)
      run. branch.
      * (* i < ncl: the statements for clause i *)
        intros Hi_ncl. apply exec_skip. normal.
        apply (clause_part_correct m sh N lss Hnd Hsz Hly).
        -- (* a return of 0 is a result of check_clauses *)
           intros le' m'. ret. exists (vint 0). split.
           ++ apply result_int.
           ++ now left.
        -- lia.
        -- apply clauses_inv_set.
           ++ discriminate.
           ++ discriminate.
           ++ discriminate.
           ++ assumption.
      * (* i >= ncl: break; return 1; every clause is checked *)
        intros Hncl_le. apply exec_break. abrupt. apply loopk_break. normal.
        return_int.
        right. splits.
        -- reflexivity.
        -- intros i' Hi'. apply Hat. lia.
        -- intros i' Hi'. apply Hnd'. lia.
        -- exists tm1. split; assumption.
        -- assumption.
    + (* The invariant holds at i = 0. *)
      constructor.
      * tmp.
      * tmp.
      * tmp.
      * lia.
      * intros i' Hi'. lia.
      * intros i' Hi'. lia.
      * constructor.
        -- assumption.
        -- frame.
      * exists tm. split; assumption.
Qed.

Lemma check_clauses_fun: FunAt _check_clauses f_check_clauses.
Proof. apply find_fun. reflexivity. Qed.
