(* check_clauses checks that the literals of the clauses have atoms below N, and that no
   clause has a literal twice. *)
From Stdlib Require Import List Bool.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep.
Import ListNotations.

(* The marks tm, by key below 2 N, are 1 exactly for the literals ls. *)
Definition Marks (N: nat) (tm: nat -> Z) (ls: list Lit): Prop :=
  forall (k: nat), (k < 2 * N)%nat ->
    tm k = if existsb (fun (l: Lit) => Nat.eqb (lit_key l) k) ls then 1 else 0.

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
Definition span (S: Shape) (a b: nat): list Lit := map (lits S) (seq a (b - a)).

(* A span extended by the next position. *)
Lemma span_snoc: forall (S: Shape) (a q: nat), (a <= q)%nat ->
  span S a (Datatypes.S q) = span S a q ++ [lits S q].
Proof.
  intros S a q Haq. unfold span.
  replace (Datatypes.S q - a)%nat with (Datatypes.S (q - a)) by lia.
  rewrite seq_S, map_app. cbn [map]. now replace (a + (q - a))%nat with q by lia.
Qed.

(* A span starting with its first position. *)
Lemma span_cons: forall (S: Shape) (q e: nat), (q < e)%nat ->
  span S q e = lits S q :: span S (Datatypes.S q) e.
Proof.
  intros S q e Hq. unfold span.
  replace (e - q)%nat with (Datatypes.S (e - Datatypes.S q)) by lia.
  reflexivity.
Qed.

(* A span without duplicates has none in its end either. *)
Lemma span_nodup_tail: forall (S: Shape) (a q e: nat), (a <= q <= e)%nat ->
  NoDup (span S a e) -> NoDup (span S q e).
Proof.
  intros S a q e Hq Hnd. unfold span in *.
  replace (e - a)%nat with ((q - a) + (e - q))%nat in Hnd by lia.
  rewrite seq_app, map_app in Hnd. apply NoDup_app_remove_l in Hnd.
  now replace (a + (q - a))%nat with q in Hnd by lia.
Qed.

(* The literals ls have atoms below N. *)
Definition AtomsBelow (N: nat) (ls: list Lit): Prop :=
  forall (l: Lit), In l ls -> (extract l < N)%nat.

(* The memory m1 during check_clauses, from the memory m of the call: the fields and
   arrays it reads are in place, and only the marks bm changed since m. *)
Record ClauseMem (m: mem) (S: Shape) (bm: block) (N: nat) (lss: list (list Lit))
  (m1: mem): Prop := {
  cm_nv: Fld m1 (b_s S) 0 Mint32 (vint (Z.of_nat N));
  cm_ncl: Fld m1 (b_s S) 4 Mint32 (vint (Z.of_nat (length lss)));
  cm_cstart: Fld m1 (b_s S) 8 Mptr (Vptr (b_cstart S) Ptrofs.zero);
  cm_clits: Fld m1 (b_s S) 16 Mptr (Vptr (b_clits S) Ptrofs.zero);
  cm_mrk: Fld m1 (b_s S) 152 Mptr (Vptr bm Ptrofs.zero);
  cm_starts: Arr m1 (b_cstart S) (Datatypes.S (length lss))
    (fun (i: nat) => Z.of_nat (starts S i));
  cm_lits: Arr m1 (b_clits S) (nclits S) (fun (q: nat) => key (lits S q));
  cm_frame: Mem.unchanged_on (fun (b: block) (_: Z) => b <> bm) m m1;
}.

(* A store to the marks keeps the memory facts of check_clauses. *)
Lemma clause_mem_store: forall (m m1 m2: mem) (S: Shape) (bm: block) (N: nat)
  (lss: list (list Lit)) (ofs: Z) (v: val),
  NoDup (iblocks S bm) -> ClauseMem m S bm N lss m1 ->
  Mem.store Mint32 m1 bm ofs v = Some m2 -> ClauseMem m S bm N lss m2.
Proof.
  intros m m1 m2 S bm N lss ofs v Hnd HM Hst. unfold iblocks in Hnd.
  destruct HM as [Fnv Fncl Fcs Fcl Fm As Al Hun]. constructor.
  - apply (fld_store_other _ _ _ _ _ _ _ _ _ _ Fnv Hst). left. neq Hnd.
  - apply (fld_store_other _ _ _ _ _ _ _ _ _ _ Fncl Hst). left. neq Hnd.
  - apply (fld_store_other _ _ _ _ _ _ _ _ _ _ Fcs Hst). left. neq Hnd.
  - apply (fld_store_other _ _ _ _ _ _ _ _ _ _ Fcl Hst). left. neq Hnd.
  - apply (fld_store_other _ _ _ _ _ _ _ _ _ _ Fm Hst). left. neq Hnd.
  - apply (arr_store_other _ _ _ _ _ _ _ _ _ As Hst). neq Hnd.
  - apply (arr_store_other _ _ _ _ _ _ _ _ _ Al Hst). neq Hnd.
  - apply (store_unchanged _ m m1 m2 Mint32 bm ofs v Hun Hst). intros i Hi. now apply Hi.
Qed.

(* The invariant of the loop over the clauses at i: the temporaries hold s, n = 2 N and
   i; the clauses before i have atoms below N and no literal twice; nothing is marked. *)
Record ClausesInv (m: mem) (S: Shape) (bm: block) (N: nat) (lss: list (list Lit))
  (i: nat) (le: temp_env) (m1: mem): Prop := {
  ki_s: le ! _s = Some (sptr S);
  ki_n: le ! _n = Some (vint (Z.of_nat (2 * N)));
  ki_i: le ! _i = Some (vint (Z.of_nat i));
  ki_le: (i <= length lss)%nat;
  ki_atoms: forall (i': nat), (i' < i)%nat -> AtomsBelow N (nth i' lss []);
  ki_nodup: forall (i': nat), (i' < i)%nat -> NoDup (nth i' lss []);
  ki_mem: ClauseMem m S bm N lss m1;
  ki_marks: exists (tm: nat -> Z), Arr m1 bm (2 * N) tm /\ Marks N tm [];
}.

(* The invariant of the marking loop of clause i at q: also b and e hold the bounds of
   the clause and q; the literals of the clause before q have atoms below N, are
   distinct, and are the marked ones. *)
Record MarkInv (m: mem) (S: Shape) (bm: block) (N: nat) (lss: list (list Lit)) (i q: nat)
  (le: temp_env) (m2: mem): Prop := {
  mi_s: le ! _s = Some (sptr S);
  mi_n: le ! _n = Some (vint (Z.of_nat (2 * N)));
  mi_i: le ! _i = Some (vint (Z.of_nat i));
  mi_b: le ! _b = Some (vint (Z.of_nat (starts S i)));
  mi_e: le ! _e = Some (vint (Z.of_nat (starts S (Datatypes.S i))));
  mi_q: le ! _q = Some (vint (Z.of_nat q));
  mi_range: (starts S i <= q <= starts S (Datatypes.S i))%nat;
  mi_atoms: AtomsBelow N (span S (starts S i) q);
  mi_nodup: NoDup (span S (starts S i) q);
  mi_mem: ClauseMem m S bm N lss m2;
  mi_marks: exists (tm: nat -> Z), Arr m2 bm (2 * N) tm /\
    Marks N tm (span S (starts S i) q);
}.

(* After the marking loop: clause i has atoms below N, is without duplicates, and is
   marked. *)
Record MarkedAll (m: mem) (S: Shape) (bm: block) (N: nat) (lss: list (list Lit)) (i: nat)
  (le: temp_env) (m2: mem): Prop := {
  ma_s: le ! _s = Some (sptr S);
  ma_n: le ! _n = Some (vint (Z.of_nat (2 * N)));
  ma_i: le ! _i = Some (vint (Z.of_nat i));
  ma_b: le ! _b = Some (vint (Z.of_nat (starts S i)));
  ma_e: le ! _e = Some (vint (Z.of_nat (starts S (Datatypes.S i))));
  ma_atoms: AtomsBelow N (nth i lss []);
  ma_nodup: NoDup (nth i lss []);
  ma_mem: ClauseMem m S bm N lss m2;
  ma_marks: exists (tm: nat -> Z), Arr m2 bm (2 * N) tm /\ Marks N tm (nth i lss []);
}.

(* The invariant of the unmarking loop of clause i at q: the literals of the clause from
   q on are the marked ones. *)
Record UnmarkInv (m: mem) (S: Shape) (bm: block) (N: nat) (lss: list (list Lit))
  (i q: nat) (le: temp_env) (m3: mem): Prop := {
  ui_s: le ! _s = Some (sptr S);
  ui_n: le ! _n = Some (vint (Z.of_nat (2 * N)));
  ui_i: le ! _i = Some (vint (Z.of_nat i));
  ui_e: le ! _e = Some (vint (Z.of_nat (starts S (Datatypes.S i))));
  ui_q: le ! _q = Some (vint (Z.of_nat q));
  ui_range: (starts S i <= q <= starts S (Datatypes.S i))%nat;
  ui_mem: ClauseMem m S bm N lss m3;
  ui_marks: exists (tm: nat -> Z), Arr m3 bm (2 * N) tm /\
    Marks N tm (span S q (starts S (Datatypes.S i)));
}.

(* After the unmarking loop: nothing is marked. *)
Record ClearedAll (m: mem) (S: Shape) (bm: block) (N: nat) (lss: list (list Lit))
  (i: nat) (le: temp_env) (m3: mem): Prop := {
  ca_s: le ! _s = Some (sptr S);
  ca_n: le ! _n = Some (vint (Z.of_nat (2 * N)));
  ca_i: le ! _i = Some (vint (Z.of_nat i));
  ca_mem: ClauseMem m S bm N lss m3;
  ca_marks: exists (tm: nat -> Z), Arr m3 bm (2 * N) tm /\ Marks N tm [];
}.

(* The parts of check_clauses proved in lemmas of their own: the loop over the clauses,
   the statements for one clause in it, the marking and the unmarking loop in those, and
   the body of the marking loop after its test. *)
Definition clauses_loop: statement :=
  first_stmt (drop_stmts 2 (fn_body f_check_clauses)).
Definition clause_part: statement := drop_stmts 1 (loop_body clauses_loop).
Definition mark_loop: statement := first_stmt (drop_stmts 3 clause_part).
Definition mark_body: statement := drop_stmts 1 (loop_body mark_loop).
Definition unmark_loop: statement := first_stmt (drop_stmts 5 clause_part).

(* What the marking loop of clause i ends in: all of it marked, or a return of 0. *)
Definition MarkPost (m: mem) (S: Shape) (bm: block) (N: nat) (lss: list (list Lit))
  (i: nat) (le: temp_env) (m2: mem) (out: outcome): Prop :=
  (out = Out_normal /\ MarkedAll m S bm N lss i le m2) \/
  out = Out_return (Some (vint 0, Ctypesdefs.tint)).

(* The variant of the marking and unmarking loops of clause i. *)
Definition clause_variant (S: Shape) (i: nat): nat -> nat -> Prop :=
  ltof nat (fun (q: nat) => starts S (Datatypes.S i) - q)%nat.

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
     {{ MarkInv i (q + 1) }}                                                          *)
Lemma mark_body_correct: forall (m m2: mem) (S: Shape) (bm: block) (N: nat)
  (lss: list (list Lit)) (i q: nat) (le: temp_env),
  NoDup (iblocks S bm) -> Z.of_nat N < 268435456 -> Z.of_nat (nclits S) < 1073741824 ->
  (starts S (Datatypes.S i) <= nclits S)%nat ->
  (forall (q: nat), (q < nclits S)%nat -> key (lits S q) < 1073741824) ->
  MarkInv m S bm N lss i q le m2 -> (q < starts S (Datatypes.S i))%nat ->
  Exec ge le m2 mark_body
    (LoopK (clause_variant S i) (MarkInv m S bm N lss i) (MarkPost m S bm N lss i) q).
Proof.
  intros m m2 S bm N lss i q le Hnd HN Hncl Hend Hkeys HI Hqlt.
  destruct HI as [Hs2 Hn2 Hi2 Hb2 He2 Hq2 Hqr Hat2 Hnd2 HM2 (tm2 & Am2 & Hm2)].
  pose proof HM2 as HM2'. destruct HM2' as [Fnv2 Fncl2 Fcs2 Fcl2 Fm2 As2 Al2 Hun2].
  unfold mark_body, mark_loop, clause_part, clauses_loop, f_check_clauses.
  cbn [fn_body drop_stmts first_stmt loop_body Swhile].
  assert (Hqn: (q < nclits S)%nat) by lia.
  pose proof (Hkeys q Hqn) as Hkq.
  assert (Haddq: Int.add (Int.repr (Z.of_nat q)) (Int.repr 1)
                 = Int.repr (Z.of_nat (Datatypes.S q))).
  { rewrite add_repr by lia. f_equal. lia. }
  (* int y = s->clits[q]; *)
  run.
  (* if (y < 0) return 0; never, as keys are not negative *)
  eapply (exec_if_cmp _ _ _ Clt _ _ _ 0).
  - ev.
  - ev.
  - reflexivity.
  - reflexivity.
  - unfold Small, key in *. lia.
  - unfold Small. lia.
  - replace (zcmp Clt (key (lits S q)) 0) with false
      by (symmetry; cbn [zcmp]; apply Z.ltb_ge; unfold key; lia).
    cbv beta iota. run.
    (* if (y >= n) return 0; *)
    eapply (exec_if_cmp _ _ _ Cge).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + unfold Small, key in *. lia.
    + unfold Small. lia.
    + destruct (Nat.lt_ge_cases (extract (lits S q)) N) as [Hy | Hy].
      * (* the atom is below N: if (s->mrk[y] != 0) return 0; *)
        replace (zcmp Cge (key (lits S q)) (Z.of_nat (2 * N))) with false
          by (symmetry; cbn [zcmp]; apply Z.leb_gt; unfold key;
              destruct (lits S q); simpl in *; lia).
        assert (Hky: (lit_key (lits S q) < 2 * N)%nat) by (now apply lit_key_lt).
        cbv beta iota. run. rewrite (Hm2 _ Hky).
        eapply (exec_if_cmp _ _ _ Cne _ _ _ 0).
        -- ev.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- unfold Small. destruct (existsb _ _); lia.
        -- unfold Small. lia.
        -- destruct (existsb (fun (l: Lit) => Nat.eqb (lit_key l) (lit_key (lits S q)))
                       (span S (starts S i) q)) eqn:Hex.
           ++ (* y is marked: a duplicate, return 0; *)
              change (zcmp Cne 1 0) with true. cbv beta iota. eapply exec_return.
              ** ev.
              ** ret. now right.
           ++ (* s->mrk[y] = 1; q++; *)
              change (zcmp Cne 0 0) with false. cbv beta iota. run. eapply exec_store.
              ** evl.
              ** ev.
              ** reflexivity.
              ** reflexivity.
              ** ofs. bound.
              ** ofs. cbn [cast_int_int].
                 destruct (arr_storable m2 bm (2 * N) (lit_key (lits S q)) tm2 1 Am2 Hky)
                   as [m3 Hst].
                 exists m3. split.
                 --- apply Hst.
                 --- normal. run. ints. apply loopk_next with (Datatypes.S q).
                     +++ unfold clause_variant, ltof. lia.
                     +++ constructor.
                         *** tmp.
                         *** tmp.
                         *** tmp.
                         *** tmp.
                         *** tmp.
                         *** tmp.
                         *** lia.
                         *** rewrite span_snoc by lia. intros l Hl.
                             apply in_app_or in Hl as [Hl | [<- | []]].
                             ---- apply Hat2. assumption.
                             ---- assumption.
                         *** rewrite span_snoc by lia. apply NoDup_app.
                             ---- assumption.
                             ---- constructor.
                                  ++++ easy.
                                  ++++ constructor.
                             ---- intros l Hl [<- | []]. apply existsb_key in Hl.
                                  congruence.
                         *** apply (clause_mem_store m m2 m3 S bm N lss _ _ Hnd HM2 Hst).
                         *** eexists. split.
                             ---- apply (arr_store m2 m3 bm (2 * N) _ tm2 1 Am2 Hky Hst).
                             ---- rewrite span_snoc by lia. apply marks_add. assumption.
      * (* the atom is not below N: return 0; *)
        replace (zcmp Cge (key (lits S q)) (Z.of_nat (2 * N))) with true
          by (symmetry; cbn [zcmp]; apply Z.leb_le; unfold key;
              destruct (lits S q); simpl in *; lia).
        cbv beta iota. eapply exec_return.
        -- ev.
        -- ret. now right.
Qed.

(* The marking loop of clause i, from b = starts S i to e = starts S (i + 1):

     {{ MarkInv i b }}
       while (q < e) { ... }                                        (mark_body_correct)
     {{ MarkInv i q /\ q >= e }} ->>
     {{ MarkedAll i }}

   The loop ends: e - q decreases. *)
Lemma mark_loop_correct: forall (m m1: mem) (S: Shape) (bm: block) (N: nat)
  (lss: list (list Lit)) (i: nat) (le: temp_env),
  NoDup (iblocks S bm) -> Z.of_nat N < 268435456 -> Z.of_nat (nclits S) < 1073741824 ->
  (starts S i <= starts S (Datatypes.S i) <= nclits S)%nat ->
  nth i lss [] = span S (starts S i) (starts S (Datatypes.S i)) ->
  (forall (q: nat), (q < nclits S)%nat -> key (lits S q) < 1073741824) ->
  MarkInv m S bm N lss i (starts S i) le m1 ->
  Exec ge le m1 mark_loop (MarkPost m S bm N lss i).
Proof.
  intros m m1 S bm N lss i le Hnd HN Hncl Hrange Hclause Hkeys HI0.
  unfold mark_loop, clause_part, clauses_loop, f_check_clauses.
  cbn [fn_body drop_stmts first_stmt loop_body]. unfold Swhile.
  apply exec_loop with (R := clause_variant S i) (I := MarkInv m S bm N lss i)
    (a := starts S i).
  - apply well_founded_ltof.
  - intros q le2 m2 HI. pose proof HI as HI'.
    destruct HI' as [Hs2 Hn2 Hi2 Hb2 He2 Hq2 Hqr Hat2 Hnd2 HM2 (tm2 & Am2 & Hm2)].
    pose proof HM2 as HM2'. destruct HM2' as [Fnv2 Fncl2 Fcs2 Fcl2 Fm2 As2 Al2 Hun2].
    apply exec_seq.
    (* if (q < e) ... else break; *)
    eapply (exec_if_cmp _ _ _ Clt).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + unfold Small. lia.
    + unfold Small. lia.
    + destruct (Nat.lt_ge_cases q (starts S (Datatypes.S i))) as [Hqlt | Hqge].
      * (* q < e: the body *)
        replace (zcmp Clt (Z.of_nat q) (Z.of_nat (starts S (Datatypes.S i)))) with true
          by (symmetry; cbn [zcmp]; apply Z.ltb_lt; lia).
        cbv beta iota. apply exec_skip. normal.
        apply (mark_body_correct m m2 S bm N lss i q le2).
        -- assumption.
        -- assumption.
        -- assumption.
        -- lia.
        -- assumption.
        -- assumption.
        -- assumption.
      * (* q >= e: break; the whole clause is marked *)
        replace (zcmp Clt (Z.of_nat q) (Z.of_nat (starts S (Datatypes.S i)))) with false
          by (symmetry; cbn [zcmp]; apply Z.ltb_ge; lia).
        cbv beta iota. apply exec_break. abrupt. apply loopk_break. left.
        replace q with (starts S (Datatypes.S i)) in * by lia.
        rewrite <- Hclause in Hat2, Hnd2, Hm2. split.
        -- reflexivity.
        -- constructor.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ exists tm2. split; assumption.
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
     {{ UnmarkInv i q /\ q >= e }} ->>
     {{ ClearedAll i }}

   The loop ends: e - q decreases. *)
Lemma unmark_loop_correct: forall (m m1: mem) (S: Shape) (bm: block) (N: nat)
  (lss: list (list Lit)) (i: nat) (le: temp_env),
  NoDup (iblocks S bm) -> Z.of_nat N < 268435456 -> Z.of_nat (nclits S) < 1073741824 ->
  (starts S i <= starts S (Datatypes.S i) <= nclits S)%nat ->
  nth i lss [] = span S (starts S i) (starts S (Datatypes.S i)) ->
  (forall (q: nat), (q < nclits S)%nat -> key (lits S q) < 1073741824) ->
  AtomsBelow N (nth i lss []) -> NoDup (nth i lss []) ->
  UnmarkInv m S bm N lss i (starts S i) le m1 ->
  Exec ge le m1 unmark_loop (fun (le': temp_env) (m': mem) (out: outcome) =>
    out = Out_normal /\ ClearedAll m S bm N lss i le' m').
Proof.
  intros m m1 S bm N lss i le Hnd HN Hncl Hrange Hclause Hkeys Hat Hndc HI0.
  unfold unmark_loop, clause_part, clauses_loop, f_check_clauses.
  cbn [fn_body drop_stmts first_stmt loop_body]. unfold Swhile.
  apply exec_loop with (R := clause_variant S i) (I := UnmarkInv m S bm N lss i)
    (a := starts S i).
  - apply well_founded_ltof.
  - intros q le3 m3 HI. destruct HI as [Hs3 Hn3 Hi3 He3 Hq3 Hqr HM3 (tm3 & Am3 & Hm3)].
    pose proof HM3 as HM3'. destruct HM3' as [Fnv3 Fncl3 Fcs3 Fcl3 Fm3 As3 Al3 Hun3].
    apply exec_seq.
    (* if (q < e) ... else break; *)
    eapply (exec_if_cmp _ _ _ Clt).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + unfold Small. lia.
    + unfold Small. lia.
    + destruct (Nat.lt_ge_cases q (starts S (Datatypes.S i))) as [Hqlt | Hqge].
      * (* q < e: s->mrk[s->clits[q]] = 0; q++; *)
        replace (zcmp Clt (Z.of_nat q) (Z.of_nat (starts S (Datatypes.S i)))) with true
          by (symmetry; cbn [zcmp]; apply Z.ltb_lt; lia).
        assert (Hin: In (lits S q) (nth i lss [])).
        { rewrite Hclause. unfold span. apply in_map, in_seq. lia. }
        assert (Hky: (lit_key (lits S q) < 2 * N)%nat).
        { apply lit_key_lt. apply Hat. assumption. }
        assert (Hqn: (q < nclits S)%nat) by lia.
        pose proof (Hkeys q Hqn) as Hkq.
        assert (Haddq: Int.add (Int.repr (Z.of_nat q)) (Int.repr 1)
                       = Int.repr (Z.of_nat (Datatypes.S q))).
        { rewrite add_repr by lia. f_equal. lia. }
        (* The literal at q is not in the rest of the clause. *)
        assert (Hnd3: NoDup (span S q (starts S (Datatypes.S i)))).
        { apply (span_nodup_tail S (starts S i)).
          - lia.
          - rewrite <- Hclause. assumption. }
        rewrite span_cons in Hnd3 by lia.
        cbv beta iota. run. eapply exec_store.
        -- evl.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- ofs. bound.
        -- ofs. cbn [cast_int_int].
           destruct (arr_storable m3 bm (2 * N) (lit_key (lits S q)) tm3 0 Am3 Hky)
             as [m4 Hst].
           exists m4. split.
           ++ apply Hst.
           ++ normal. run. ints. apply loopk_next with (Datatypes.S q).
              ** unfold clause_variant, ltof. lia.
              ** constructor.
                 --- tmp.
                 --- tmp.
                 --- tmp.
                 --- tmp.
                 --- tmp.
                 --- lia.
                 --- apply (clause_mem_store m m3 m4 S bm N lss _ _ Hnd HM3 Hst).
                 --- eexists. split.
                     +++ apply (arr_store m3 m4 bm (2 * N) _ tm3 0 Am3 Hky Hst).
                     +++ apply marks_remove.
                         *** rewrite <- span_cons by lia. assumption.
                         *** inversion Hnd3. assumption.
      * (* q >= e: break; nothing is marked *)
        replace (zcmp Clt (Z.of_nat q) (Z.of_nat (starts S (Datatypes.S i)))) with false
          by (symmetry; cbn [zcmp]; apply Z.ltb_ge; lia).
        cbv beta iota. apply exec_break. abrupt. apply loopk_break.
        unfold span in Hm3.
        replace (starts S (Datatypes.S i) - q)%nat with 0%nat in Hm3 by lia.
        cbn [seq map] in Hm3. split.
        -- reflexivity.
        -- constructor.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ assumption.
           ++ exists tm3. split; assumption.
  - assumption.
Qed.

(* check_clauses marks the literals of each clause in turn, rejecting a literal out of
   range or marked already (a duplicate), and then unmarks them again:

     {{ the fields and arrays of the clauses and the marks are in m, nothing is marked }}
       int n = 2 * s->nv;
       int i = 0;
     {{ ClausesInv 0 }}
       while (i < s->ncl) {
     {{ ClausesInv i /\ i < ncl }}
         int b = s->cstart[i];
         int e = s->cstart[i + 1];
         int q = b;
     {{ MarkInv i b }}
         while (q < e) {
     {{ MarkInv i q /\ q < e }}
           int y = s->clits[q];
           if (y < 0) return 0;
           if (y >= n) return 0;
           if (s->mrk[y] != 0) return 0;
     {{ result = 0 (rejected) }}
     {{ MarkInv i q /\ y is a literal with atom below N, not marked }}
           s->mrk[y] = 1;
           q++;
     {{ MarkInv i (q + 1) }}
         }
     {{ MarkedAll i }}
         q = b;
     {{ UnmarkInv i b }}
         while (q < e) {
           s->mrk[s->clits[q]] = 0;
           q++;
     {{ UnmarkInv i (q + 1) }}
         }
     {{ ClearedAll i }}
         i++;
     {{ ClausesInv (i + 1) }}
       }
     {{ ClausesInv ncl }}
       return 1;
     {{ result = 1 /\ every clause has atoms below N and no literal twice }}

   The loops end: length lss - i and starts S (i + 1) - q decrease. *)
Lemma check_clauses_correct: forall (S: Shape) (bm: block) (N: nat)
  (lss: list (list Lit)) (tm: nat -> Z),
  {{ m | NoDup (iblocks S bm) /\
         Fld m (b_s S) 0 Mint32 (vint (Z.of_nat N)) /\
         Fld m (b_s S) 4 Mint32 (vint (Z.of_nat (length lss))) /\
         Fld m (b_s S) 8 Mptr (Vptr (b_cstart S) Ptrofs.zero) /\
         Fld m (b_s S) 16 Mptr (Vptr (b_clits S) Ptrofs.zero) /\
         Fld m (b_s S) 152 Mptr (Vptr bm Ptrofs.zero) /\
         Arr m (b_cstart S) (Datatypes.S (length lss))
           (fun (i: nat) => Z.of_nat (starts S i)) /\
         Arr m (b_clits S) (nclits S) (fun (q: nat) => key (lits S q)) /\
         Arr m bm (2 * N) tm /\
         (forall (i: nat), (i < length lss)%nat ->
            (starts S i <= starts S (Datatypes.S i) <= nclits S)%nat /\
            nth i lss [] = span S (starts S i) (starts S (Datatypes.S i))) /\
         Z.of_nat N < 268435456 /\ Z.of_nat (nclits S) < 1073741824 /\
         Z.of_nat (length lss) < 1073741824 /\
         (forall (q: nat), (q < nclits S)%nat -> key (lits S q) < 1073741824) /\
         Marks N tm [] }}
    f_check_clauses(sptr S)
  {{ m', v | v = vint 0 \/
             (v = vint 1 /\
              (forall (i: nat) (l: Lit), (i < length lss)%nat -> In l (nth i lss []) ->
                 (extract l < N)%nat) /\
              (forall (i: nat), (i < length lss)%nat -> NoDup (nth i lss [])) /\
              (exists (tm': nat -> Z), Arr m' bm (2 * N) tm' /\ Marks N tm' []) /\
              Mem.unchanged_on (fun (b: block) (_: Z) => b <> bm) m m') }}.
Proof.
  intros S bm N lss tm m (Hnd & Fnv & Fncl & Fcstart & Fclits & Fmrk & Astarts & Alits
    & Amrk & Hclauses & HN & Hncl & Hlss & Hkeys & Hm0).
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
      (I := ClausesInv m S bm N lss) (a := 0%nat).
    + apply well_founded_ltof.
    + intros i le1 m1 HI. destruct HI as [Hs Hn Hi Hile Hat Hnd' HM1 (tm1 & Am1 & Hm1)].
      pose proof HM1 as HM1'. destruct HM1' as [Fnv1 Fncl1 Fcs1 Fcl1 Fm1 As1 Al1 Hun1].
      clear Fnv Fncl Fcstart Fclits Fmrk Astarts Alits Amrk.
      (* if (i < s->ncl) ... else break; *)
      run. eapply (exec_if_cmp _ _ _ Clt).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * destruct (Nat.lt_ge_cases i (length lss)) as [Hlt | Hge].
        -- (* i < ncl: int b = s->cstart[i]; int e = s->cstart[i + 1]; int q = b; *)
           replace (zcmp Clt (Z.of_nat i) (Z.of_nat (length lss))) with true
             by (symmetry; cbn [zcmp]; apply Z.ltb_lt; lia).
           destruct (Hclauses i Hlt) as [Hrange Hclause].
           assert (Hadd: Int.add (Int.repr (Z.of_nat i)) (Int.repr 1)
                         = Int.repr (Z.of_nat (Datatypes.S i))).
           { rewrite add_repr by lia. f_equal. lia. }
           cbv beta iota. run.
           (* The marking loop: all of clause i marked, or a return of 0. *)
           apply exec_weaken with (Q := MarkPost m S bm N lss i).
           ++ apply (mark_loop_correct m m1 S bm N lss i).
              ** assumption.
              ** assumption.
              ** assumption.
              ** assumption.
              ** assumption.
              ** assumption.
              ** (* The marking invariant holds at q = b, with nothing marked. *)
                 constructor.
                 --- tmp.
                 --- tmp.
                 --- tmp.
                 --- tmp.
                 --- tmp.
                 --- tmp.
                 --- lia.
                 --- unfold span. rewrite Nat.sub_diag. intros l [].
                 --- unfold span. rewrite Nat.sub_diag. constructor.
                 --- assumption.
                 --- exists tm1. split.
                     +++ assumption.
                     +++ unfold span. rewrite Nat.sub_diag. assumption.
           ++ intros le2 m2 out [[-> HA] | ->].
              ** (* all of clause i is marked: q = b; and the unmarking loop *)
                 destruct HA as [Hs2 Hn2 Hi2 Hb2 He2 Hat2 Hnd2 HM2 (tm2 & Am2 & Hm2)].
                 clear Fnv1 Fncl1 Fcs1 Fcl1 Fm1 As1 Al1 Am1. normal. run.
                 apply exec_weaken
                   with (Q := fun (le: temp_env) (m3: mem) (out: outcome) =>
                                out = Out_normal /\ ClearedAll m S bm N lss i le m3).
                 --- apply (unmark_loop_correct m m2 S bm N lss i).
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ (* The unmarking invariant holds at q = b. *)
                         constructor.
                         *** tmp.
                         *** tmp.
                         *** tmp.
                         *** tmp.
                         *** tmp.
                         *** lia.
                         *** assumption.
                         *** exists tm2. split.
                             ---- assumption.
                             ---- rewrite <- Hclause. assumption.
                 --- (* nothing is marked: i++; and the invariant holds for i + 1 *)
                     intros le3 m3 out (-> & HC). destruct HC as [Hs3 Hn3 Hi3 HM3 HMk3].
                     normal. run. ints. apply loopk_next with (Datatypes.S i).
                     +++ unfold ltof. lia.
                     +++ constructor.
                         *** tmp.
                         *** tmp.
                         *** tmp.
                         *** lia.
                         *** intros i' Hi' l Hl.
                             destruct (Nat.eq_dec i' i) as [-> | Hne].
                             ---- apply Hat2. assumption.
                             ---- apply (Hat i').
                                  ++++ lia.
                                  ++++ assumption.
                         *** intros i' Hi'. destruct (Nat.eq_dec i' i) as [-> | Hne].
                             ---- assumption.
                             ---- apply Hnd'. lia.
                         *** assumption.
                         *** assumption.
              ** (* return 0 from the marking loop *)
                 ret. exists (vint 0). split.
                 --- apply result_int.
                 --- now left.
        -- (* i >= ncl: break; return 1; every clause is checked *)
           replace (zcmp Clt (Z.of_nat i) (Z.of_nat (length lss))) with false
             by (symmetry; cbn [zcmp]; apply Z.ltb_ge; lia).
           cbv beta iota. apply exec_break. abrupt. apply loopk_break. normal.
           eapply exec_return.
           ++ ev.
           ++ exists (vint 1). split.
              ** apply result_int.
              ** right. split.
                 --- reflexivity.
                 --- split.
                     +++ intros i' l Hi' Hl. apply (Hat i').
                         *** lia.
                         *** assumption.
                     +++ split.
                         *** intros i' Hi'. apply Hnd'. lia.
                         *** split.
                             ---- exists tm1. split; assumption.
                             ---- assumption.
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
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- apply Mem.unchanged_on_refl.
      * exists tm. split; assumption.
Qed.

Lemma check_clauses_fun: exists (b: block),
  Genv.find_symbol ge _check_clauses = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_check_clauses).
Proof. apply find_fun. reflexivity. Qed.
