(* check_lits checks the literals to decide on that the caller put in alls: they are the
   literals of the clauses, each once, in any order. *)
From Stdlib Require Import List Bool.
From Stdlib Require Finite.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep CheckClauses.
Import ListNotations.

Section Lists.
  (* Distinct literals with atoms below N are at most 2 N. *)
  Lemma keys_bound: forall (acc: list Lit) (N: nat),
    NoDup acc -> (forall (l: Lit), In l acc -> (extract l < N)%nat) ->
    (length acc <= 2 * N)%nat.
  Proof.
    intros acc N Hnodup Hacc. rewrite <- (length_map lit_key acc).
    rewrite <- (length_seq (2 * N) 0). apply NoDup_incl_length.
    - apply Finite.Injective_map_NoDup.
      + intros a b. apply lit_key_inj.
      + assumption.
    - intros k Hk. apply in_map_iff in Hk as [l [<- Hl]]. apply Hacc in Hl. apply in_seq.
      destruct l; simpl in *; lia.
  Qed.

  (* The literals of the first k entries of the table ta of keys. *)
  Definition decoded (ta: nat -> Z) (k: nat): list Lit :=
    map (fun (j: nat) => lit_of (ta j)) (seq 0 k).

  Lemma decoded_snoc: forall (ta: nat -> Z) (k: nat),
    decoded ta (Datatypes.S k) = decoded ta k ++ [lit_of (ta k)].
  Proof. intros ta k. unfold decoded. rewrite seq_S, map_app. reflexivity. Qed.

  Lemma decoded_length: forall (ta: nat -> Z) (k: nat), length (decoded ta k) = k.
  Proof. intros ta k. unfold decoded. rewrite length_map, length_seq. reflexivity. Qed.

  Lemma decoded_nth: forall (ta: nat -> Z) (k j: nat), (j < k)%nat ->
    nth j (decoded ta k) (Pos 0%nat) = lit_of (ta j).
  Proof.
    intros ta k j Hj. unfold decoded.
    pose proof (map_nth (fun (i: nat) => lit_of (ta i)) (seq 0 k) 0%nat j) as Hmap.
    cbv beta in Hmap. rewrite (nth_indep _ (Pos 0%nat) (lit_of (ta 0%nat))).
    - rewrite Hmap, seq_nth by assumption. reflexivity.
    - rewrite length_map, length_seq. assumption.
  Qed.

  (* The clause literals: those at the positions below nclits S. *)
  Lemma in_clause_lits: forall (S: Shape) (l: Lit),
    In l (span S 0 (nclits S)) <-> exists (q: nat), (q < nclits S)%nat /\ lits S q = l.
  Proof.
    intros S l. unfold span. rewrite in_map_iff. split.
    - intros [q [<- Hq]]. apply in_seq in Hq. exists q. split.
      + lia.
      + reflexivity.
    - intros [q [Hq <-]]. exists q. split.
      + reflexivity.
      + apply in_seq. lia.
  Qed.

  (* The clause literals that are not among done: those still marked. *)
  Definition remaining (S: Shape) (done: list Lit): list Lit :=
    filter (fun (l: Lit) =>
              negb (existsb (fun (y: Lit) => Nat.eqb (lit_key y) (lit_key l)) done))
      (span S 0 (nclits S)).

  Lemma in_remaining: forall (S: Shape) (done: list Lit) (l: Lit),
    In l (remaining S done) <-> In l (span S 0 (nclits S)) /\ ~ In l done.
  Proof.
    intros S done l. unfold remaining. rewrite filter_In, negb_true_iff. split.
    - intros [Hl Hex]. split.
      + assumption.
      + intros Hin. apply existsb_key in Hin. congruence.
    - intros [Hl Hnot]. split.
      + assumption.
      + apply not_true_iff_false. intros Hex. apply existsb_key in Hex. contradiction.
  Qed.

  Lemma remaining_nil: forall (S: Shape), remaining S [] = span S 0 (nclits S).
  Proof.
    intros S. unfold remaining. induction (span S 0 (nclits S)) as [|l ls IH].
    - reflexivity.
    - simpl. f_equal. apply IH.
  Qed.

  (* Unmarking y, which is still marked, moves it to done. *)
  Lemma marks_unmark: forall (S: Shape) (N: nat) (tm: nat -> Z) (done: list Lit)
    (y: Lit),
    Marks N tm (remaining S done) ->
    Marks N (fun (j: nat) => if Nat.eqb (lit_key y) j then 0 else tm j)
      (remaining S (done ++ [y])).
  Proof.
    intros S N tm done y Hm k Hk. destruct (Nat.eqb_spec (lit_key y) k) as [<- | Hne].
    - (* y is not marked any more *)
      destruct (existsb _ (remaining S (done ++ [y]))) eqn:Hex.
      + apply existsb_key in Hex. apply in_remaining in Hex as [_ Hnot].
        exfalso. apply Hnot. apply in_or_app. right. left. reflexivity.
      + reflexivity.
    - (* the other literals are marked as before *)
      rewrite (Hm k Hk).
      assert (Hiff: existsb (fun (l: Lit) => Nat.eqb (lit_key l) k)
                      (remaining S done) = true
                    <-> existsb (fun (l: Lit) => Nat.eqb (lit_key l) k)
                          (remaining S (done ++ [y])) = true).
      { rewrite !existsb_exists. split.
        - intros [l [Hl Hlk]]. exists l. split.
          + apply in_remaining in Hl as [Hl Hnot]. apply in_remaining. split.
            * assumption.
            * intros Hin. apply in_app_or in Hin as [Hin | [<- | []]].
              -- contradiction.
              -- apply Nat.eqb_eq in Hlk. contradiction.
          + assumption.
        - intros [l [Hl Hlk]]. exists l. split.
          + apply in_remaining in Hl as [Hl Hnot]. apply in_remaining. split.
            * assumption.
            * intros Hin. apply Hnot. apply in_or_app. left. assumption.
          + assumption. }
      destruct (existsb _ (remaining S done)), (existsb _ (remaining S (done ++ [y]))).
      + reflexivity.
      + exfalso. assert (Htrue: false = true) by (apply Hiff; reflexivity). discriminate.
      + exfalso. assert (Htrue: false = true) by (apply Hiff; reflexivity). discriminate.
      + reflexivity.
  Qed.
End Lists.

(* What check_lits needs: the fields and arrays it reads, the caller's literals in alls,
   small ints as it compares them, and no marks. *)
Record LitsPre (m: mem) (S: Shape) (bm: block) (N: nat) (lss: list (list Lit)) (zl: Z)
  (ta tm: nat -> Z): Prop := {
  lp_nodup: NoDup (iblocks S bm);
  lp_nv: Fld m (b_s S) 0 Mint32 (vint (Z.of_nat N));
  lp_ncl: Fld m (b_s S) 4 Mint32 (vint (Z.of_nat (length lss)));
  lp_cstart: Fld m (b_s S) 8 Mptr (Vptr (b_cstart S) Ptrofs.zero);
  lp_clits: Fld m (b_s S) 16 Mptr (Vptr (b_clits S) Ptrofs.zero);
  lp_alls: Fld m (b_s S) 104 Mptr (Vptr (b_alls S) Ptrofs.zero);
  lp_nlits: Fld m (b_s S) 112 Mint32 (vint zl);
  lp_mrk: Fld m (b_s S) 152 Mptr (Vptr bm Ptrofs.zero);
  lp_starts: Arr m (b_cstart S) (Datatypes.S (length lss))
    (fun (i: nat) => Z.of_nat (starts S i));
  lp_lits: Arr m (b_clits S) (nclits S) (fun (q: nat) => key (lits S q));
  lp_aalls: Arr m (b_alls S) (2 * N) ta;
  lp_amrk: Arr m bm (2 * N) tm;
  lp_marks: Marks N tm [];
  lp_small: Small zl;
  lp_small_alls: forall (k: nat), (k < 2 * N)%nat -> Small (ta k);
  lp_end: starts S (length lss) = nclits S;
  lp_atoms: forall (q: nat), (q < nclits S)%nat -> (extract (lits S q) < N)%nat;
  lp_n: Z.of_nat N < 268435456;
  lp_nclits: Z.of_nat (nclits S) < 1073741824;
  lp_lss: Z.of_nat (length lss) < 1073741824;
}.

(* check_lits returns 0, having changed only the marks. *)
Definition LitsReject (m: mem) (bm: block) (N: nat) (m': mem) (out: outcome): Prop :=
  out = Out_return (Some (vint 0, Ctypesdefs.tint)) /\
  (exists (tm': nat -> Z), Arr m' bm (2 * N) tm') /\
  Mem.unchanged_on (fun (b: block) (_: Z) => b <> bm) m m'.

Lemma lits_reject: forall (m m1: mem) (S: Shape) (bm: block) (N: nat)
  (lss: list (list Lit)) (tm: nat -> Z),
  ClauseMem m S bm N lss m1 -> Arr m1 bm (2 * N) tm ->
  LitsReject m bm N m1 (Out_return (Some (vint 0, Ctypesdefs.tint))).
Proof.
  intros m m1 S bm N lss tm HM Am. split.
  - reflexivity.
  - split.
    + exists tm. assumption.
    + apply (cm_frame _ _ _ _ _ _ HM).
Qed.

(* The field and the array alls are as in the memory m of the call. *)
Lemma alls_kept: forall (m m1: mem) (S: Shape) (bm: block) (N: nat)
  (lss: list (list Lit)) (ta: nat -> Z),
  NoDup (iblocks S bm) -> ClauseMem m S bm N lss m1 ->
  Fld m (b_s S) 104 Mptr (Vptr (b_alls S) Ptrofs.zero) -> Arr m (b_alls S) (2 * N) ta ->
  Fld m1 (b_s S) 104 Mptr (Vptr (b_alls S) Ptrofs.zero) /\ Arr m1 (b_alls S) (2 * N) ta.
Proof.
  intros m m1 S bm N lss ta Hnd HM Fal Aal. pose proof (cm_frame _ _ _ _ _ _ HM) as Hun.
  unfold iblocks in Hnd. split.
  - apply (fld_unchanged _ m m1 _ _ _ _ Hun).
    + intros i _. cbv beta. neq Hnd.
    + assumption.
  - apply (arr_unchanged _ m m1 _ _ _ Hun).
    + intros ofs. cbv beta. neq Hnd.
    + assumption.
Qed.

(* The three loops of check_lits. *)
Definition lits_mark: statement := first_stmt (drop_stmts 6 (fn_body f_check_lits)).
Definition lits_list: statement := first_stmt (drop_stmts 8 (fn_body f_check_lits)).
Definition lits_cover: statement := first_stmt (drop_stmts 10 (fn_body f_check_lits)).

(* The invariant of the marking loop at q: the clause literals before q are marked. *)
Record MarkLitsInv (m: mem) (S: Shape) (bm: block) (N: nat) (lss: list (list Lit))
  (nz q: nat) (le: temp_env) (m1: mem): Prop := {
  mk_s: le ! _s = Some (sptr S);
  mk_n: le ! _n = Some (vint (Z.of_nat (2 * N)));
  mk_nl: le ! _nl = Some (vint (Z.of_nat nz));
  mk_e: le ! _e = Some (vint (Z.of_nat (nclits S)));
  mk_q: le ! _q = Some (vint (Z.of_nat q));
  mk_le: (q <= nclits S)%nat;
  mk_mem: ClauseMem m S bm N lss m1;
  mk_marks: exists (tm: nat -> Z), Arr m1 bm (2 * N) tm /\ Marks N tm (span S 0 q);
}.

(* The marking loop, over the clause literals:

     {{ MarkLitsInv 0 }}
       while (q < e) {
         s->mrk[s->clits[q]] = 1;                                         (marks_add)
         q++;
       }
     {{ MarkLitsInv e: every clause literal is marked }}

   The loop ends: nclits S - q decreases. *)
Lemma lits_mark_correct: forall (m m1: mem) (S: Shape) (bm: block) (N: nat)
  (lss: list (list Lit)) (nz: nat) (le: temp_env),
  NoDup (iblocks S bm) -> Z.of_nat N < 268435456 -> Z.of_nat (nclits S) < 1073741824 ->
  (forall (q: nat), (q < nclits S)%nat -> (extract (lits S q) < N)%nat) ->
  MarkLitsInv m S bm N lss nz 0 le m1 ->
  Exec ge le m1 lits_mark
    (fun (le': temp_env) (m': mem) (out: outcome) =>
       out = Out_normal /\ MarkLitsInv m S bm N lss nz (nclits S) le' m').
Proof.
  intros m m1 S bm N lss nz le Hnd HN Hncl Hat HI0.
  unfold lits_mark, f_check_lits. cbn [fn_body drop_stmts first_stmt]. unfold Swhile.
  apply exec_loop with (R := ltof nat (fun (q: nat) => nclits S - q)%nat)
    (I := MarkLitsInv m S bm N lss nz) (a := 0%nat).
  - apply well_founded_ltof.
  - intros q le2 m2 HI.
    destruct HI as [Hs Hn Hnl He Hq Hqle HM (tm & Am & Hm)].
    pose proof HM as [Fnv Fncl Fcs Fcl Fm As Al Hun].
    (* while (q < e) *)
    apply exec_seq. eapply (exec_if_cmp _ _ _ Clt).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + unfold Small. lia.
    + unfold Small. lia.
    + destruct (Nat.lt_ge_cases q (nclits S)) as [Hlt | Hge].
      * (* s->mrk[s->clits[q]] = 1; q++; *)
        replace (zcmp Clt (Z.of_nat q) (Z.of_nat (nclits S))) with true
          by (symmetry; cbn [zcmp]; apply Z.ltb_lt; lia).
        pose proof (Hat q Hlt) as Hy.
        assert (Hky: (lit_key (lits S q) < 2 * N)%nat) by (apply lit_key_lt; assumption).
        assert (Hadd: Int.add (Int.repr (Z.of_nat q)) (Int.repr 1)
                      = Int.repr (Z.of_nat (Datatypes.S q))).
        { apply incr_nat. lia. }
        cbv beta iota. apply exec_skip. normal. run. eapply exec_store.
        -- evl.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- ofs. bound.
        -- ofs. cbn [cast_int_int].
           destruct (arr_storable m2 bm (2 * N) (lit_key (lits S q)) tm 1 Am Hky)
             as [m3 Hst].
           exists m3. split.
           ++ apply Hst.
           ++ normal. run. ints. apply loopk_next with (Datatypes.S q).
              ** unfold ltof. lia.
              ** constructor.
                 --- tmp.
                 --- tmp.
                 --- tmp.
                 --- tmp.
                 --- tmp.
                 --- lia.
                 --- apply (clause_mem_store m m2 m3 S bm N lss _ _ Hnd HM Hst).
                 --- eexists. split.
                     +++ apply (arr_store m2 m3 bm (2 * N) _ tm 1 Am Hky Hst).
                     +++ rewrite span_snoc by lia. apply marks_add. assumption.
      * (* q >= e: break *)
        replace (zcmp Clt (Z.of_nat q) (Z.of_nat (nclits S))) with false
          by (symmetry; cbn [zcmp]; apply Z.ltb_ge; lia).
        cbv beta iota. apply exec_break. abrupt. apply loopk_break. split.
        -- reflexivity.
        -- replace (nclits S) with q by lia. constructor.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ replace q with (nclits S) by lia. tmp.
           ++ tmp.
           ++ lia.
           ++ assumption.
           ++ exists tm. split.
              ** assumption.
              ** assumption.
  - assumption.
Qed.

(* The invariant of the loop over alls at k: the first k entries of alls are distinct
   clause literals, done, and the marked literals are the other clause literals. *)
Record ListInv (m: mem) (S: Shape) (bm: block) (N: nat) (lss: list (list Lit))
  (ta: nat -> Z) (nz k: nat) (le: temp_env) (m1: mem): Prop := {
  li_s: le ! _s = Some (sptr S);
  li_n: le ! _n = Some (vint (Z.of_nat (2 * N)));
  li_nl: le ! _nl = Some (vint (Z.of_nat nz));
  li_e: le ! _e = Some (vint (Z.of_nat (nclits S)));
  li_k: le ! _k = Some (vint (Z.of_nat k));
  li_le: (k <= nz)%nat;
  li_keys: forall (j: nat), (j < k)%nat -> 0 <= ta j;
  li_nodup: NoDup (decoded ta k);
  li_in: forall (l: Lit), In l (decoded ta k) -> In l (span S 0 (nclits S));
  li_mem: ClauseMem m S bm N lss m1;
  li_marks: exists (tm: nat -> Z), Arr m1 bm (2 * N) tm /\
    Marks N tm (remaining S (decoded ta k));
}.

(* The variant, the end and the rest of the body after its range checks of the loop over
   alls. *)
Definition list_variant (nz: nat): nat -> nat -> Prop :=
  ltof nat (fun (k: nat) => nz - k)%nat.

Definition ListPost (m: mem) (S: Shape) (bm: block) (N: nat) (lss: list (list Lit))
  (ta: nat -> Z) (nz: nat) (le': temp_env) (m': mem) (out: outcome): Prop :=
  (out = Out_normal /\ ListInv m S bm N lss ta nz nz le' m') \/ LitsReject m bm N m' out.

Definition lits_take: statement := drop_stmts 3 (drop_stmts 1 (loop_body lits_list)).

(* The literal y' = lit_of (alls[k]) of the loop over alls, whose key y is below 2 N; le
   has the temporaries of ListInv, and y and t'8 that the body set:

     {{ ListInv k /\ y = key y' }}
       if (s->mrk[y] == 0) return 0;
     {{ result = 0: y' is not of a clause, or there twice }}
       s->mrk[y] = 0;                                                 (marks_unmark)
       k++;
     {{ ListInv (k + 1) }}                                                           *)
Lemma lits_take_correct: forall (m m2: mem) (S: Shape) (bm: block) (N: nat)
  (lss: list (list Lit)) (ta: nat -> Z) (nz k: nat) (le2 le: temp_env),
  NoDup (iblocks S bm) -> Z.of_nat N < 268435456 -> (nz <= 2 * N)%nat ->
  ListInv m S bm N lss ta nz k le2 m2 -> (k < nz)%nat -> 0 <= ta k < Z.of_nat (2 * N) ->
  le = PTree.set _y (vint (ta k)) (PTree.set _t'8 (Vptr (b_alls S) Ptrofs.zero) le2) ->
  Exec ge le m2 lits_take
    (LoopK (list_variant nz) (ListInv m S bm N lss ta nz)
       (ListPost m S bm N lss ta nz) k).
Proof.
  intros m m2 S bm N lss ta nz k le2 le Hnd HN Hnz HI Hlt Hrange ->.
  destruct HI as [Hs Hn Hnl He Hk Hkle Hkeys Hndk Hin HM (tm & Am & Hm)].
  pose proof HM as [Fnv Fncl Fcs Fcl Fm As Al Hun].
  (* y is the key of the literal y' *)
  remember (lit_of (ta k)) as y' eqn:Hy'.
  assert (Hkey: ta k = key y').
  { rewrite Hy'. symmetry. apply key_lit_of. lia. }
  assert (Hky: (lit_key y' < 2 * N)%nat) by (unfold key in Hkey; lia).
  unfold lits_take, lits_list, f_check_lits.
  cbn [fn_body drop_stmts first_stmt loop_body Swhile].
  rewrite Hkey. run. rewrite (Hm _ Hky).
  (* if (s->mrk[y] == 0) return 0; *)
  eapply (exec_if_cmp _ _ _ Ceq _ _ _ 0).
  - ev.
  - ev.
  - reflexivity.
  - reflexivity.
  - unfold Small. destruct (existsb _ _); lia.
  - unfold Small. lia.
  - destruct (existsb (fun (l: Lit) => Nat.eqb (lit_key l) (lit_key y'))
                (remaining S (decoded ta k))) eqn:Hex.
    + (* y' is marked: s->mrk[y] = 0; k++; *)
      change (zcmp Ceq 1 0) with false. cbv beta iota. apply exec_skip. normal.
      apply existsb_key in Hex. apply in_remaining in Hex as [Hcl Hnew].
      assert (Hadd: Int.add (Int.repr (Z.of_nat k)) (Int.repr 1)
                    = Int.repr (Z.of_nat (Datatypes.S k))).
      { apply incr_nat. lia. }
      run. eapply exec_store.
      * evl.
      * ev.
      * reflexivity.
      * reflexivity.
      * ofs. bound.
      * ofs. cbn [cast_int_int].
        destruct (arr_storable m2 bm (2 * N) (lit_key y') tm 0 Am Hky) as [m3 Hst].
        exists m3. split.
        -- apply Hst.
        -- normal. run. ints. apply loopk_next with (Datatypes.S k).
           ++ unfold list_variant, ltof. lia.
           ++ constructor.
              ** tmp.
              ** tmp.
              ** tmp.
              ** tmp.
              ** tmp.
              ** lia.
              ** (* the key at k is not negative *)
                 intros j Hj. destruct (Nat.eq_dec j k) as [-> | Hne].
                 --- lia.
                 --- apply Hkeys. lia.
              ** (* y' was not done yet *)
                 rewrite decoded_snoc, <- Hy'. apply NoDup_app.
                 --- assumption.
                 --- constructor.
                     +++ easy.
                     +++ constructor.
                 --- intros l Hl [<- | []]. contradiction.
              ** (* y' is a clause literal *)
                 rewrite decoded_snoc, <- Hy'. intros l Hl.
                 apply in_app_or in Hl as [Hl | [<- | []]].
                 --- apply Hin. assumption.
                 --- assumption.
              ** apply (clause_mem_store m m2 m3 S bm N lss _ _ Hnd HM Hst).
              ** eexists. split.
                 --- apply (arr_store m2 m3 bm (2 * N) _ tm 0 Am Hky Hst).
                 --- rewrite decoded_snoc, <- Hy'. apply marks_unmark. assumption.
    + (* y' is not marked: not of a clause, or there twice *)
      change (zcmp Ceq 0 0) with true. cbv beta iota. eapply exec_return.
      * ev.
      * ret. right. apply (lits_reject m m2 S bm N lss tm HM Am).
Qed.

(* The loop over the caller's literals in alls:

     {{ ListInv 0 }}
       while (k < nl) {
         int y = s->alls[k];
         if (y < 0) return 0;
         if (y >= n) return 0;
         if (s->mrk[y] == 0) return 0;
     {{ result = 0: not a literal, not of a clause, or there twice }}
         s->mrk[y] = 0;                                               (marks_unmark)
         k++;
       }
     {{ ListInv nl }}

   The loop ends: nl - k decreases. *)
Lemma lits_list_correct: forall (m m1: mem) (S: Shape) (bm: block) (N: nat)
  (lss: list (list Lit)) (ta: nat -> Z) (nz: nat) (le: temp_env),
  NoDup (iblocks S bm) -> Z.of_nat N < 268435456 -> (nz <= 2 * N)%nat ->
  Fld m (b_s S) 104 Mptr (Vptr (b_alls S) Ptrofs.zero) -> Arr m (b_alls S) (2 * N) ta ->
  (forall (k: nat), (k < 2 * N)%nat -> Small (ta k)) ->
  ListInv m S bm N lss ta nz 0 le m1 ->
  Exec ge le m1 lits_list (ListPost m S bm N lss ta nz).
Proof.
  intros m m1 S bm N lss ta nz le Hnd HN Hnz Fal Aal Hsmall HI0.
  unfold lits_list, f_check_lits. cbn [fn_body drop_stmts first_stmt]. unfold Swhile.
  apply exec_loop with (R := list_variant nz) (I := ListInv m S bm N lss ta nz)
    (a := 0%nat).
  - apply well_founded_ltof.
  - intros k le2 m2 HI. pose proof HI as HI'.
    destruct HI' as [Hs Hn Hnl He Hk Hkle Hkeys Hndk Hin HM (tm & Am & Hm)].
    pose proof HM as [Fnv Fncl Fcs Fcl Fm As Al Hun].
    destruct (alls_kept m m2 S bm N lss ta Hnd HM Fal Aal) as [Fal2 Aal2].
    (* while (k < nl) *)
    apply exec_seq. eapply (exec_if_cmp _ _ _ Clt).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + unfold Small. lia.
    + unfold Small. lia.
    + destruct (Nat.lt_ge_cases k nz) as [Hlt | Hge].
      * replace (zcmp Clt (Z.of_nat k) (Z.of_nat nz)) with true
          by (symmetry; cbn [zcmp]; apply Z.ltb_lt; lia).
        cbv beta iota. apply exec_skip. normal.
        (* int y = s->alls[k]; *)
        run.
        (* if (y < 0) return 0; *)
        eapply (exec_if_cmp _ _ _ Clt _ _ (ta k) 0).
        -- ev.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- apply Hsmall. lia.
        -- unfold Small. lia.
        -- cbn [zcmp]. destruct (Z.ltb_spec (ta k) 0) as [Hneg | Hpos].
           ++ (* not a literal *)
              cbv beta iota. eapply exec_return.
              ** ev.
              ** ret. right. apply (lits_reject m m2 S bm N lss tm HM Am).
           ++ cbv beta iota. apply exec_skip. normal. apply exec_seq.
              (* if (y >= n) return 0; *)
              eapply (exec_if_cmp _ _ _ Cge _ _ (ta k) (Z.of_nat (2 * N))).
              ** ev.
              ** ev.
              ** reflexivity.
              ** reflexivity.
              ** apply Hsmall. lia.
              ** unfold Small. lia.
              ** cbn [zcmp].
                 destruct (Z.leb_spec (Z.of_nat (2 * N)) (ta k)) as [Hbig | Hsm].
                 --- (* an atom not below N *)
                     cbv beta iota. eapply exec_return.
                     +++ ev.
                     +++ ret. right. apply (lits_reject m m2 S bm N lss tm HM Am).
                 --- (* the rest of the body, for the literal y' with key y *)
                     cbv beta iota. apply exec_skip. normal.
                     apply (lits_take_correct m m2 S bm N lss ta nz k le2).
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ lia.
                     +++ reflexivity.
      * (* k >= nl: break *)
        replace (zcmp Clt (Z.of_nat k) (Z.of_nat nz)) with false
          by (symmetry; cbn [zcmp]; apply Z.ltb_ge; lia).
        cbv beta iota. apply exec_break. abrupt. apply loopk_break. left. split.
        -- reflexivity.
        -- replace k with nz in * by lia. constructor.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ lia.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ exists tm. split.
              ** assumption.
              ** assumption.
  - assumption.
Qed.

(* The invariant of the last loop at q: the clause literals before q are among the nz
   literals of alls. *)
Record CoverInv (m: mem) (S: Shape) (bm: block) (N: nat) (lss: list (list Lit))
  (ta: nat -> Z) (nz q: nat) (le: temp_env) (m1: mem): Prop := {
  cv_s: le ! _s = Some (sptr S);
  cv_e: le ! _e = Some (vint (Z.of_nat (nclits S)));
  cv_q: le ! _q = Some (vint (Z.of_nat q));
  cv_le: (q <= nclits S)%nat;
  cv_cover: forall (q': nat), (q' < q)%nat -> In (lits S q') (decoded ta nz);
  cv_mem: ClauseMem m S bm N lss m1;
  cv_marks: exists (tm: nat -> Z), Arr m1 bm (2 * N) tm /\
    Marks N tm (remaining S (decoded ta nz));
}.

(* The last loop, over the clause literals again:

     {{ CoverInv 0 }}
       while (q < e) {
         if (s->mrk[s->clits[q]] != 0) return 0;
     {{ result = 0: a clause literal is not in alls }}
         q++;
       }
     {{ CoverInv e: every clause literal is in alls }}

   The loop ends: nclits S - q decreases. *)
Lemma lits_cover_correct: forall (m m1: mem) (S: Shape) (bm: block) (N: nat)
  (lss: list (list Lit)) (ta: nat -> Z) (nz: nat) (le: temp_env),
  Z.of_nat N < 268435456 -> Z.of_nat (nclits S) < 1073741824 ->
  (forall (q: nat), (q < nclits S)%nat -> (extract (lits S q) < N)%nat) ->
  CoverInv m S bm N lss ta nz 0 le m1 ->
  Exec ge le m1 lits_cover
    (fun (le': temp_env) (m': mem) (out: outcome) =>
       (out = Out_normal /\ CoverInv m S bm N lss ta nz (nclits S) le' m') \/
       LitsReject m bm N m' out).
Proof.
  intros m m1 S bm N lss ta nz le HN Hncl Hat HI0.
  unfold lits_cover, f_check_lits. cbn [fn_body drop_stmts first_stmt]. unfold Swhile.
  apply exec_loop with (R := ltof nat (fun (q: nat) => nclits S - q)%nat)
    (I := CoverInv m S bm N lss ta nz) (a := 0%nat).
  - apply well_founded_ltof.
  - intros q le2 m2 HI.
    destruct HI as [Hs He Hq Hqle Hcover HM (tm & Am & Hm)].
    pose proof HM as [Fnv Fncl Fcs Fcl Fm As Al Hun].
    (* while (q < e) *)
    apply exec_seq. eapply (exec_if_cmp _ _ _ Clt).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + unfold Small. lia.
    + unfold Small. lia.
    + destruct (Nat.lt_ge_cases q (nclits S)) as [Hlt | Hge].
      * replace (zcmp Clt (Z.of_nat q) (Z.of_nat (nclits S))) with true
          by (symmetry; cbn [zcmp]; apply Z.ltb_lt; lia).
        pose proof (Hat q Hlt) as Hy.
        assert (Hky: (lit_key (lits S q) < 2 * N)%nat) by (apply lit_key_lt; assumption).
        cbv beta iota. apply exec_skip. normal.
        (* if (s->mrk[s->clits[q]] != 0) return 0; *)
        run. rewrite (Hm _ Hky).
        eapply (exec_if_cmp _ _ _ Cne _ _ _ 0).
        -- ev.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- unfold Small. destruct (existsb _ _); lia.
        -- unfold Small. lia.
        -- destruct (existsb (fun (l: Lit) => Nat.eqb (lit_key l) (lit_key (lits S q)))
                       (remaining S (decoded ta nz))) eqn:Hex.
           ++ (* still marked: not in alls *)
              change (zcmp Cne 1 0) with true. cbv beta iota. eapply exec_return.
              ** ev.
              ** ret. right. apply (lits_reject m m2 S bm N lss tm HM Am).
           ++ (* not marked: in alls; q++ *)
              change (zcmp Cne 0 0) with false. cbv beta iota. apply exec_skip. normal.
              assert (Hadd: Int.add (Int.repr (Z.of_nat q)) (Int.repr 1)
                            = Int.repr (Z.of_nat (Datatypes.S q))).
              { apply incr_nat. lia. }
              run. ints. apply loopk_next with (Datatypes.S q).
              ** unfold ltof. lia.
              ** constructor.
                 --- tmp.
                 --- tmp.
                 --- tmp.
                 --- lia.
                 --- (* the literal at q is a clause literal that is not marked *)
                     intros q' Hq'. destruct (Nat.eq_dec q' q) as [-> | Hne].
                     +++ destruct (in_dec Lit.eq_dec (lits S q) (decoded ta nz))
                           as [Hdone | Hnot].
                         *** assumption.
                         *** exfalso.
                             assert (Hrem: In (lits S q) (remaining S (decoded ta nz))).
                             { apply in_remaining. split.
                               - apply in_clause_lits. exists q. split.
                                 + assumption.
                                 + reflexivity.
                               - assumption. }
                             apply existsb_key in Hrem. congruence.
                     +++ apply Hcover. lia.
                 --- assumption.
                 --- exists tm. split.
                     +++ assumption.
                     +++ assumption.
      * (* q >= e: break *)
        replace (zcmp Clt (Z.of_nat q) (Z.of_nat (nclits S))) with false
          by (symmetry; cbn [zcmp]; apply Z.ltb_ge; lia).
        cbv beta iota. apply exec_break. abrupt. apply loopk_break. left. split.
        -- reflexivity.
        -- replace q with (nclits S) in * by lia. constructor.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ lia.
           ++ assumption.
           ++ assumption.
           ++ exists tm. split.
              ** assumption.
              ** assumption.
  - assumption.
Qed.

(* What check_lits returns: 0, or 1 when the zl entries of alls (the table ta) are the
   clause literals acc, each once; only the marks change. *)
Definition LitsPost (m: mem) (S: Shape) (bm: block) (N: nat) (zl: Z) (ta: nat -> Z)
  (m': mem) (v: val): Prop :=
  (exists (tm': nat -> Z), Arr m' bm (2 * N) tm') /\
  Mem.unchanged_on (fun (b: block) (_: Z) => b <> bm) m m' /\
  (v = vint 0 \/
   (v = vint 1 /\ exists (acc: list Lit),
      zl = Z.of_nat (length acc) /\ NoDup acc /\ (length acc <= 2 * N)%nat /\
      (forall (l: Lit),
         In l acc <-> exists (q: nat), (q < nclits S)%nat /\ lits S q = l) /\
      forall (k: nat), (k < length acc)%nat -> ta k = key (nth k acc (Pos 0%nat)))).

(* Returning 0. *)
Lemma lits_post_reject: forall (m m': mem) (S: Shape) (bm: block) (N: nat) (zl: Z)
  (ta: nat -> Z),
  (exists (tm': nat -> Z), Arr m' bm (2 * N) tm') ->
  Mem.unchanged_on (fun (b: block) (_: Z) => b <> bm) m m' ->
  LitsPost m S bm N zl ta m' (vint 0).
Proof.
  intros m m' S bm N zl ta Hmk Hun. split.
  - assumption.
  - split.
    + assumption.
    + left. reflexivity.
Qed.

(* Returning 1 at the end: the nz literals of alls are the clause literals, each once. *)
Lemma lits_post_accept: forall (m m': mem) (S: Shape) (bm: block) (N: nat)
  (ta tm: nat -> Z) (nz: nat),
  Arr m' bm (2 * N) tm -> Mem.unchanged_on (fun (b: block) (_: Z) => b <> bm) m m' ->
  (nz <= 2 * N)%nat -> (forall (j: nat), (j < nz)%nat -> 0 <= ta j) ->
  NoDup (decoded ta nz) ->
  (forall (l: Lit), In l (decoded ta nz) -> In l (span S 0 (nclits S))) ->
  (forall (q: nat), (q < nclits S)%nat -> In (lits S q) (decoded ta nz)) ->
  LitsPost m S bm N (Z.of_nat nz) ta m' (vint 1).
Proof.
  intros m m' S bm N ta tm nz Am Hun Hnz Hkeys Hnd Hin Hcover. split.
  - exists tm. assumption.
  - split.
    + assumption.
    + right. split.
      * reflexivity.
      * exists (decoded ta nz). rewrite decoded_length. split.
        -- reflexivity.
        -- split.
           ++ assumption.
           ++ split.
              ** assumption.
              ** split.
                 --- (* in alls exactly when a clause literal *)
                     intros l. split.
                     +++ intros Hl. apply in_clause_lits. apply Hin. assumption.
                     +++ intros [q [Hq <-]]. apply Hcover. assumption.
                 --- (* alls holds their keys *)
                     intros k Hk. rewrite decoded_nth by assumption. symmetry.
                     apply key_lit_of. apply Hkeys. assumption.
Qed.

(* The facts of the memory of the call, for its loops. *)
Lemma lits_clause_mem: forall (m: mem) (S: Shape) (bm: block) (N: nat)
  (lss: list (list Lit)) (zl: Z) (ta tm: nat -> Z),
  LitsPre m S bm N lss zl ta tm -> ClauseMem m S bm N lss m.
Proof.
  intros m S bm N lss zl ta tm HP. destruct HP. constructor.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - apply Mem.unchanged_on_refl.
Qed.

(* The statements after the range checks: the three loops and return 1. *)
Definition lits_scan: statement := drop_stmts 5 (fn_body f_check_lits).

(* The three loops, once nl = nz is at most 2 N:

     {{ LitsPre /\ the temporaries hold s, n = 2 N, nl = nz and e }}
       q = 0; while (q < e) { ... }                               (lits_mark_correct)
     {{ every clause literal is marked }}
       k = 0; while (k < nl) { ... }                              (lits_list_correct)
     {{ result = 0 \/ alls holds distinct clause literals, unmarked }}
       q = 0; while (q < e) { ... }                              (lits_cover_correct)
     {{ result = 0 \/ every clause literal is in alls }}
       return 1;
     {{ LitsPost }}                                                                 *)
Lemma lits_scan_correct: forall (m: mem) (S: Shape) (bm: block) (N: nat)
  (lss: list (list Lit)) (ta tm: nat -> Z) (nz: nat) (le: temp_env),
  LitsPre m S bm N lss (Z.of_nat nz) ta tm -> (nz <= 2 * N)%nat ->
  le ! _s = Some (sptr S) -> le ! _n = Some (vint (Z.of_nat (2 * N))) ->
  le ! _nl = Some (vint (Z.of_nat nz)) -> le ! _e = Some (vint (Z.of_nat (nclits S))) ->
  Exec ge le m lits_scan (Returns f_check_lits (LitsPost m S bm N (Z.of_nat nz) ta)).
Proof.
  intros m S bm N lss ta tm nz le HP Hnz Hs Hn Hnl He.
  pose proof (lits_clause_mem m S bm N lss _ ta tm HP) as HM.
  destruct HP as [Hnd Fnv Fncl Fcs Fcl Fal Fnl Fm As Al Aal Am Hm0 Hzl Hsmall Hend Hat
    HN Hncl Hlss].
  unfold lits_scan, f_check_lits. cbn [fn_body drop_stmts].
  (* q = 0; the marking loop *)
  run. eapply exec_weaken.
  - apply (lits_mark_correct m m S bm N lss nz).
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + constructor.
      * tmp.
      * tmp.
      * tmp.
      * tmp.
      * tmp.
      * lia.
      * assumption.
      * exists tm. split.
        -- assumption.
        -- assumption.
  - intros le1 m1 out [-> HI1]. normal.
    destruct HI1 as [Hs1 Hn1 Hnl1 He1 Hq1 _ HM1 (tm1 & Am1 & Hm1)].
    (* k = 0; the loop over alls *)
    run. eapply exec_weaken.
    + apply (lits_list_correct m m1 S bm N lss ta nz).
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * constructor.
        -- tmp.
        -- tmp.
        -- tmp.
        -- tmp.
        -- tmp.
        -- lia.
        -- intros j Hj. lia.
        -- constructor.
        -- intros l [].
        -- assumption.
        -- exists tm1. split.
           ++ assumption.
           ++ rewrite remaining_nil. assumption.
    + intros le2 m2 out [[-> HI2] | (-> & Hmk2 & Hun2)].
      * normal.
        destruct HI2 as [Hs2 Hn2 Hnl2 He2 Hk2 _ Hkeys2 Hnd2 Hin2 HM2 (tm2 & Am2 & Hm2)].
        (* q = 0; the last loop *)
        run. eapply exec_weaken.
        -- apply (lits_cover_correct m m2 S bm N lss ta nz).
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ constructor.
              ** tmp.
              ** tmp.
              ** tmp.
              ** lia.
              ** intros q' Hq'. lia.
              ** assumption.
              ** exists tm2. split.
                 --- assumption.
                 --- assumption.
        -- intros le3 m3 out [[-> HI3] | (-> & Hmk3 & Hun3)].
           ++ (* return 1; *)
              normal. destruct HI3 as [Hs3 He3 Hq3 _ Hcover HM3 (tm3 & Am3 & Hm3)].
              eapply exec_return.
              ** ev.
              ** exists (vint 1). split.
                 --- apply result_int.
                 --- apply (lits_post_accept m m3 S bm N ta tm3 nz).
                     +++ assumption.
                     +++ apply (cm_frame _ _ _ _ _ _ HM3).
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
           ++ (* return 0 in the last loop *)
              ret. exists (vint 0). split.
              ** apply result_int.
              ** apply lits_post_reject.
                 --- assumption.
                 --- assumption.
      * (* return 0 in the loop over alls *)
        ret. exists (vint 0). split.
        -- apply result_int.
        -- apply lits_post_reject.
           ++ assumption.
           ++ assumption.
Qed.

(* check_lits checks that the caller's literals to decide on, alls[0 .. nl), are the
   literals of the clauses, each once:

     {{ LitsPre zl ta }}
       int n = 2 * s->nv; int nl = s->nlits; int e = s->cstart[s->ncl];
       if (nl < 0) return 0;
       if (nl > n) return 0;
     {{ result = 0 }}
       ...                                                        (lits_scan_correct)
     {{ result = 0 \/ result = 1 /\ alls holds the clause literals, each once }}     *)
Lemma check_lits_correct: forall (S: Shape) (bm: block) (N: nat) (lss: list (list Lit))
  (zl: Z) (ta tm: nat -> Z),
  {{ m | LitsPre m S bm N lss zl ta tm }}
    f_check_lits(sptr S)
  {{ m', v | (exists (tm': nat -> Z), Arr m' bm (2 * N) tm') /\
             Mem.unchanged_on (fun (b: block) (_: Z) => b <> bm) m m' /\
             (v = vint 0 \/
              (v = vint 1 /\ exists (acc: list Lit),
                 zl = Z.of_nat (length acc) /\ NoDup acc /\
                 (length acc <= 2 * N)%nat /\
                 (forall (l: Lit),
                    In l acc <-> exists (q: nat), (q < nclits S)%nat /\ lits S q = l) /\
                 forall (k: nat), (k < length acc)%nat ->
                   ta k = key (nth k acc (Pos 0%nat)))) }}.
Proof.
  intros S bm N lss zl ta tm m HP. pose proof HP as HP'.
  destruct HP' as [Hnd Fnv Fncl Fcs Fcl Fal Fnl Fm As Al Aal Am Hm0 Hzl Hsmall Hend Hat
    HN Hncl Hlss].
  assert (Hmul: Int.mul (Int.repr 2) (Int.repr (Z.of_nat N))
                = Int.repr (Z.of_nat (2 * N))).
  { rewrite mul_repr. f_equal. lia. }
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_check_lits. cbn [fn_body fn_return].
    (* int n = 2 * s->nv; int nl = s->nlits; int e = s->cstart[s->ncl]; *)
    run. ints. rewrite Hend.
    (* if (nl < 0) return 0; *)
    eapply (exec_if_cmp _ _ _ Clt _ _ zl 0).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + assumption.
    + unfold Small. lia.
    + cbn [zcmp]. destruct (Z.ltb_spec zl 0) as [Hneg | Hpos].
      * cbv beta iota. eapply exec_return.
        -- ev.
        -- ret. exists (vint 0). split.
           ++ apply result_int.
           ++ apply (lits_post_reject m m S bm N zl ta).
              ** exists tm. assumption.
              ** apply Mem.unchanged_on_refl.
      * cbv beta iota. apply exec_skip. normal. apply exec_seq.
        (* if (nl > n) return 0; *)
        eapply (exec_if_cmp _ _ _ Cgt _ _ zl (Z.of_nat (2 * N))).
        -- ev.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- assumption.
        -- unfold Small. lia.
        -- cbn [zcmp]. destruct (Z.ltb_spec (Z.of_nat (2 * N)) zl) as [Hbig | Hsm].
           ++ cbv beta iota. eapply exec_return.
              ** ev.
              ** ret. exists (vint 0). split.
                 --- apply result_int.
                 --- apply (lits_post_reject m m S bm N zl ta).
                     +++ exists tm. assumption.
                     +++ apply Mem.unchanged_on_refl.
           ++ (* nl is some nz at most 2 N: the loops *)
              cbv beta iota. apply exec_skip. normal.
              assert (Hz: zl = Z.of_nat (Z.to_nat zl)) by lia.
              remember (Z.to_nat zl) as nz eqn:Hnz. rewrite Hz in HP |- *.
              apply (lits_scan_correct m S bm N lss ta tm nz).
              ** assumption.
              ** lia.
              ** tmp.
              ** tmp.
              ** tmp.
              ** tmp.
Qed.

Lemma check_lits_fun: exists (b: block),
  Genv.find_symbol ge _check_lits = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_check_lits).
Proof. apply find_fun. reflexivity. Qed.
