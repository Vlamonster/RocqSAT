(* check_lits checks the literals to decide on that the caller put in alls: they are the
   literals of the clauses, each once, in any order. *)
From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Finite.
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
From RocqSAT.refinement Require Import Table.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement.c Require Import Arrays.
From RocqSAT.refinement.c Require Import Logic.
From RocqSAT.refinement.c Require Import Common.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Rep.
From RocqSAT.refinement.c Require Import CheckClauses.

Section Lists.
  (* The literals of the first k entries of the table ta of keys. *)
  Definition decoded (ta: nat -> Z) (k: nat): list Lit :=
    map (fun (j: nat) => lit_of (ta j)) (seq 0 k).

  (* The first k + 1 entries: the first k and the one at k. *)
  Lemma decoded_snoc: forall (ta: nat -> Z) (k: nat),
    decoded ta (S k) = decoded ta k ++ [lit_of (ta k)].
  Proof. intros ta k. unfold decoded. rewrite seq_S, map_app. reflexivity. Qed.

  (* There are k of them. *)
  Lemma decoded_length: forall (ta: nat -> Z) (k: nat), length (decoded ta k) = k.
  Proof. intros ta k. unfold decoded. rewrite length_map, length_seq. reflexivity. Qed.

  (* Entry j of them is the literal of ta j. *)
  Lemma decoded_nth: forall (ta: nat -> Z) (k j: nat), (j < k)%nat ->
    nth j (decoded ta k) (Pos 0%nat) = lit_of (ta j).
  Proof.
    intros ta k j Hj. unfold decoded.
    pose proof (map_nth (fun (i: nat) => lit_of (ta i)) (seq 0 k) 0%nat j) as Hmap.
    cbv beta in Hmap. rewrite (nth_indep _ (Pos 0%nat) (lit_of (ta 0%nat))).
    - rewrite Hmap, seq_nth by assumption. reflexivity.
    - rewrite length_map, length_seq. assumption.
  Qed.

  (* The clause literals: those at the positions below nclits sh. *)
  Lemma in_clause_lits: forall (sh: Shape) (l: Lit),
    In l (span sh 0 (nclits sh)) <->
    exists (q: nat), (q < nclits sh)%nat /\ lits sh q = l.
  Proof.
    intros sh l. unfold span. rewrite in_map_iff. split.
    - intros [q [<- Hq]]. apply in_seq in Hq. exists q. split.
      + lia.
      + reflexivity.
    - intros [q [Hq <-]]. exists q. split.
      + reflexivity.
      + apply in_seq. lia.
  Qed.

  (* The clause literals that are not among done: those still marked. *)
  Definition remaining (sh: Shape) (done: list Lit): list Lit :=
    filter
              (fun (l: Lit) => negb (existsb (fun (y: Lit) => Nat.eqb (lit_key y)
                (lit_key l)) done))
      (span sh 0 (nclits sh)).

  (* The remaining literals are the clause literals not among done. *)
  Lemma in_remaining: forall (sh: Shape) (done: list Lit) (l: Lit),
    In l (remaining sh done) <-> In l (span sh 0 (nclits sh)) /\ ~ In l done.
  Proof.
    intros sh done l. unfold remaining. rewrite filter_In, negb_true_iff. split.
    - intros [Hl Hex]. split.
      + assumption.
      + intros Hin. apply existsb_key in Hin. congruence.
    - intros [Hl Hnot]. split.
      + assumption.
      + apply not_true_iff_false. intros Hex. apply existsb_key in Hex. contradiction.
  Qed.

  (* With none done, all clause literals remain. *)
  Lemma remaining_nil: forall (sh: Shape), remaining sh [] = span sh 0 (nclits sh).
  Proof.
    intros sh. unfold remaining. induction (span sh 0 (nclits sh)) as [|l ls IH].
    - reflexivity.
    - simpl. f_equal. apply IH.
  Qed.

  (* Unmarking y, which is still marked, moves it to done. *)
  Lemma marks_unmark: forall (sh: Shape) (N: nat) (tm: nat -> Z) (done: list Lit)
    (y: Lit),
    Marks N tm (remaining sh done) ->
    Marks N (fun (j: nat) => if Nat.eqb (lit_key y) j then 0 else tm j)
      (remaining sh (done ++ [y])).
  Proof.
    intros sh N tm done y Hm k Hk. destruct (Nat.eqb_spec (lit_key y) k) as [<- | Hne].
    - (* y is not marked any more *)
      destruct (existsb _ (remaining sh (done ++ [y]))) eqn:Hex.
      + apply existsb_key in Hex. apply in_remaining in Hex as [_ Hnot].
        exfalso. apply Hnot. apply in_or_app. right. left. reflexivity.
      + reflexivity.
    - (* the other literals are marked as before *)
      rewrite (Hm k Hk).
      assert (Hiff: existsb (fun (l: Lit) => Nat.eqb (lit_key l) k)
                      (remaining sh done) = true
                    <-> existsb (fun (l: Lit) => Nat.eqb (lit_key l) k)
                          (remaining sh (done ++ [y])) = true).
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
      destruct (existsb _ (remaining sh done)), (existsb _ (remaining sh (done ++ [y]))).
      + reflexivity.
      + exfalso. assert (Htrue: false = true) by (apply Hiff; reflexivity). discriminate.
      + exfalso. assert (Htrue: false = true) by (apply Hiff; reflexivity). discriminate.
      + reflexivity.
  Qed.
End Lists.


(* What check_lits needs: the clauses and their sizes, the caller's literals in alls, the
   clause literals with atoms below N, small ints as it compares them, and no marks. *)
Record LitsPre {m: mem} {sh: Shape} {N: nat} {lss: list (list Lit)} {zl: Z}
  {ta tm: nat -> Z}: Prop := {
  lp_nodup: NoDup (iblocks sh);
  lp_clauses: ClauseFlds sh N lss m;
  lp_alls: PtrAt m sh o_alls (b_alls sh);
  lp_nlits: Fld m (b_s sh) o_nlits Mint32 (vint zl);
  lp_aalls: Arr m (b_alls sh) (2 * N) ta;
  lp_amrk: Arr m (b_mrk sh) (2 * N) tm;
  lp_marks: Marks N tm [];
  lp_small: Small zl;
  lp_small_alls: forall (k: nat), (k < 2 * N)%nat -> Small (ta k);
  lp_layout: Layout sh lss;
  lp_atoms: forall (q: nat), (q < nclits sh)%nat -> (extract (lits sh q) < N)%nat;
  lp_sizes: Sizes sh N lss;
}.
Arguments LitsPre : clear implicits.

(* check_lits returns 0, having changed only the marks. *)
Definition LitsReject (m: mem) (sh: Shape) (N: nat) (m': mem) (out: outcome): Prop :=
  out = ret_int 0 /\
  (exists (tm': nat -> Z), Arr m' (b_mrk sh) (2 * N) tm') /\
  Mem.unchanged_on (AllBut (b_mrk sh)) m m'.

Lemma lits_reject: forall (m m1: mem) (sh: Shape) (N: nat)
  (lss: list (list Lit)) (tm: nat -> Z),
  ClauseMem m sh N lss m1 -> Arr m1 (b_mrk sh) (2 * N) tm ->
  LitsReject m sh N m1 (ret_int 0).
Proof.
  intros m m1 sh N lss tm HM Am. split.
  - reflexivity.
  - split.
    + exists tm. assumption.
    + apply (cm_frame HM).
Qed.

(* The field and the array alls are as in the memory m of the call. *)
Lemma alls_kept: forall (m m1: mem) (sh: Shape) (N: nat)
  (lss: list (list Lit)) (ta: nat -> Z),
  NoDup (iblocks sh) -> ClauseMem m sh N lss m1 ->
  PtrAt m sh o_alls (b_alls sh) ->
  Arr m (b_alls sh) (2 * N) ta ->
  PtrAt m1 sh o_alls (b_alls sh) /\
  Arr m1 (b_alls sh) (2 * N) ta.
Proof.
  intros m m1 sh N lss ta Hnd HM Fal Aal. pose proof (cm_frame HM) as Hun.
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

(* The body of the loop over alls after its range checks. *)
Definition lits_take: statement := drop_stmts 3 (drop_stmts 1 (loop_body lits_list)).


(* When every clause literal is done, no literal is marked. *)
Lemma marks_none: forall (sh: Shape) (N: nat) (tm ta: nat -> Z) (nz: nat),
  Marks N tm (remaining sh (decoded ta nz)) ->
  (forall (q: nat), (q < nclits sh)%nat -> In (lits sh q) (decoded ta nz)) ->
  forall (k: nat), (k < 2 * N)%nat -> tm k = 0.
Proof.
  intros sh N tm ta nz Hm Hcover k Hk. rewrite (Hm k Hk).
  destruct (existsb _ _) eqn:Hex.
  - exfalso. apply existsb_exists in Hex as (y & Hy & _).
    apply in_remaining in Hy as [Hspan Hnot].
    apply in_clause_lits in Hspan as (q & Hq & <-).
    apply Hnot. apply Hcover. assumption.
  - reflexivity.
Qed.

(* What check_lits returns: 0, or 1 when the zl entries of alls (the table ta) are the
   clause literals acc, each once, and no literal is marked; only the marks change. *)
Definition LitsPost (m: mem) (sh: Shape) (N: nat) (zl: Z) (ta: nat -> Z)
  (m': mem) (v: val): Prop :=
  (exists (tm': nat -> Z), Arr m' (b_mrk sh) (2 * N) tm') /\
  Mem.unchanged_on (AllBut (b_mrk sh)) m m' /\
  (v = vint 0 \/
   (v = vint 1 /\ Arr m' (b_mrk sh) (2 * N) (fun (_: nat) => 0) /\
    exists (acc: list Lit),
      zl = Z.of_nat (length acc) /\ NoDup acc /\ (length acc <= 2 * N)%nat /\
      (forall (l: Lit),
         In l acc <-> exists (q: nat), (q < nclits sh)%nat /\ lits sh q = l) /\
      forall (k: nat), (k < length acc)%nat -> ta k = key (nth k acc (Pos 0%nat)))).

(* check_lits may return 0 whenever only the marks changed. *)
Lemma lits_post_reject: forall (m m': mem) (sh: Shape) (N: nat) (zl: Z)
  (ta: nat -> Z),
  (exists (tm': nat -> Z), Arr m' (b_mrk sh) (2 * N) tm') ->
  Mem.unchanged_on (AllBut (b_mrk sh)) m m' ->
  LitsPost m sh N zl ta m' (vint 0).
Proof.
  intros m m' sh N zl ta Hmk Hun. split.
  - assumption.
  - split.
    + assumption.
    + left. reflexivity.
Qed.

(* Returning 1 at the end: the nz literals of alls are the clause literals, each once. *)
Lemma lits_post_accept: forall (m m': mem) (sh: Shape) (N: nat)
  (ta tm: nat -> Z) (nz: nat),
  Arr m' (b_mrk sh) (2 * N) tm -> Mem.unchanged_on
    (AllBut (b_mrk sh)) m m' ->
  Marks N tm (remaining sh (decoded ta nz)) ->
  (nz <= 2 * N)%nat -> (forall (j: nat), (j < nz)%nat -> 0 <= ta j) ->
  NoDup (decoded ta nz) ->
  (forall (l: Lit), In l (decoded ta nz) -> In l (span sh 0 (nclits sh))) ->
  (forall (q: nat), (q < nclits sh)%nat -> In (lits sh q) (decoded ta nz)) ->
  LitsPost m sh N (Z.of_nat nz) ta m' (vint 1).
Proof.
  intros m m' sh N ta tm nz Am Hun Hm Hnz Hkeys Hnd Hin Hcover. split.
  - exists tm. assumption.
  - split.
    + assumption.
    + right. split.
      * reflexivity.
      * split.
        -- (* no literal is marked *)
           apply (arr_ext m' (b_mrk sh) (2 * N) tm).
           ++ assumption.
           ++ intros k Hk. symmetry. apply (marks_none sh N tm ta nz Hm Hcover k Hk).
        -- exists (decoded ta nz). rewrite decoded_length. split.
           ++ reflexivity.
           ++ split.
              ** assumption.
              ** split.
                 --- assumption.
                 --- split.
                     +++ (* in alls exactly when a clause literal *)
                         intros l. split.
                         *** intros Hl. apply in_clause_lits. apply Hin. assumption.
                         *** intros [q [Hq <-]]. apply Hcover. assumption.
                     +++ (* alls holds their keys *)
                         intros k Hk. rewrite decoded_nth by assumption. symmetry.
                         apply key_lit_of. apply Hkeys. assumption.
Qed.

(* The facts of the memory of the call, for its loops. *)
Lemma lits_clause_mem: forall (m: mem) (sh: Shape) (N: nat)
  (lss: list (list Lit)) (zl: Z) (ta tm: nat -> Z),
  LitsPre m sh N lss zl ta tm -> ClauseMem m sh N lss m.
Proof.
  intros m sh N lss zl ta tm HP. constructor.
  - apply (lp_clauses HP).
  - frame.
Qed.


(* The statements after the range checks: the three loops and return 1. *)
Definition lits_scan: statement := drop_stmts 5 (fn_body f_check_lits).

Section Loops.
  (* A call of check_lits from the memory m, with the marks tm0 and the nz literals of
     alls in ta, nz at most 2 N. *)
  Variables (m: mem) (sh: Shape) (N: nat) (lss: list (list Lit)) (ta: nat -> Z)
    (nz: nat) (tm0: nat -> Z).
  Hypothesis (HP: LitsPre m sh N lss (Z.of_nat nz) ta tm0).
  Hypothesis (Hnz: (nz <= 2 * N)%nat).

  (* The invariant of the marking loop at q: the clause literals before q are marked. *)
  Record MarkLitsInv (q: nat) (le: temp_env) (m1: mem): Prop := {
    mk_s: le ! _s = Some (sptr sh);
    mk_n: le ! _n = Some (vnat (2 * N));
    mk_nl: le ! _nl = Some (vnat nz);
    mk_e: le ! _e = Some (vnat (nclits sh));
    mk_q: le ! _q = Some (vnat q);
    mk_le: (q <= nclits sh)%nat;
    mk_mem: ClauseMem m sh N lss m1;
    mk_marks: exists (tm: nat -> Z), Arr m1 (b_mrk sh) (2 * N) tm /\ Marks N tm
      (span sh 0 q);
  }.

  (* The marking loop, over the clause literals:

       {{ MarkLitsInv 0 }}
         while (q < e) {
           s->mrk[s->clits[q]] = 1;                                         (marks_add)
           q++;
         }
       {{ MarkLitsInv e: every clause literal is marked }}

     The loop ends: nclits sh - q decreases. *)
  Lemma lits_mark_correct: forall (le: temp_env) (m1: mem),
    MarkLitsInv 0 le m1 ->
    Exec ge le m1 lits_mark
      (fun (le': temp_env) (m': mem) (out: outcome) =>
         out = Out_normal /\ MarkLitsInv (nclits sh) le' m').
  Proof.
    intros le m1 HI0. pose proof HP as [Hnd _ _ _ _ _ _ _ _ _ Hat [HN Hncl _ _]].
    unfold lits_mark, f_check_lits. cbn [fn_body drop_stmts first_stmt]. unfold Swhile.
    apply exec_loop with (R := ltof nat (fun (q: nat) => nclits sh - q)%nat)
      (I := MarkLitsInv) (a := 0%nat).
    - apply well_founded_ltof.
    - intros q le2 m2 HI.
      destruct HI as [Hs Hn Hnl He Hq Hqle HM (tm & Am & Hm)].
      pose proof HM as [[Fnv Fncl Fcs Fcl Fm As Al] Hun].
      (* while (q < e) *)
      apply exec_seq. branch.
      + (* s->mrk[s->clits[q]] = 1; q++; *)
        intros Hlt. assert (Hq_lt: (q < nclits sh)%nat) by lia.
        pose proof (Hat q Hq_lt) as Hy.
        assert (Hky: (lit_key (lits sh q) < 2 * N)%nat)
          by (apply lit_key_lt; assumption).
        assert (Hadd: Int.add (Int.repr (Z.of_nat q)) (Int.repr 1)
                      = Int.repr (Z.of_nat (S q))).
        { apply incr_nat. lia. }
        apply exec_skip. normal. run. store Am Hky as m3 Hst.
        run. ints. apply loopk_next with (S q).
        * unfold ltof. lia.
        * constructor.
          -- tmp.
          -- tmp.
          -- tmp.
          -- tmp.
          -- tmp.
          -- lia.
          -- apply (clause_mem_store m m2 m3 sh N lss _ _ Hnd HM Hst).
          -- eexists. split.
             ++ apply (arr_store Am Hky Hst).
             ++ rewrite span_snoc by lia. apply marks_add. assumption.
      + (* q >= e: break *)
        intros Hge. apply exec_break. abrupt. apply loopk_break. split.
        * reflexivity.
        * replace (nclits sh) with q by lia. constructor.
          -- tmp.
          -- tmp.
          -- tmp.
          -- replace q with (nclits sh) by lia. tmp.
          -- tmp.
          -- lia.
          -- assumption.
          -- exists tm. split; assumption.
    - assumption.
  Qed.

  (* The invariant of the loop over alls at k: the first k entries of alls are distinct
     clause literals, done, and the marked literals are the other clause literals. *)
  Record ListInv (k: nat) (le: temp_env) (m1: mem): Prop := {
    li_s: le ! _s = Some (sptr sh);
    li_n: le ! _n = Some (vnat (2 * N));
    li_nl: le ! _nl = Some (vnat nz);
    li_e: le ! _e = Some (vnat (nclits sh));
    li_k: le ! _k = Some (vnat k);
    li_le: (k <= nz)%nat;
    li_keys: forall (j: nat), (j < k)%nat -> 0 <= ta j;
    li_nodup: NoDup (decoded ta k);
    li_in: forall (l: Lit), In l (decoded ta k) -> In l (span sh 0 (nclits sh));
    li_mem: ClauseMem m sh N lss m1;
    li_marks: exists (tm: nat -> Z), Arr m1 (b_mrk sh) (2 * N) tm /\
      Marks N tm (remaining sh (decoded ta k));
  }.

  (* The variant and the end of the loop over alls. *)
  Definition list_variant: nat -> nat -> Prop :=
    ltof nat (fun (k: nat) => nz - k)%nat.

  Definition ListPost (le': temp_env) (m': mem) (out: outcome): Prop :=
    (out = Out_normal /\ ListInv nz le' m') \/ LitsReject m sh N m' out.

  (* The literal y' = lit_of (alls[k]) of the loop over alls, whose key y is below 2 N;
     le has the temporaries of ListInv, and y and t'8 that the body set:

       {{ ListInv k /\ y = key y' }}
         if (s->mrk[y] == 0) return 0;
       {{ result = 0: y' is not of a clause, or there twice }}
         s->mrk[y] = 0;                                                 (marks_unmark)
         k++;
       {{ ListInv (k + 1) }}                                                           *)
  Lemma lits_take_correct: forall (k: nat) (le2 le: temp_env) (m2: mem),
    ListInv k le2 m2 -> (k < nz)%nat -> 0 <= ta k < Z.of_nat (2 * N) ->
    le = PTree.set _y (vint (ta k))
           (PTree.set _t'8 (Vptr (b_alls sh) Ptrofs.zero) le2) ->
    Exec ge le m2 lits_take (LoopK list_variant ListInv ListPost k).
  Proof.
    intros k le2 le m2 HI Hlt Hrange ->.
    pose proof HP as [Hnd _ _ _ _ _ _ _ _ _ _ [HN _ _ _]].
    destruct HI as [Hs Hn Hnl He Hk Hkle Hkeys Hndk Hin HM (tm & Am & Hm)].
    pose proof HM as [[Fnv Fncl Fcs Fcl Fm As Al] Hun].
    (* y is the key of the literal y' *)
    remember (lit_of (ta k)) as y' eqn:Hy'.
    assert (Hkey: ta k = key y').
    { rewrite Hy'. symmetry. apply key_lit_of. lia. }
    assert (Hky: (lit_key y' < 2 * N)%nat) by (unfold key in Hkey; lia).
    unfold lits_take, lits_list, f_check_lits.
    cbn [fn_body drop_stmts first_stmt loop_body Swhile].
    rewrite Hkey. run. rewrite (Hm _ Hky).
    (* if (s->mrk[y] == 0) return 0; *)
    eapply exec_if_eq.
    - ev.
    - ev.
    - reflexivity.
    - destruct (existsb _ _); lia.
    - (* y' is not marked: not of a clause, or there twice *)
      intros _. eapply exec_return.
      + ev.
      + ret. right. apply (lits_reject m m2 sh N lss tm HM Am).
    - intros Hmarked.
      destruct (existsb (fun (l: Lit) => Nat.eqb (lit_key l) (lit_key y'))
                  (remaining sh (decoded ta k))) eqn:Hex.
      + (* y' is marked: s->mrk[y] = 0; k++; *)
        apply exec_skip. normal.
        apply existsb_key in Hex. apply in_remaining in Hex as [Hcl Hnew].
        assert (Hadd: Int.add (Int.repr (Z.of_nat k)) (Int.repr 1)
                      = Int.repr (Z.of_nat (S k))).
        { apply incr_nat. lia. }
        run. store Am Hky as m3 Hst.
        run. ints. apply loopk_next with (S k).
        * unfold list_variant, ltof. lia.
        * constructor.
          -- tmp.
          -- tmp.
          -- tmp.
          -- tmp.
          -- tmp.
          -- lia.
          -- (* the key at k is not negative *)
             intros j Hj. destruct (Nat.eq_dec j k) as [-> | Hne].
             ++ lia.
             ++ apply Hkeys. lia.
          -- (* y' was not done yet *)
             rewrite decoded_snoc, <- Hy'. apply NoDup_app.
             ++ assumption.
             ++ constructor.
                ** easy.
                ** constructor.
             ++ intros l Hl [<- | []]. contradiction.
          -- (* y' is a clause literal *)
             rewrite decoded_snoc, <- Hy'. intros l Hl.
             apply in_app_or in Hl as [Hl | [<- | []]].
             ++ apply Hin. assumption.
             ++ assumption.
          -- apply (clause_mem_store m m2 m3 sh N lss _ _ Hnd HM Hst).
          -- eexists. split.
             ++ apply (arr_store Am Hky Hst).
             ++ rewrite decoded_snoc, <- Hy'. apply marks_unmark. assumption.
      + (* the mark is 0 here, but the test said it was not *)
        exfalso. apply Hmarked. reflexivity.
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
  Lemma lits_list_correct: forall (le: temp_env) (m1: mem),
    ListInv 0 le m1 -> Exec ge le m1 lits_list ListPost.
  Proof.
    intros le m1 HI0. pose proof HP as [Hnd _ Fal _ Aal _ _ _ Hsmall _ _ [HN _ _ _]].
    unfold lits_list, f_check_lits. cbn [fn_body drop_stmts first_stmt]. unfold Swhile.
    apply exec_loop with (R := list_variant) (I := ListInv) (a := 0%nat).
    - apply well_founded_ltof.
    - intros k le2 m2 HI. pose proof HI as HI'.
      destruct HI' as [Hs Hn Hnl He Hk Hkle Hkeys Hndk Hin HM (tm & Am & Hm)].
      pose proof HM as [[Fnv Fncl Fcs Fcl Fm As Al] Hun].
      destruct (alls_kept m m2 sh N lss ta Hnd HM Fal Aal) as [Fal2 Aal2].
      (* while (k < nl) *)
      apply exec_seq. branch.
      + intros Hlt. apply exec_skip. normal.
        (* int y = s->alls[k]; *)
        run.
        (* if (y < 0) return 0; *)
        assert (Hsmall_k: Small (ta k)) by (apply Hsmall; lia).
        branch.
        * (* not a literal *)
          intros _. eapply exec_return.
          -- ev.
          -- ret. right. apply (lits_reject m m2 sh N lss tm HM Am).
        * intros Hpos. apply exec_skip. normal. apply exec_seq.
          (* if (y >= n) return 0; *)
          branch.
          -- (* an atom not below N *)
             intros _. eapply exec_return.
             ++ ev.
             ++ ret. right. apply (lits_reject m m2 sh N lss tm HM Am).
          -- (* the rest of the body, for the literal y' with key y *)
             intros Hsm. apply exec_skip. normal.
             apply (lits_take_correct k le2 _ m2).
             ++ assumption.
             ++ lia.
             ++ lia.
             ++ reflexivity.
      + (* k >= nl: break *)
        intros Hge. apply exec_break. abrupt. apply loopk_break. left. split.
        * reflexivity.
        * replace k with nz in * by lia. constructor.
          -- tmp.
          -- tmp.
          -- tmp.
          -- tmp.
          -- tmp.
          -- lia.
          -- assumption.
          -- assumption.
          -- assumption.
          -- assumption.
          -- exists tm. split; assumption.
    - assumption.
  Qed.

  (* The invariant of the last loop at q: the clause literals before q are among the nz
     literals of alls. *)
  Record CoverInv (q: nat) (le: temp_env) (m1: mem): Prop := {
    cv_s: le ! _s = Some (sptr sh);
    cv_e: le ! _e = Some (vnat (nclits sh));
    cv_q: le ! _q = Some (vnat q);
    cv_le: (q <= nclits sh)%nat;
    cv_cover: forall (q': nat), (q' < q)%nat -> In (lits sh q') (decoded ta nz);
    cv_mem: ClauseMem m sh N lss m1;
    cv_marks: exists (tm: nat -> Z), Arr m1 (b_mrk sh) (2 * N) tm /\
      Marks N tm (remaining sh (decoded ta nz));
  }.

  (* The last loop, over the clause literals again:

       {{ CoverInv 0 }}
         while (q < e) {
           if (s->mrk[s->clits[q]] != 0) return 0;
       {{ result = 0: a clause literal is not in alls }}
           q++;
         }
       {{ CoverInv e: every clause literal is in alls }}

     The loop ends: nclits sh - q decreases. *)
  Lemma lits_cover_correct: forall (le: temp_env) (m1: mem),
    CoverInv 0 le m1 ->
    Exec ge le m1 lits_cover
      (fun (le': temp_env) (m': mem) (out: outcome) =>
         (out = Out_normal /\ CoverInv (nclits sh) le' m') \/ LitsReject m sh N m' out).
  Proof.
    intros le m1 HI0. pose proof HP as [_ _ _ _ _ _ _ _ _ _ Hat [HN Hncl _ _]].
    unfold lits_cover, f_check_lits. cbn [fn_body drop_stmts first_stmt]. unfold Swhile.
    apply exec_loop with (R := ltof nat (fun (q: nat) => nclits sh - q)%nat)
      (I := CoverInv) (a := 0%nat).
    - apply well_founded_ltof.
    - intros q le2 m2 HI.
      destruct HI as [Hs He Hq Hqle Hcover HM (tm & Am & Hm)].
      pose proof HM as [[Fnv Fncl Fcs Fcl Fm As Al] Hun].
      (* while (q < e) *)
      apply exec_seq. branch.
      + intros Hlt. assert (Hq_lt: (q < nclits sh)%nat) by lia.
        pose proof (Hat q Hq_lt) as Hy.
        assert (Hky: (lit_key (lits sh q) < 2 * N)%nat)
          by (apply lit_key_lt; assumption).
        apply exec_skip. normal.
        (* if (s->mrk[s->clits[q]] != 0) return 0; *)
        run. rewrite (Hm _ Hky).
        eapply exec_if_ne.
        * ev.
        * ev.
        * reflexivity.
        * destruct (existsb _ _); lia.
        * (* still marked: not in alls *)
          intros _. eapply exec_return.
          -- ev.
          -- ret. right. apply (lits_reject m m2 sh N lss tm HM Am).
        * intros Hunmarked.
          destruct (existsb (fun (l: Lit) => Nat.eqb (lit_key l) (lit_key (lits sh q)))
                      (remaining sh (decoded ta nz))) eqn:Hex.
          -- (* the mark is 1 here, but the test said it was 0 *)
             discriminate Hunmarked.
          -- (* not marked: in alls; q++ *)
             apply exec_skip. normal.
             assert (Hadd: Int.add (Int.repr (Z.of_nat q)) (Int.repr 1)
                           = Int.repr (Z.of_nat (S q))).
             { apply incr_nat. lia. }
             run. ints. apply loopk_next with (S q).
             ++ unfold ltof. lia.
             ++ constructor.
                ** tmp.
                ** tmp.
                ** tmp.
                ** lia.
                ** (* the literal at q is a clause literal that is not marked *)
                   intros q' Hq'. destruct (Nat.eq_dec q' q) as [-> | Hne].
                   --- destruct (in_dec Lit.eq_dec (lits sh q) (decoded ta nz))
                         as [Hdone | Hnot].
                       +++ assumption.
                       +++ exfalso.
                           assert (Hrem: In (lits sh q) (remaining sh (decoded ta nz))).
                           { apply in_remaining. split.
                             - apply in_clause_lits. exists q. split.
                               + assumption.
                               + reflexivity.
                             - assumption. }
                           apply existsb_key in Hrem. congruence.
                   --- apply Hcover. lia.
                ** assumption.
                ** exists tm. split; assumption.
      + (* q >= e: break *)
        intros Hge. apply exec_break. abrupt. apply loopk_break. left. split.
        * reflexivity.
        * replace q with (nclits sh) in * by lia. constructor.
          -- tmp.
          -- tmp.
          -- tmp.
          -- lia.
          -- assumption.
          -- assumption.
          -- exists tm. split; assumption.
    - assumption.
  Qed.


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
  Lemma lits_scan_correct: forall (le: temp_env),
    le ! _s = Some (sptr sh) -> le ! _n = Some (vnat (2 * N)) ->
    le ! _nl = Some (vnat nz) -> le ! _e = Some (vnat (nclits sh)) ->
    Exec ge le m lits_scan (Returns f_check_lits (LitsPost m sh N (Z.of_nat nz) ta)).
  Proof.
    intros le Hs Hn Hnl He.
    pose proof (lits_clause_mem m sh N lss _ ta tm0 HP) as HM.
    pose proof HP as [Hnd _ Fal Fnl Aal Am Hm0 Hzl Hsmall _ Hat [HN Hncl _ Hlss]].
    unfold lits_scan, f_check_lits. cbn [fn_body drop_stmts].
    (* q = 0; the marking loop *)
    run. eapply exec_weaken.
    - apply lits_mark_correct. constructor.
      + tmp.
      + tmp.
      + tmp.
      + tmp.
      + tmp.
      + lia.
      + assumption.
      + exists tm0. split; assumption.
    - intros le1 m1 out [-> HI1]. normal.
      destruct HI1 as [Hs1 Hn1 Hnl1 He1 Hq1 _ HM1 (tm1 & Am1 & Hm1)].
      (* k = 0; the loop over alls *)
      run. eapply exec_weaken.
      + apply lits_list_correct. constructor.
        * tmp.
        * tmp.
        * tmp.
        * tmp.
        * tmp.
        * lia.
        * intros j Hj. lia.
        * constructor.
        * intros l [].
        * assumption.
        * exists tm1. split.
          -- assumption.
          -- rewrite remaining_nil. assumption.
      + intros le2 m2 out [[-> HI2] | (-> & Hmk2 & Hun2)].
        * normal.
          destruct HI2
            as [Hs2 Hn2 Hnl2 He2 Hk2 _ Hkeys2 Hnd2 Hin2 HM2 (tm2 & Am2 & Hm2)].
          (* q = 0; the last loop *)
          run. eapply exec_weaken.
          -- apply lits_cover_correct. constructor.
             ++ tmp.
             ++ tmp.
             ++ tmp.
             ++ lia.
             ++ intros q' Hq'. lia.
             ++ assumption.
             ++ exists tm2. split; assumption.
          -- intros le3 m3 out [[-> HI3] | (-> & Hmk3 & Hun3)].
             ++ (* return 1; *)
                normal. destruct HI3 as [Hs3 He3 Hq3 _ Hcover HM3 (tm3 & Am3 & Hm3)].
                return_int.
                apply (lits_post_accept m m3 sh N ta tm3 nz).
                ** assumption.
                ** apply (cm_frame HM3).
                ** assumption.
                ** assumption.
                ** assumption.
                ** assumption.
                ** assumption.
                ** assumption.
             ++ (* return 0 in the last loop *)
                ret. exists (vint 0). split.
                ** apply result_int.
                ** apply lits_post_reject; assumption.
        * (* return 0 in the loop over alls *)
          ret. exists (vint 0). split.
          -- apply result_int.
          -- apply lits_post_reject; assumption.
  Qed.
End Loops.

(* check_lits checks that the caller's literals to decide on, alls[0 .. nl), are the
   literals of the clauses, each once:

     {{ LitsPre zl ta }}
       int n = 2 * s->nv; int nl = s->nlits; int e = s->cstart[s->ncl];
       if (nl < 0) return 0;
       if (nl > n) return 0;
     {{ result = 0 }}
       ...                                                        (lits_scan_correct)
     {{ result = 0 \/ result = 1 /\ alls holds the clause literals, each once /\
        no literal is marked }}                                                        *)
Lemma check_lits_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (zl: Z) (ta tm: nat -> Z),
  {{ m | LitsPre m sh N lss zl ta tm }}
    f_check_lits(sptr sh)
  {{ m', v | LitsPost m sh N zl ta m' v }}.
Proof.
  intros sh N lss zl ta tm m HP. pose proof HP as HP'.
  destruct HP' as [Hnd [Fnv Fncl Fcs Fcl Fm As Al] Fal Fnl Aal Am Hm0 Hzl Hsmall
    [_ _ Hend] Hat [HN Hncl _ Hlss]].
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
    branch.
    + intros _. return_int.
      apply (lits_post_reject m m sh N zl ta).
      * exists tm. assumption.
      * frame.
    + intros Hpos. apply exec_skip. normal. apply exec_seq.
      (* if (nl > n) return 0; *)
      branch.
      * intros _. return_int.
        apply (lits_post_reject m m sh N zl ta).
        -- exists tm. assumption.
        -- frame.
      * (* nl is some nz at most 2 N: the loops *)
        intros Hsm. apply exec_skip. normal.
        assert (Hz: zl = Z.of_nat (Z.to_nat zl)) by lia.
        remember (Z.to_nat zl) as nz eqn:Hnz. rewrite Hz in HP |- *.
        apply (lits_scan_correct m sh N lss ta nz tm).
        -- assumption.
        -- lia.
        -- tmp.
        -- tmp.
        -- tmp.
        -- tmp.
Qed.

Lemma check_lits_fun: FunAt _check_lits f_check_lits.
Proof. apply find_fun. reflexivity. Qed.
