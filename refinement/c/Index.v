(* index_clauses watches the first literals of the clauses and collects the short ones
   (index), or gives up. *)
From Stdlib Require Import List Bool.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Ctypesdefs Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Heur Propagate Step CStep.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep Wpush.
Import ListNotations.
Local Open Scope nat_scope.

Section Model.
  (* Indexing one more clause. *)
  Lemma index_snoc: forall (l1: list (list Lit)) (ls: list Lit) (k: nat) (cm: ClauseMap)
    (wl: WatchLists) (sh: list nat),
    index k (l1 ++ [ls]) cm wl sh =
    match index k l1 cm wl sh with
    | (cm', wl', sh') =>
      (tset cm' (k + length l1) (Some ls), watch_first wl' (k + length l1) ls,
       if length ls <=? 1 then (k + length l1) :: sh' else sh')
    end.
  Proof.
    intros l1. induction l1 as [|ls1 l1 IH]; intros ls k cm wl sh; simpl.
    - now rewrite Nat.add_0_r.
    - rewrite IH.
      now replace (Datatypes.S k + length l1)%nat with (k + Datatypes.S (length l1))%nat
        by lia.
  Qed.

  (* Position i is in the range of n + 1 positions from k, but not k itself, exactly when
     it is in the range of n positions from k + 1. *)
  Lemma in_range_succ: forall (k i n: nat), k <> i ->
    ((Datatypes.S k <=? i) && (i <? Datatypes.S k + n)) =
      ((k <=? i) && (i <? k + Datatypes.S n)).
  Proof.
    intros k i n Hne. apply eq_true_iff_eq.
    rewrite !andb_true_iff, !Nat.leb_le, !Nat.ltb_lt. lia.
  Qed.

  (* No position is in the empty range. *)
  Lemma in_range_empty: forall (k i: nat), ((k <=? i) && (i <? k + 0)) = false.
  Proof.
    intros k i. rewrite Nat.add_0_r. apply not_true_iff_false.
    rewrite andb_true_iff, Nat.leb_le, Nat.ltb_lt. lia.
  Qed.

  (* The clauses the index sets, by position. *)
  Lemma index_cmap: forall (l: list (list Lit)) (k: nat) (cm cm': ClauseMap)
    (wl wl': WatchLists) (sh sh': list nat) (i: nat),
    index k l cm wl sh = (cm', wl', sh') ->
    tget cm' i = (if (k <=? i) && (i <? k + length l) then Some (nth (i - k) l [])
                  else tget cm i)%nat.
  Proof.
    intros l. induction l as [|ls l IH]; intros k cm cm' wl wl' sh sh' i Hix;
      simpl in Hix.
    - injection Hix as <- <- <-. cbn [length]. rewrite in_range_empty. reflexivity.
    - apply (IH _ _ _ _ _ _ _ i) in Hix as Hc. rewrite Hc. rewrite tget_tset.
      cbn [length]. destruct (Nat.eq_dec k i) as [<- | Hne].
      + (* the first clause of the list is at position k *)
        rewrite Nat.leb_refl, Nat.sub_diag.
        replace (Datatypes.S k <=? k)%nat with false
          by (symmetry; apply Nat.leb_gt; lia).
        replace (k <? k + Datatypes.S (length l))%nat with true
          by (symmetry; apply Nat.ltb_lt; lia).
        reflexivity.
      + (* a later one *)
        rewrite (in_range_succ k i (length l) Hne).
        destruct ((k <=? i) && (i <? k + Datatypes.S (length l))) eqn:Hin.
        * apply andb_true_iff in Hin as [Hki _]. apply Nat.leb_le in Hki.
          replace (i - k)%nat with (Datatypes.S (i - Datatypes.S k)) by lia. reflexivity.
        * reflexivity.
  Qed.

  (* The prefix of k + 1 entries. *)
  Lemma firstn_snoc: forall {A: Type} (l: list A) (d: A) (k: nat),
    (k < length l)%nat -> firstn (Datatypes.S k) l = firstn k l ++ [nth k l d].
  Proof.
    intros A l d. induction l as [|a l IH]; intros k Hk; simpl in Hk.
    - lia.
    - destruct k as [|k].
      + reflexivity.
      + change (firstn (Datatypes.S (Datatypes.S k)) (a :: l))
          with (a :: firstn (Datatypes.S k) l).
        rewrite (IH k) by lia. reflexivity.
  Qed.

  (* The new watchers in the watch list of key y are of clause k (watch_first_in, by
     key). *)
  Lemma watch_first_in_key: forall (wl: WatchLists) (k: nat) (ls: list Lit) (y j: nat)
    (c: Lit),
    In (j, c) (tget (watch_first wl k ls) y) -> In (j, c) (tget wl y) \/
      (j = k /\ In c ls).
  Proof.
    intros wl k ls y j c Hin.
    assert (Hy: lit_key (lit_of (Z.of_nat y)) = y).
    { pose proof (key_lit_of (Z.of_nat y)) as Hk. unfold key in Hk. lia. }
    rewrite <- Hy in Hin |- *. apply (watch_first_in wl k ls (lit_of (Z.of_nat y))).
    assumption.
  Qed.
End Model.

(* The index of the first k clauses, and its parts. *)
Definition idx (lss: list (list Lit)) (k: nat): ClauseMap * WatchLists * list nat :=
  index 0 (firstn k lss) (tmake None) (tmake []) [].

Definition icm (p: ClauseMap * WatchLists * list nat): ClauseMap :=
match p with
| (cm, _, _) => cm
end.

Definition iwl (p: ClauseMap * WatchLists * list nat): WatchLists :=
match p with
| (_, wl, _) => wl
end.

Definition ish (p: ClauseMap * WatchLists * list nat): list nat :=
match p with
| (_, _, sh) => sh
end.

(* The context while indexing clause k: all clauses known, the first k watched, nothing
   assigned, and the empty heuristic of the nl literals to decide on. *)
Definition ictx (lss: list (list Lit)) (alls: Table Lit) (nl N rc k: nat): Ctx :=
mkCtx (tmake None) (icm (idx lss (length lss))) (iwl (idx lss k)) (tmake (Pos 0)) 0 0 []
  alls nl 0 [] (tmake no_reason) (tmake 0) 0 (tmake false) (tmake None) N (tmake [])
  (tmake 0) 0 rc (empty_heur nl).

Section Facts.
  Context (lss: list (list Lit)).

  Lemma idx_snoc: forall (k: nat), (k < length lss)%nat ->
    idx lss (Datatypes.S k) =
      (tset (icm (idx lss k)) k (Some (nth k lss [])),
       watch_first (iwl (idx lss k)) k (nth k lss []),
       if length (nth k lss []) <=? 1 then k :: ish (idx lss k) else ish (idx lss k)).
  Proof.
    intros k Hk. unfold idx. rewrite (firstn_snoc _ [] k Hk), index_snoc.
    rewrite length_firstn, Nat.min_l by lia. cbn [Nat.add].
    now destruct (index 0 (firstn k lss) (tmake None) (tmake []) []) as [[cm wl] sh].
  Qed.

  (* The clause map of the index. *)
  Lemma idx_cm: forall (k i: nat), (k <= length lss)%nat ->
    tget (icm (idx lss k)) i = (if i <? k then Some (nth i lss []) else None)%nat.
  Proof.
    intros k i Hk. unfold idx.
    destruct (index 0 (firstn k lss) (tmake None) (tmake []) []) as [[cm wl] sh] eqn:Hix.
    apply (index_cmap _ _ _ _ _ _ _ _ i) in Hix as Hc. cbn [icm].
    rewrite Hc, length_firstn.
    rewrite Nat.min_l by lia. rewrite !tget_tmake, Nat.sub_0_r.
    cbn [Nat.leb andb Nat.add].
    destruct (Nat.ltb_spec i k).
    - rewrite nth_firstn.
      replace (i <? k)%nat with true by (symmetry; now apply Nat.ltb_lt). reflexivity.
    - reflexivity.
  Qed.

  (* The watch lists of the index hold watchers of earlier clauses, and the short clauses
     are earlier and fewer. *)
  Lemma idx_lists: forall (k: nat), (k <= length lss)%nat ->
    (forall (y i: nat) (b: Lit), In (i, b) (tget (iwl (idx lss k)) y) -> (i < k)%nat) /\
    (forall (i: nat), In i (ish (idx lss k)) -> (i < k)%nat) /\
    (length (ish (idx lss k)) <= k)%nat.
  Proof.
    intros k. induction k as [|k IH]; intros Hk.
    - unfold idx. cbn. split.
      + intros y i b. rewrite tget_tmake. intros [].
      + split.
        * intros i [].
        * lia.
    - destruct IH as (Hwl & Hsh & Hlen).
      { lia. }
      rewrite (idx_snoc k) by lia. cbn [iwl ish]. split.
      + (* the watch lists gained watchers of clause k *)
        intros y i b Hi. apply watch_first_in_key in Hi as [Hi | [-> _]].
        * apply Hwl in Hi. lia.
        * lia.
      + destruct (length (nth k lss []) <=? 1)%nat; cbn [In length].
        * split.
          -- intros i [<- | Hi].
             ++ lia.
             ++ apply Hsh in Hi. lia.
          -- lia.
        * split.
          -- intros i Hi. apply Hsh in Hi. lia.
          -- lia.
  Qed.
End Facts.

(* Indexing clause k: its first literals watch it. *)
Lemma ictx_step: forall (lss: list (list Lit)) (alls: Table Lit) (nl N rc k: nat),
  (k < length lss)%nat ->
  ictx lss alls nl N rc (Datatypes.S k) =
  mkCtx (tmake None) (icm (idx lss (length lss)))
    (watch_first (iwl (idx lss k)) k (nth k lss [])) (tmake (Pos 0)) 0 0 [] alls nl 0 []
    (tmake no_reason) (tmake 0) 0 (tmake false) (tmake None) N (tmake [])
    (tmake 0) 0 rc (empty_heur nl).
Proof.
  intros lss alls nl N rc k Hk. unfold ictx. rewrite (idx_snoc lss k Hk). reflexivity.
Qed.

(* The parts of index_clauses proved in lemmas of their own: the loop, its body after the
   test, and in the body the watchers of the clause and the bookkeeping of a short
   clause. *)
Definition index_loop: statement := first_stmt (drop_stmts 2 (fn_body f_index_clauses)).
Definition index_body: statement := drop_stmts 1 (loop_body index_loop).
Definition index_watch: statement := first_stmt (drop_stmts 2 index_body).
Definition index_short: statement := drop_stmts 3 index_body.

(* A call of wpush, which C makes in three places, with the temporary tr for its result:
   if (!wpush(s, ta, k, tb)) return -1; *)
Definition push_stmt (tr ta tb: ident): statement :=
  Ssequence
    (Scall (Some tr)
      (Evar _wpush (Tfunction ((tptr (Tstruct _solver noattr)) :: tint :: tint :: tint ::
                               nil) tint cc_default))
      ((Etempvar _s (tptr (Tstruct _solver noattr))) :: (Etempvar ta tint) ::
       (Etempvar _k tint) :: (Etempvar tb tint) :: nil))
    (Sifthenelse (Eunop Onotbool (Etempvar tr tint) tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
      Sskip).

(* The invariant of the loop of index_clauses at clause k: the temporaries hold s, k and
   the number ns of short clauses among the first k, the memory represents the context
   with the first k clauses watched, and the array ts holds their short clauses. *)
Record IndexInv (S: Shape) (N: nat) (lss: list (list Lit)) (al: Table Lit) (nl rc: nat)
  (ts: nat -> Z) (k: nat) (le: temp_env) (m1: mem): Prop := {
  xi_s: le ! _s = Some (sptr S);
  xi_k: le ! _k = Some (vint (Z.of_nat k));
  xi_ns: le ! _ns = Some (vint (Z.of_nat (length (ish (idx lss k)))));
  xi_le: k <= length lss;
  xi_rep: Rep m1 S N lss (ictx lss al nl N rc k) [];
  xi_shorts: Arr m1 (b_shorts S) (length lss) ts;
  xi_ts: forall (q: nat), q < length (ish (idx lss k)) ->
    ts q = Z.of_nat (nth q (rev (ish (idx lss k))) 0);
}.

Definition index_inv (S: Shape) (N: nat) (lss: list (list Lit)) (al: Table Lit)
  (nl rc k: nat) (le: temp_env) (m1: mem): Prop :=
  exists (ts: nat -> Z), IndexInv S N lss al nl rc ts k le m1.

Definition index_variant (lss: list (list Lit)): nat -> nat -> Prop :=
  ltof nat (fun (k: nat) => length lss - k).

(* What the loop of index_clauses ends in: every clause indexed, or out of room. *)
Definition IndexPost (S: Shape) (N: nat) (lss: list (list Lit)) (al: Table Lit)
  (nl rc: nat) (le: temp_env) (m: mem) (out: outcome): Prop :=
  (out = Out_normal /\ index_inv S N lss al nl rc (length lss) le m) \/
  out = Out_return (Some (vint (-1), Ctypesdefs.tint)).

(* What must hold after the watchers of clause k: the loop goes on, or index_clauses
   returns -1. *)
Definition IndexK (S: Shape) (N: nat) (lss: list (list Lit)) (al: Table Lit) (nl rc: nat)
  (k: nat): temp_env -> mem -> outcome -> Prop :=
  LoopK (index_variant lss) (index_inv S N lss al nl rc) (IndexPost S N lss al nl rc) k.

(* The state of the loop body of clause k: the temporaries also hold len, and the memory
   represents x with the pool tp. *)
Record IndexAt (S: Shape) (N: nat) (lss: list (list Lit)) (ts tp: nat -> Z) (k: nat)
  (x: Ctx) (le: temp_env) (m: mem): Prop := {
  ia_s: le ! _s = Some (sptr S);
  ia_k: le ! _k = Some (vint (Z.of_nat k));
  ia_ns: le ! _ns = Some (vint (Z.of_nat (length (ish (idx lss k)))));
  ia_len: le ! _len = Some (vint (Z.of_nat (starts S (Datatypes.S k) - starts S k)));
  ia_lt: k < length lss;
  ia_rep: RepB m S N lss x [];
  ia_pool: Arr m (b_wpool S) (2 * npool S) tp;
  ia_poolof: PoolOf S N tp (wls x) (fun (_ _: nat) => False);
  ia_shorts: Arr m (b_shorts S) (length lss) ts;
  ia_ts: forall (q: nat), q < length (ish (idx lss k)) ->
    ts q = Z.of_nat (nth q (rev (ish (idx lss k))) 0);
}.

(* Clause k of the context while indexing is clause k of lss, at its range of clits. *)
Lemma ictx_clause: forall (m: mem) (S: Shape) (N: nat) (lss: list (list Lit))
  (al: Table Lit) (nl rc j k: nat) (x: Ctx),
  RepB m S N lss x [] -> cmap x = cmap (ictx lss al nl N rc j) -> k < length lss ->
  tget (cmap x) k = Some (nth k lss []) /\
  length (nth k lss []) = starts S (Datatypes.S k) - starts S k.
Proof.
  intros m S N lss al nl rc j k x HRep Hcm Hk.
  assert (Hcl: tget (cmap x) k = Some (nth k lss [])).
  { rewrite Hcm. cbn [ictx cmap]. rewrite idx_cm by lia.
    replace (k <? length lss) with true by (symmetry; now apply Nat.ltb_lt). reflexivity.
    }
  split.
  - assumption.
  - destruct (a_lits _ _ _ _ _ _ _ HRep) as (t & _ & Hclauses).
    apply (clause_length m S N lss x [] t k).
    + assumption.
    + assumption.
    + assumption.
Qed.

(* The end of the loop body of clause k: a short clause is added to the array; and k++.

     {{ IndexAt (ictx (k + 1)) }}
       if (len <= 1) { s->shorts[ns] = k; ns++; }              (rep_store_short_entry)
       k++;
     {{ IndexInv (k + 1) }}                                                            *)
Lemma index_short_correct: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (al: Table Lit) (nl rc: nat) (ts tp: nat -> Z) (k: nat) (le: temp_env) (m: mem),
  IndexAt S N lss ts tp k (ictx lss al nl N rc (Datatypes.S k)) le m ->
  Exec ge le m index_short (IndexK S N lss al nl rc k).
Proof.
  intros S N lss al nl rc ts tp k le m HA.
  destruct HA as [Hs Hk Hns Hlen Hlt HRep Apool Hpool Ats Hts].
  pose proof (r_lss_small _ _ _ _ _ _ _ HRep) as Hlss.
  pose proof (r_nclits_small _ _ _ _ _ _ _ HRep) as Hncl.
  pose proof (Rep.r_starts _ _ _ _ _ _ _ HRep k Hlt) as Hrange.
  pose proof (idx_lists lss k (Nat.lt_le_incl _ _ Hlt)) as (Hwl & Hshk & Hshl).
  destruct (ictx_clause m S N lss al nl rc (Datatypes.S k) k _ HRep eq_refl Hlt)
    as [_ Hlen_cl].
  assert (Hshn: ish (idx lss (Datatypes.S k)) =
                if Nat.leb (length (nth k lss [])) 1 then k :: ish (idx lss k)
                else ish (idx lss k)).
  { rewrite (idx_snoc lss k Hlt). reflexivity. }
  assert (Hadd: Int.add (Int.repr (Z.of_nat k)) (Int.repr 1)
                = Int.repr (Z.of_nat (Datatypes.S k))).
  { rewrite add_repr. f_equal. lia. }
  rewrite Hlen_cl in Hshn.
  unfold index_short, index_body, index_loop, f_index_clauses.
  cbn [fn_body drop_stmts first_stmt loop_body Swhile].
  (* if (len <= 1) *)
  apply exec_seq. eapply (exec_if_cmp _ _ _ Cle _ _ _ 1).
  - ev.
  - ev.
  - reflexivity.
  - reflexivity.
  - unfold Small. lia.
  - unfold Small. lia.
  - destruct (Nat.leb_spec (starts S (Datatypes.S k) - starts S k) 1) as [Hsh | Hsh].
    + (* a short clause: s->shorts[ns] = k; ns++; *)
      replace (zcmp Cle (Z.of_nat (starts S (Datatypes.S k) - starts S k)) 1) with true
        by (symmetry; cbn [zcmp]; apply Z.leb_le; lia).
      assert (Hns1: Int.add (Int.repr (Z.of_nat (length (ish (idx lss k))))) (Int.repr 1)
                    = Int.repr (Z.of_nat (length (ish (idx lss (Datatypes.S k)))))).
      { rewrite Hshn, add_repr. f_equal. cbn [length]. lia. }
      assert (Hnsk: length (ish (idx lss k)) < length lss) by lia.
      pose proof (Rep.r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
      pose proof (Rep.r_shorts _ _ _ _ _ _ _ HRep) as Fsh.
      cbv beta iota. run. eapply exec_store.
      * evl.
      * ev.
      * reflexivity.
      * reflexivity.
      * ofs. bound.
      * ofs. cbn [cast_int_int].
        destruct (arr_storable m (b_shorts S) (length lss) (length (ish (idx lss k))) ts
                    (Z.of_nat k) Ats Hnsk) as [m1 Hst1].
        exists m1. split.
        -- apply Hst1.
        -- normal. run. ints. apply loopk_next with (Datatypes.S k).
           ++ unfold index_variant, ltof. lia.
           ++ exists (fun (j: nat) =>
                        if Nat.eqb (length (ish (idx lss k))) j then Z.of_nat k
                        else ts j).
              constructor.
              ** tmp.
              ** tmp.
              ** tmp.
              ** lia.
              ** split.
                 --- apply (rep_store_short_entry m m1 S N lss _ [] ts
                              (length (ish (idx lss k))) (Z.of_nat k) HRep).
                     +++ reflexivity.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                 --- exists tp. split.
                     +++ apply (arr_store_other _ _ _ _ _ _ _ _ _ Apool Hst1). neq Hnd.
                     +++ assumption.
              ** apply (arr_store m m1 (b_shorts S) (length lss) _ ts (Z.of_nat k)
                          Ats Hnsk Hst1).
              ** (* clause k is the newest short clause *)
                 intros q Hq. rewrite Hshn in Hq |- *. cbn [length rev] in Hq |- *.
                 destruct (Nat.eq_dec (length (ish (idx lss k))) q) as [<- | Hne].
                 --- rewrite Nat.eqb_refl, <- length_rev, nth_middle. reflexivity.
                 --- replace (Nat.eqb (length (ish (idx lss k))) q) with false
                       by (symmetry; now apply Nat.eqb_neq).
                     rewrite app_nth1 by (rewrite length_rev; lia). apply Hts. lia.
    + (* not a short clause: k++; *)
      replace (zcmp Cle (Z.of_nat (starts S (Datatypes.S k) - starts S k)) 1) with false
        by (symmetry; cbn [zcmp]; apply Z.leb_gt; lia).
      cbv beta iota. run. ints. apply loopk_next with (Datatypes.S k).
      * unfold index_variant, ltof. lia.
      * exists ts. constructor.
        -- tmp.
        -- tmp.
        -- rewrite Hshn. tmp.
        -- lia.
        -- split.
           ++ assumption.
           ++ exists tp. split; assumption.
        -- assumption.
        -- rewrite Hshn. assumption.
Qed.

(* One watcher of clause k: appending (k, bl) to the watch list of l, with the temporaries
   ta and tb holding l and bl, and tr for the result of wpush:

     {{ RepB x /\ the pool tp holds the watch lists of x }}
       if (!wpush(s, ta, k, tb)) return -1;                           (wpush_correct)
     {{ result = -1 (out of room) }}
     {{ RepB (set_watching x l (watching l ++ [(k, bl)])), and its pool }}            *)
Lemma index_push_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (k: nat) (l bl: Lit) (tp: nat -> Z) (tr ta tb: ident) (le: temp_env) (m: mem)
  (Q: temp_env -> mem -> outcome -> Prop),
  RepB m S N lss x [] -> Arr m (b_wpool S) (2 * npool S) tp ->
  PoolOf S N tp (wls x) (fun (_ _: nat) => False) ->
  le ! _s = Some (sptr S) -> le ! ta = Some (vint (key l)) ->
  le ! _k = Some (vint (Z.of_nat k)) -> le ! tb = Some (vint (key bl)) ->
  (extract l < N)%nat -> k < length lss -> (extract bl < N)%nat ->
  (forall (le': temp_env) (m': mem),
     Q le' m' (Out_return (Some (vint (-1), Ctypesdefs.tint)))) ->
  (forall (m': mem) (tp': nat -> Z),
     RepB m' S N lss (set_watching x l (watching (wls x) l ++ [(k, bl)])) [] ->
     Arr m' (b_wpool S) (2 * npool S) tp' ->
     PoolOf S N tp' (tset (wls x) (lit_key l) (watching (wls x) l ++ [(k, bl)]))
       (fun (_ _: nat) => False) ->
     Mem.unchanged_on (fun (b: block) (_: Z) => b <> b_wpool S /\ b <> b_wlen S) m m' ->
     Q (PTree.set tr (vint 1) le) m' Out_normal) ->
  Exec ge le m (push_stmt tr ta tb) Q.
Proof.
  intros S N lss x k l bl tp tr ta tb le m Q HRep Apool Hpool Hs Hta Hk Htb Hl Hkl Hbl
    Hfail Hok.
  unfold push_stmt. apply exec_seq. call wpush_fun. eapply call_weaken.
  - apply (wpush_correct S N lss x [] l k bl tp (fun _ _ => False) m).
    split.
    + assumption.
    + split.
      * assumption.
      * split.
        -- assumption.
        -- split.
           ++ intros q [].
           ++ split.
              ** assumption.
              ** split.
                 --- assumption.
                 --- assumption.
  - intros m' v Hv. normal.
    destruct Hv as [-> | (-> & HRep' & Apool' & Hpool' & Hun)].
    + (* out of room: return -1; *)
      eapply (exec_if_int _ _ _ _ 1).
      * ev.
      * reflexivity.
      * unfold Small. lia.
      * change (negb (Z.eqb 1 0)) with true. cbv beta iota. eapply exec_return.
        -- ev.
        -- apply Hfail.
    + eapply (exec_if_int _ _ _ _ 0).
      * ev.
      * reflexivity.
      * unfold Small. lia.
      * change (negb (Z.eqb 0 0)) with false. cbv beta iota. apply exec_skip.
        eapply Hok.
        -- assumption.
        -- eassumption.
        -- assumption.
        -- assumption.
Qed.

(* The watchers of clause k, by its length:

     {{ IndexAt (ictx k) /\ b, the start of clause k, in the temporaries }}
       if (len >= 2) { int a = s->clits[b]; int c = s->clits[b + 1];
                       push (a, k, c); push (c, k, a); }        (index_push_correct)
       else if (len == 1) { int a = s->clits[b]; push (a, k, a); }
     {{ result = -1 (out of room) }}
     {{ IndexAt (ictx (k + 1)) }}                                           (ictx_step)
       ...                                                       (index_short_correct) *)
Lemma index_watch_correct: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (al: Table Lit) (nl rc: nat) (ts tp: nat -> Z) (k: nat) (le: temp_env) (m: mem),
  IndexAt S N lss ts tp k (ictx lss al nl N rc k) le m ->
  le ! _b = Some (vint (Z.of_nat (starts S k))) ->
  Exec ge le m index_watch (SeqK ge index_short (IndexK S N lss al nl rc k)).
Proof.
  intros S N lss al nl rc ts tp k le m HA Hb. pose proof HA as HA'.
  destruct HA' as [Hs Hk Hns Hlen Hlt HRep Apool Hpool Ats Hts].
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_nclits_small _ _ _ _ _ _ _ HRep) as Hncl.
  pose proof (Rep.r_starts _ _ _ _ _ _ _ HRep k Hlt) as Hrange.
  pose proof (r_clits _ _ _ _ _ _ _ HRep) as Fclits.
  pose proof (a_lits _ _ _ _ _ _ _ HRep) as (tl & Alits & Hclauses).
  destruct (ictx_clause m S N lss al nl rc k k _ HRep eq_refl Hlt) as [Hcls Hlen_cl].
  (* What is left after the watchers: IndexAt for ictx (k + 1) *)
  assert (Hnext: forall (le': temp_env) (m': mem) (tp': nat -> Z),
    le' ! _s = Some (sptr S) -> le' ! _k = Some (vint (Z.of_nat k)) ->
    le' ! _ns = Some (vint (Z.of_nat (length (ish (idx lss k))))) ->
    le' ! _len = Some (vint (Z.of_nat (starts S (Datatypes.S k) - starts S k))) ->
    RepB m' S N lss (ictx lss al nl N rc (Datatypes.S k)) [] ->
    Arr m' (b_wpool S) (2 * npool S) tp' ->
    PoolOf S N tp' (wls (ictx lss al nl N rc (Datatypes.S k)))
      (fun (_ _: nat) => False) ->
    Mem.unchanged_on (fun (b: block) (_: Z) => b <> b_wpool S /\ b <> b_wlen S) m m' ->
    SeqK ge index_short (IndexK S N lss al nl rc k) le' m' Out_normal).
  { intros le' m' tp' Hs' Hk' Hns' Hlen' HRep' Apool' Hpool' Hun. normal.
    apply (index_short_correct S N lss al nl rc ts tp' k). constructor.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - apply (arr_unchanged _ m m' (b_shorts S) (length lss) ts Hun).
      + intros ofs. split.
        * neq Hnd.
        * neq Hnd.
      + assumption.
    - assumption. }
  assert (Hfail: forall (le': temp_env) (m': mem),
    SeqK ge index_short (IndexK S N lss al nl rc k) le' m'
      (Out_return (Some (vint (-1), Ctypesdefs.tint)))).
  { intros le' m'. abrupt. apply loopk_return. right. reflexivity. }
  unfold index_watch, index_body, index_loop, f_index_clauses.
  cbn [fn_body drop_stmts first_stmt loop_body Swhile].
  (* if (len >= 2) *)
  eapply (exec_if_cmp _ _ _ Cge _ _ _ 2).
  - ev.
  - ev.
  - reflexivity.
  - reflexivity.
  - unfold Small. lia.
  - unfold Small. lia.
  - destruct (nth k lss []) as [|c0 [|c1 ls]] eqn:Hcl.
    + (* the empty clause: no watcher *)
      replace (zcmp Cge (Z.of_nat (starts S (Datatypes.S k) - starts S k)) 2) with false
        by (symmetry; cbn [zcmp]; apply Z.leb_gt; cbn [length] in Hlen_cl; lia).
      cbv beta iota. eapply (exec_if_cmp _ _ _ Ceq _ _ _ 1).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * replace (zcmp Ceq (Z.of_nat (starts S (Datatypes.S k) - starts S k)) 1) with false
          by (symmetry; cbn [zcmp]; apply Z.eqb_neq; cbn [length] in Hlen_cl; lia).
        cbv beta iota. apply exec_skip. apply (Hnext le m tp).
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- rewrite ictx_step by assumption. rewrite Hcl. apply HRep.
        -- assumption.
        -- rewrite ictx_step by assumption. rewrite Hcl. apply Hpool.
        -- apply Mem.unchanged_on_refl.
    + (* a unit clause [c0]: watched by c0 *)
      replace (zcmp Cge (Z.of_nat (starts S (Datatypes.S k) - starts S k)) 2) with false
        by (symmetry; cbn [zcmp]; apply Z.leb_gt; cbn [length] in Hlen_cl; lia).
      cbv beta iota. eapply (exec_if_cmp _ _ _ Ceq _ _ _ 1).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * replace (zcmp Ceq (Z.of_nat (starts S (Datatypes.S k) - starts S k)) 1) with true
          by (symmetry; cbn [zcmp]; apply Z.eqb_eq; cbn [length] in Hlen_cl; lia).
        destruct (clause_lit m S N lss _ [] tl k 0 [c0] HRep Hclauses Hlt Hcls)
          as (Hpos0 & Htl0 & Hc0).
        { cbn [length]. lia. }
        cbn [nth] in Htl0, Hc0. rewrite Nat.add_0_r in Htl0, Hpos0.
        pose proof (key_small c0 N Hc0 HN) as Hkc0.
        cbv beta iota. fold (push_stmt _t'3 _a__1 _a__1). run. rewrite Htl0.
        apply (index_push_correct S N lss
          (ictx lss al nl N rc k) k c0 c0 tp _t'3 _a__1 _a__1).
        -- assumption.
        -- assumption.
        -- assumption.
        -- tmp.
        -- tmp.
        -- tmp.
        -- tmp.
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- intros m' tp' HRep' Apool' Hpool' Hun. apply Hnext with tp'.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ rewrite ictx_step by assumption. rewrite Hcl. apply HRep'.
           ++ assumption.
           ++ rewrite ictx_step by assumption. rewrite Hcl. apply Hpool'.
           ++ assumption.
    + (* two literals or more: watched by c0 and c1, each with the other as blocker *)
      replace (zcmp Cge (Z.of_nat (starts S (Datatypes.S k) - starts S k)) 2) with true
        by (symmetry; cbn [zcmp]; apply Z.leb_le; cbn [length] in Hlen_cl; lia).
      destruct (clause_lit m S N lss _ [] tl k 0 (c0 :: c1 :: ls) HRep Hclauses Hlt Hcls)
        as (Hpos0 & Htl0 & Hc0).
      { cbn [length]. lia. }
      destruct (clause_lit m S N lss _ [] tl k 1 (c0 :: c1 :: ls) HRep Hclauses Hlt Hcls)
        as (Hpos1 & Htl1 & Hc1).
      { cbn [length]. lia. }
      cbn [nth] in Htl0, Hc0, Htl1, Hc1. rewrite Nat.add_0_r in Htl0, Hpos0.
      pose proof (key_small c0 N Hc0 HN) as Hkc0.
      pose proof (key_small c1 N Hc1 HN) as Hkc1.
      assert (Hb1: Int.add (Int.repr (Z.of_nat (starts S k))) (Int.repr 1)
                   = Int.repr (Z.of_nat (starts S k + 1))).
      { rewrite add_repr. f_equal. lia. }
      cbv beta iota. fold (push_stmt _t'1 _a _c) (push_stmt _t'2 _c _a).
      run. rewrite Htl0. run. rewrite Htl1.
      apply (index_push_correct S N lss (ictx lss al nl N rc k) k c0 c1 tp _t'1 _a _c).
      * assumption.
      * assumption.
      * assumption.
      * tmp.
      * tmp.
      * tmp.
      * tmp.
      * assumption.
      * assumption.
      * assumption.
      * intros le' m'. abrupt. apply Hfail.
      * intros m1 tp1 HRep1 Apool1 Hpool1 Hun1. normal.
        set (x1 := set_watching (ictx lss al nl N rc k) c0
                     (watching (wls (ictx lss al nl N rc k)) c0 ++ [(k, c1)])) in *.
        apply (index_push_correct S N lss x1 k c1 c0 tp1 _t'2 _c _a).
        -- assumption.
        -- assumption.
        -- assumption.
        -- tmp.
        -- tmp.
        -- tmp.
        -- tmp.
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- intros m2 tp2 HRep2 Apool2 Hpool2 Hun2. apply Hnext with tp2.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ rewrite ictx_step by assumption. rewrite Hcl. apply HRep2.
           ++ assumption.
           ++ rewrite ictx_step by assumption. rewrite Hcl. apply Hpool2.
           ++ apply (Mem.unchanged_on_trans _ m m1 m2).
              ** assumption.
              ** assumption.
Qed.

(* The loop body of clause k: the range of the clause, then its watchers.

     {{ IndexInv k /\ k < ncl }}
       int b = s->cstart[k];
       int len = s->cstart[k + 1] - b;
     {{ IndexAt (ictx k) /\ b }}
       ...                                                       (index_watch_correct) *)
Lemma index_body_correct: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (al: Table Lit) (nl rc: nat) (ts: nat -> Z) (k: nat) (le: temp_env) (m: mem),
  k < length lss -> IndexInv S N lss al nl rc ts k le m ->
  Exec ge le m index_body (IndexK S N lss al nl rc k).
Proof.
  intros S N lss al nl rc ts k le m Hlt HI.
  destruct HI as [Hs Hk Hns Hkl [HRep [tp [Apool Hpool]]] Ats Hts].
  pose proof (r_lss_small _ _ _ _ _ _ _ HRep) as Hlss.
  pose proof (r_nclits_small _ _ _ _ _ _ _ HRep) as Hncl.
  pose proof (Rep.r_starts _ _ _ _ _ _ _ HRep k Hlt) as Hrange.
  pose proof (r_cstart _ _ _ _ _ _ _ HRep) as Fcstart.
  pose proof (a_starts _ _ _ _ _ _ _ HRep) as Astarts.
  assert (Hadd: Int.add (Int.repr (Z.of_nat k)) (Int.repr 1)
                = Int.repr (Z.of_nat (Datatypes.S k))).
  { rewrite add_repr. f_equal. lia. }
  assert (Hsub: Int.sub (Int.repr (Z.of_nat (starts S (Datatypes.S k))))
                  (Int.repr (Z.of_nat (starts S k)))
                = Int.repr (Z.of_nat (starts S (Datatypes.S k) - starts S k))).
  { rewrite sub_repr. f_equal. lia. }
  unfold index_body, index_loop, f_index_clauses.
  cbn [fn_body drop_stmts first_stmt loop_body Swhile].
  (* int b = s->cstart[k]; int len = s->cstart[k + 1] - b; *)
  run. ints. clear Fcstart Astarts.
  apply (index_watch_correct S N lss al nl rc ts tp k).
  - constructor.
    + tmp.
    + tmp.
    + tmp.
    + tmp.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
  - tmp.
Qed.

(* The loop of index_clauses, over the clauses:

     {{ IndexInv 0 }}
       while (k < s->ncl) { ... }                                 (index_body_correct)
     {{ IndexInv ncl }}

   The loop ends: length lss - k decreases. *)
Lemma index_loop_correct: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (al: Table Lit) (nl rc: nat) (le: temp_env) (m: mem),
  (1 <= N)%nat -> index_inv S N lss al nl rc 0 le m ->
  Exec ge le m index_loop (IndexPost S N lss al nl rc).
Proof.
  intros S N lss al nl rc le m HN1 HI0.
  unfold index_loop, f_index_clauses. cbn [fn_body drop_stmts first_stmt].
  apply exec_loop with (R := index_variant lss) (I := index_inv S N lss al nl rc)
    (a := 0).
  - apply well_founded_ltof.
  - intros k le1 m1 [ts HI]. pose proof HI as HI'.
    destruct HI' as [Hs Hk Hns Hkl [HRep [tp [Apool Hpool]]] Ats Hts].
    pose proof (r_lss_small _ _ _ _ _ _ _ HRep) as Hlss.
    pose proof (Rep.r_ncl _ _ _ _ _ _ _ HRep) as Fncl.
    (* if (k < s->ncl) ... else break; *)
    run. eapply (exec_if_cmp _ _ _ Clt).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + unfold Small. lia.
    + unfold Small. lia.
    + destruct (Nat.lt_ge_cases k (length lss)) as [Hlt | Hge].
      * (* k < ncl: the body *)
        replace (zcmp Clt (Z.of_nat k) (Z.of_nat (length lss))) with true
          by (symmetry; cbn [zcmp]; apply Z.ltb_lt; lia).
        cbv beta iota. apply exec_skip. normal. clear Fncl.
        apply (index_body_correct S N lss al nl rc ts k).
        -- assumption.
        -- constructor.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ assumption.
           ++ split.
              ** assumption.
              ** exists tp. split; assumption.
           ++ assumption.
           ++ assumption.
      * (* k = ncl: break; every clause is indexed *)
        replace (zcmp Clt (Z.of_nat k) (Z.of_nat (length lss))) with false
          by (symmetry; cbn [zcmp]; apply Z.ltb_ge; lia).
        cbv beta iota. apply exec_break. abrupt. apply loopk_break. left. split.
        -- reflexivity.
        -- replace k with (length lss) in * by lia. exists ts. constructor.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ lia.
           ++ split.
              ** assumption.
              ** exists tp. split; assumption.
           ++ assumption.
           ++ assumption.
  - assumption.
Qed.

(* index_clauses watches the first literals of every clause and collects the short ones:

     {{ Rep (ictx ... 0) /\ Arr shorts tsh }}
       int k = 0;
       int ns = 0;
       while (k < s->ncl) { ... }                                 (index_loop_correct)
     {{ result = -1 (out of room) }}
       return ns;
     {{ result = the number of short clauses /\ Rep (ictx ... ncl) /\
        they are in shorts }}                                                          *)
Lemma index_clauses_correct: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (al: Table Lit) (nl rc: nat) (tsh: nat -> Z),
  {{ m | Rep m S N lss (ictx lss al nl N rc 0) [] /\
    Arr m (b_shorts S) (length lss) tsh /\ (1 <= N)%nat }}
    f_index_clauses(sptr S)
  {{ m', v | v = vint (-1) \/ exists (tsh': nat -> Z),
             v = vint (Z.of_nat (length (ish (idx lss (length lss))))) /\
             Rep m' S N lss (ictx lss al nl N rc (length lss)) [] /\
             Arr m' (b_shorts S) (length lss) tsh' /\
             forall (q: nat), q < length (ish (idx lss (length lss))) ->
               tsh' q = Z.of_nat (nth q (rev (ish (idx lss (length lss)))) 0) }}.
Proof.
  intros S N lss al nl rc tsh m (HRep & Ash & HN1).
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_index_clauses. cbn [fn_body fn_return].
    (* int k = 0; int ns = 0; *)
    run. apply exec_weaken with (Q := IndexPost S N lss al nl rc).
    + apply (index_loop_correct S N lss al nl rc).
      * assumption.
      * exists tsh. constructor.
        -- tmp.
        -- tmp.
        -- tmp.
        -- lia.
        -- assumption.
        -- assumption.
        -- intros q Hq. cbn in Hq. lia.
    + intros le' m' out [[-> [ts HI]] | ->].
      * (* return ns; *)
        destruct HI as [Hs Hk Hns Hkl HRep' Ats Hts]. normal. eapply exec_return.
        -- ev.
        -- exists (vint (Z.of_nat (length (ish (idx lss (length lss)))))). split.
           ++ apply result_int.
           ++ right. exists ts. split.
              ** reflexivity.
              ** split.
                 --- assumption.
                 --- split; assumption.
      * (* out of room *)
        abrupt. exists (vint (-1)). split.
        -- apply result_int.
        -- now left.
Qed.

Lemma index_clauses_fun: exists (b: block),
  Genv.find_symbol ge _index_clauses = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_index_clauses).
Proof. apply find_fun. reflexivity. Qed.
