(* index_clauses watches the first literals of the clauses and collects the short ones
   (index), or gives up. *)
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
From compcert Require Import Ctypesdefs.
From compcert Require Import Clight.
From compcert Require Import ClightBigstep.

From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Tactics.
From RocqSAT.refinement Require Import Table.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import Heur.
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement Require Import Step.
From RocqSAT.refinement.c Require Import Arrays.
From RocqSAT.refinement.c Require Import Logic.
From RocqSAT.refinement.c Require Import Common.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Rep.
From RocqSAT.refinement.c Require Import Wpush.
Local Open Scope nat_scope.

Section Model.
  (* Indexing l1 ++ [ls] from position k: index l1, then add ls at k + length l1. *)
  Lemma index_snoc: forall (l1: list (list Lit)) (ls: list Lit) (k: nat) (cm: ClauseMap)
    (wl: WatchLists) (ss: list nat),
    index k (l1 ++ [ls]) cm wl ss =
    match index k l1 cm wl ss with
    | (cm', wl', ss') =>
      (tset cm' (k + length l1) (Some ls), watch_first wl' (k + length l1) ls,
       if length ls <=? 1 then (k + length l1) :: ss' else ss')
    end.
  Proof.
    intros l1. induction l1 as [|ls1 l1 IH]; intros ls k cm wl ss; simpl.
    - now rewrite Nat.add_0_r.
    - rewrite IH.
      now replace (S k + length l1)%nat with (k + S (length l1))%nat
        by lia.
  Qed.

  (* Position i is in the range of n + 1 positions from k, but not k itself, exactly when
     it is in the range of n positions from k + 1. *)
  Lemma in_range_succ: forall (k i n: nat), k <> i ->
    ((S k <=? i) && (i <? S k + n)) =
      ((k <=? i) && (i <? k + S n)).
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
    (wl wl': WatchLists) (ss ss': list nat) (i: nat),
    index k l cm wl ss = (cm', wl', ss') ->
    tget cm' i = (if (k <=? i) && (i <? k + length l) then Some (nth (i - k) l [])
                  else tget cm i)%nat.
  Proof.
    intros l. induction l as [|ls l IH]; intros k cm cm' wl wl' ss ss' i Hix;
      simpl in Hix.
    - injection Hix as <- <- <-. cbn [length]. rewrite in_range_empty. reflexivity.
    - apply (IH _ _ _ _ _ _ _ i) in Hix as Hc. rewrite Hc. rewrite tget_tset.
      cbn [length]. destruct (Nat.eq_dec k i) as [<- | Hne].
      + (* the first clause of the list is at position k *)
        rewrite Nat.leb_refl, Nat.sub_diag.
        replace (S k <=? k)%nat with false
          by (symmetry; apply Nat.leb_gt; lia).
        replace (k <? k + S (length l))%nat with true
          by (symmetry; apply Nat.ltb_lt; lia).
        reflexivity.
      + (* a later one *)
        rewrite (in_range_succ k i (length l) Hne).
        destruct ((k <=? i) && (i <? k + S (length l))) eqn:Hin.
        * apply andb_true_iff in Hin as [Hki _]. apply Nat.leb_le in Hki.
          replace (i - k)%nat with (S (i - S k)) by lia. reflexivity.
        * reflexivity.
  Qed.
  #[global] Arguments index_cmap {l k cm cm' wl wl' ss ss'}.

  (* The first k + 1 entries: the first k and entry k. *)
  Lemma firstn_snoc: forall {A: Type} (l: list A) (d: A) (k: nat),
    (k < length l)%nat -> firstn (S k) l = firstn k l ++ [nth k l d].
  Proof.
    intros A l d. induction l as [|a l IH]; intros k Hk; simpl in Hk.
    - lia.
    - destruct k as [|k].
      + reflexivity.
      + change (firstn (S (S k)) (a :: l))
          with (a :: firstn (S k) l).
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
| (_, _, ss) => ss
end.

(* The context while indexing clause k: all clauses known, the first k watched, nothing
   assigned, and the empty heuristic of the nl literals to decide on. *)
Definition ictx (lss: list (list Lit)) (alls: Table Lit) (nl N rc k: nat): Ctx :=
mkCtx (tmake None) (icm (idx lss (length lss))) (iwl (idx lss k)) (tmake (Pos 0)) 0 0 []
  alls nl 0 [] [] (tmake no_reason) (tmake 0) 0 (tmake false) [] (tmake None) N
  (tmake []) (tmake 0) 0 rc (empty_heur nl).

Section Facts.
  Context (lss: list (list Lit)).

  (* Indexing clause k: it joins the clause map, its first literals watch it, and it is
     short when it has at most one literal. *)
  Lemma idx_snoc: forall (k: nat), (k < length lss)%nat ->
    idx lss (S k) =
      (tset (icm (idx lss k)) k (Some (nth k lss [])),
       watch_first (iwl (idx lss k)) k (nth k lss []),
       if length (nth k lss []) <=? 1 then k :: ish (idx lss k) else ish (idx lss k)).
  Proof.
    intros k Hk. unfold idx. rewrite (firstn_snoc _ [] k Hk), index_snoc.
    rewrite length_firstn, Nat.min_l by lia. cbn [Nat.add].
    now destruct (index 0 (firstn k lss) (tmake None) (tmake []) []) as [[cm wl] ss].
  Qed.

  (* The index of the first k clauses maps i < k to clause i, and others to None. *)
  Lemma idx_cm: forall (k i: nat), (k <= length lss)%nat ->
    tget (icm (idx lss k)) i = (if i <? k then Some (nth i lss []) else None)%nat.
  Proof.
    intros k i Hk. unfold idx.
    destruct (index 0 (firstn k lss) (tmake None) (tmake []) []) as [[cm wl] ss] eqn:Hix.
    apply (index_cmap i) in Hix as Hc. cbn [icm].
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
    - unfold idx. cbn. splits.
      + intros y i b. rewrite tget_tmake. intros [].
      + intros i [].
      + lia.
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
  ictx lss alls nl N rc (S k) =
  (ictx lss alls nl N rc k) <| wls := watch_first (iwl (idx lss k)) k (nth k lss []) |>.
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

Section Loop.
  (* A call of index_clauses for the clauses lss of N atoms, with the nl literals al to
     decide on and the room rc for the literals of the reason clauses. *)
  Variables (sh: Shape) (N: nat) (lss: list (list Lit)) (al: Table Lit) (nl rc: nat).

  (* The invariant of the loop of index_clauses at clause k: the temporaries hold s, k
     and the number ns of short clauses among the first k, the memory represents the
     context with the first k clauses watched, and the array ts holds their short
     clauses. *)
  Record IndexInv (ts: nat -> Z) (k: nat) (le: temp_env) (m1: mem): Prop := {
    xi_s: le ! _s = Some (sptr sh);
    xi_k: le ! _k = Some (vnat k);
    xi_ns: le ! _ns = Some (vnat (length (ish (idx lss k))));
    xi_le: k <= length lss;
    xi_rep: Rep m1 sh N lss (ictx lss al nl N rc k);
    xi_shorts: Arr m1 (b_shorts sh) (length lss) ts;
    xi_ts: StackIn ts (ish (idx lss k));
  }.

  (* The invariant of the loop, for some array of short clauses. *)
  Definition index_inv (k: nat) (le: temp_env) (m1: mem): Prop :=
    exists (ts: nat -> Z), IndexInv ts k le m1.

  (* The variant of the loop: the number of clauses left. *)
  Definition index_variant: nat -> nat -> Prop :=
    ltof nat (fun (k: nat) => length lss - k).

  (* What the loop of index_clauses ends in: every clause indexed, or out of room. *)
  Definition IndexPost (le: temp_env) (m: mem) (out: outcome): Prop :=
    (out = Out_normal /\ index_inv (length lss) le m) \/
    out = ret_int (-1).

  (* What must hold after the watchers of clause k: the loop goes on, or index_clauses
     returns -1. *)
  Definition IndexK (k: nat): temp_env -> mem -> outcome -> Prop :=
    LoopK index_variant index_inv IndexPost k.

  (* The state of the loop body of clause k: the temporaries also hold len, and the
     memory represents x with the pool tp. *)
  Record IndexAt (ts tp: nat -> Z) (k: nat) (x: Ctx) (le: temp_env) (m: mem): Prop := {
    ia_s: le ! _s = Some (sptr sh);
    ia_k: le ! _k = Some (vnat k);
    ia_ns: le ! _ns = Some (vnat (length (ish (idx lss k))));
    ia_len: le ! _len = Some (vnat (starts sh (S k) - starts sh k));
    ia_lt: k < length lss;
    ia_rep: RepL m sh N lss x;
    ia_pool: PoolArr m sh tp;
    ia_poolof: PoolFree sh N tp (wls x);
    ia_shorts: Arr m (b_shorts sh) (length lss) ts;
    ia_ts: StackIn ts (ish (idx lss k));
  }.

  (* Clause k of the context while indexing is clause k of lss, at its range of clits. *)
  Lemma ictx_clause: forall (m: mem) (j k: nat) (x: Ctx),
    RepL m sh N lss x -> cmap x = cmap (ictx lss al nl N rc j) -> k < length lss ->
    tget (cmap x) k = Some (nth k lss []) /\
    length (nth k lss []) = starts sh (S k) - starts sh k.
  Proof.
    intros m j k x HRep Hcm Hk.
    assert (Hcl: tget (cmap x) k = Some (nth k lss [])).
    { rewrite Hcm. cbn [ictx cmap]. rewrite idx_cm by lia.
      replace (k <? length lss) with true by (symmetry; now apply Nat.ltb_lt).
      reflexivity. }
    split.
    - assumption.
    - destruct (a_lits HRep) as (t & _ & Hclauses).
      apply (clause_length sh N lss x t k); assumption.
  Qed.

  (* The end of the loop body of clause k: a short clause is added to the array; and k++.

       {{ IndexAt (ictx (k + 1)) }}
         if (len <= 1) { s->shorts[ns] = k; ns++; }              (rep_store_short_entry)
         k++;
       {{ IndexInv (k + 1) }}                                                          *)
  Lemma index_short_correct: forall (ts tp: nat -> Z) (k: nat) (le: temp_env) (m: mem),
    IndexAt ts tp k (ictx lss al nl N rc (S k)) le m ->
    Exec ge le m index_short (IndexK k).
  Proof.
    intros ts tp k le m HA.
    destruct HA as [Hs Hk Hns Hlen Hlt HRep Apool Hpool Ats Hts].
    pose proof (r_lss_small HRep) as Hlss.
    pose proof (r_nclits_small HRep) as Hncl.
    pose proof (Rep.r_starts HRep k Hlt) as Hrange.
    pose proof (idx_lists lss k (Nat.lt_le_incl _ _ Hlt)) as (Hwl & Hshk & Hshl).
    destruct (ictx_clause m (S k) k _ HRep eq_refl Hlt)
      as [_ Hlen_cl].
    assert (Hshn: ish (idx lss (S k)) =
                  if Nat.leb (length (nth k lss [])) 1 then k :: ish (idx lss k)
                  else ish (idx lss k)).
    { rewrite (idx_snoc lss k Hlt). reflexivity. }
    assert (Hadd: Int.add (Int.repr (Z.of_nat k)) (Int.repr 1)
                  = Int.repr (Z.of_nat (S k))).
    { rewrite add_repr. f_equal. lia. }
    rewrite Hlen_cl in Hshn.
    unfold index_short, index_body, index_loop, f_index_clauses.
    cbn [fn_body drop_stmts first_stmt loop_body Swhile].
    (* if (len <= 1) *)
    apply exec_seq. branch.
    - (* a short clause: s->shorts[ns] = k; ns++; *)
      intros Hshort. assert (Hleb: Nat.leb (starts sh (S k) - starts sh k) 1 = true)
        by (apply Nat.leb_le; lia).
      rewrite Hleb in Hshn.
      assert (Hns1: Int.add (Int.repr (Z.of_nat (length (ish (idx lss k))))) (Int.repr 1)
                    = Int.repr (Z.of_nat (length (ish (idx lss (S k)))))).
      { rewrite Hshn, add_repr. f_equal. cbn [length]. lia. }
      assert (Hnsk: length (ish (idx lss k)) < length lss) by lia.
      pose proof (Rep.r_nodup HRep) as Hnd.
      pose proof (Rep.r_shorts HRep) as Fsh.
      run. store Ats Hnsk as m1 Hst1.
      run. ints. apply loopk_next with (S k).
      + unfold index_variant, ltof. lia.
      + exists (fun (j: nat) =>
                  if Nat.eqb (length (ish (idx lss k))) j then Z.of_nat k
                  else ts j).
        constructor.
        * tmp.
        * tmp.
        * tmp.
        * lia.
        * split.
          -- apply (rep_store_short_entry m m1 ts
                      (length (ish (idx lss k))) (Z.of_nat k) HRep).
             ++ reflexivity.
             ++ assumption.
             ++ assumption.
             ++ assumption.
          -- split.
             ++ reflexivity.
             ++ exists tp. split.
                ** apply (arr_store_other Apool Hst1). neq Hnd.
                ** assumption.
        * apply (arr_store Ats Hnsk Hst1).
        * (* clause k is the newest short clause *)
          intros q Hq. rewrite Hshn in Hq |- *. cbn [length rev] in Hq |- *.
          destruct (Nat.eq_dec (length (ish (idx lss k))) q) as [<- | Hne].
          -- rewrite Nat.eqb_refl, <- length_rev, nth_middle. reflexivity.
          -- replace (Nat.eqb (length (ish (idx lss k))) q) with false
               by (symmetry; now apply Nat.eqb_neq).
             rewrite app_nth1 by (rewrite length_rev; lia). apply Hts. lia.
    - (* not a short clause: k++; *)
      intros Hlong. assert (Hleb: Nat.leb (starts sh (S k) - starts sh k) 1 = false)
        by (apply Nat.leb_gt; lia).
      rewrite Hleb in Hshn.
      run. ints. apply loopk_next with (S k).
      + unfold index_variant, ltof. lia.
      + exists ts. constructor.
        * tmp.
        * tmp.
        * rewrite Hshn. tmp.
        * lia.
        * split.
          -- assumption.
          -- split.
             ++ reflexivity.
             ++ exists tp. split; assumption.
        * assumption.
        * rewrite Hshn. assumption.
  Qed.

  (* The temporaries of a call of wpush for clause k: s, k, and ta and tb holding the
     keys of the literal l to watch and its blocker bl. *)
  Record WpushTemps (ta tb: ident) (k: nat) (l bl: Lit) (le: temp_env): Prop := {
    pt_s: le ! _s = Some (sptr sh);
    pt_l: le ! ta = Some (vint (key l));
    pt_k: le ! _k = Some (vnat k);
    pt_bl: le ! tb = Some (vint (key bl));
  }.

  (* One watcher of clause k: appending (k, bl) to the watch list of l, with the
     temporaries ta and tb holding l and bl, and tr for the result of wpush:

       {{ RepL x /\ the pool tp holds the watch lists of x }}
         if (!wpush(s, ta, k, tb)) return -1;                           (wpush_correct)
       {{ result = -1 (out of room) }}
       {{ RepL (set_watching x l (watching l ++ [(k, bl)])), and its pool }}          *)
  Lemma index_push_correct: forall (x: Ctx) (k: nat) (l bl: Lit) (tp: nat -> Z)
    (tr ta tb: ident) (le: temp_env) (m: mem) (Q: temp_env -> mem -> outcome -> Prop),
    RepL m sh N lss x -> PoolArr m sh tp -> PoolFree sh N tp (wls x) ->
    WpushTemps ta tb k l bl le ->
    (extract l < N)%nat -> k < length lss -> (extract bl < N)%nat ->
    (forall (le': temp_env) (m': mem),
       Q le' m' (ret_int (-1))) ->
    (forall (m': mem) (tp': nat -> Z),
       RepL m' sh N lss (set_watching x l (watching (wls x) l ++ [(k, bl)])) ->
       PoolArr m' sh tp' ->
       PoolFree sh N tp' (tset (wls x) (lit_key l) (watching (wls x) l ++ [(k, bl)])) ->
       Mem.unchanged_on (PoolFrame sh)
         m m' ->
       Q (PTree.set tr (vint 1) le) m' Out_normal) ->
    Exec ge le m (push_stmt tr ta tb) Q.
  Proof.
    intros x k l bl tp tr ta tb le m Q HRep Apool Hpool [Hs Hta Hk Htb] Hl Hkl Hbl Hfail
      Hok.
    unfold push_stmt. apply exec_seq.
    call wpush_fun (wpush_correct sh N lss x l k bl tp (fun _ _ => False)).
    - split.
      + assumption.
      + split.
        * assumption.
        * split.
          -- assumption.
          -- split.
             ++ intros q [].
             ++ split.
                ** assumption.
                ** split; assumption.
    - intros m' v Hv. normal.
      destruct Hv as [-> | (-> & HRep' & Apool' & Hpool' & Hun)].
      + (* out of room: return -1; *)
        branch.
        * intros _. eapply exec_return.
          -- ev.
          -- apply Hfail.
        * (* 1 = 0 is impossible *)
          intros Hzero. lia.
      + branch.
        * (* 0 <> 0 is impossible *)
          intros Hnonzero. lia.
        * intros _. apply exec_skip.
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
         ...                                                     (index_short_correct) *)
  Lemma index_watch_correct: forall (ts tp: nat -> Z) (k: nat) (le: temp_env) (m: mem),
    IndexAt ts tp k (ictx lss al nl N rc k) le m ->
    le ! _b = Some (vnat (starts sh k)) ->
    Exec ge le m index_watch (SeqK ge index_short (IndexK k)).
  Proof.
    intros ts tp k le m HA Hb. pose proof HA as HA'.
    destruct HA' as [Hs Hk Hns Hlen Hlt HRep Apool Hpool Ats Hts].
    pose proof (r_n HRep) as HN.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (r_nclits_small HRep) as Hncl.
    pose proof (Rep.r_starts HRep k Hlt) as Hrange.
    pose proof (r_clits HRep) as Fclits.
    pose proof (a_lits HRep) as (tl & Alits & Hclauses).
    destruct (ictx_clause m k k _ HRep eq_refl Hlt) as [Hcls Hlen_cl].
    (* What is left after the watchers: IndexAt for ictx (k + 1) *)
    assert (Hnext: forall (le': temp_env) (m': mem) (tp': nat -> Z),
      le' ! _s = Some (sptr sh) -> le' ! _k = Some (vnat k) ->
      le' ! _ns = Some (vnat (length (ish (idx lss k)))) ->
      le' ! _len = Some (vnat (starts sh (S k) - starts sh k)) ->
      RepL m' sh N lss (ictx lss al nl N rc (S k)) ->
      PoolArr m' sh tp' ->
      PoolFree sh N tp' (wls (ictx lss al nl N rc (S k))) ->
      Mem.unchanged_on (PoolFrame sh)
        m m' ->
      SeqK ge index_short (IndexK k) le' m' Out_normal).
    { intros le' m' tp' Hs' Hk' Hns' Hlen' HRep' Apool' Hpool' Hun. normal.
      apply (index_short_correct ts tp' k). constructor.
      - assumption.
      - assumption.
      - assumption.
      - assumption.
      - assumption.
      - assumption.
      - assumption.
      - assumption.
      - apply (arr_unchanged _ m m' (b_shorts sh) (length lss) ts Hun).
        + intros ofs. split; neq Hnd.
        + assumption.
      - assumption. }
    assert (Hfail: forall (le': temp_env) (m': mem),
      SeqK ge index_short (IndexK k) le' m'
        (ret_int (-1))).
    { intros le' m'. abrupt. apply loopk_return. right. reflexivity. }
    unfold index_watch, index_body, index_loop, f_index_clauses.
    cbn [fn_body drop_stmts first_stmt loop_body Swhile].
    (* if (len >= 2) *)
    branch.
    - (* len >= 2 *)
      intros Hge. destruct (nth k lss []) as [|c0 [|c1 ls]] eqn:Hcl.
      + (* not the empty clause *)
        cbn [length] in Hlen_cl. lia.
      + (* not a unit clause *)
        cbn [length] in Hlen_cl. lia.
      + (* two literals or more: watched by c0 and c1, each with the other as blocker *)
        destruct (clause_lit m sh N lss _ tl k 0 (c0 :: c1 :: ls) HRep Hclauses Hlt Hcls)
          as (Hpos0 & Htl0 & Hc0).
        { cbn [length]. lia. }
        destruct (clause_lit m sh N lss _ tl k 1 (c0 :: c1 :: ls) HRep Hclauses Hlt Hcls)
          as (Hpos1 & Htl1 & Hc1).
        { cbn [length]. lia. }
        cbn [nth] in Htl0, Hc0, Htl1, Hc1. rewrite Nat.add_0_r in Htl0, Hpos0.
        pose proof (key_small c0 N Hc0 HN) as Hkc0.
        pose proof (key_small c1 N Hc1 HN) as Hkc1.
        assert (Hb1: Int.add (Int.repr (Z.of_nat (starts sh k))) (Int.repr 1)
                     = Int.repr (Z.of_nat (starts sh k + 1))).
        { rewrite add_repr. f_equal. lia. }
        fold (push_stmt _t'1 _a _c) (push_stmt _t'2 _c _a).
        run. rewrite Htl0. run. rewrite Htl1.
        apply (index_push_correct (ictx lss al nl N rc k) k c0 c1 tp _t'1 _a _c).
        * assumption.
        * assumption.
        * assumption.
        * constructor; tmp.
        * assumption.
        * assumption.
        * assumption.
        * intros le' m'. abrupt. apply Hfail.
        * intros m1 tp1 HRep1 Apool1 Hpool1 Hun1. normal.
          set (x1 := set_watching (ictx lss al nl N rc k) c0
                       (watching (wls (ictx lss al nl N rc k)) c0 ++ [(k, c1)])) in *.
          apply (index_push_correct x1 k c1 c0 tp1 _t'2 _c _a).
          -- assumption.
          -- assumption.
          -- assumption.
          -- constructor; tmp.
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
             ++ frame.
    - (* else if (len == 1) *)
      intros Hlt2. branch.
      + (* a unit clause [c0]: watched by c0 *)
        intros Hone. destruct (nth k lss []) as [|c0 [|c1 ls]] eqn:Hcl.
        * (* not the empty clause *)
          cbn [length] in Hlen_cl. lia.
        * destruct (clause_lit m sh N lss _ tl k 0 [c0] HRep Hclauses Hlt Hcls)
            as (Hpos0 & Htl0 & Hc0).
          { cbn [length]. lia. }
          cbn [nth] in Htl0, Hc0. rewrite Nat.add_0_r in Htl0, Hpos0.
          pose proof (key_small c0 N Hc0 HN) as Hkc0.
          fold (push_stmt _t'3 _a__1 _a__1). run. rewrite Htl0.
          apply (index_push_correct (ictx lss al nl N rc k) k c0 c0 tp _t'3 _a__1 _a__1).
          -- assumption.
          -- assumption.
          -- assumption.
          -- constructor; tmp.
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
        * (* not two literals or more *)
          cbn [length] in Hlen_cl. lia.
      + (* the empty clause: no watcher *)
        intros Hnot1. destruct (nth k lss []) as [|c0 [|c1 ls]] eqn:Hcl.
        * apply exec_skip. apply (Hnext le m tp).
          -- assumption.
          -- assumption.
          -- assumption.
          -- assumption.
          -- rewrite ictx_step by assumption. rewrite Hcl. apply HRep.
          -- assumption.
          -- rewrite ictx_step by assumption. rewrite Hcl. apply Hpool.
          -- frame.
        * (* not a unit clause *)
          cbn [length] in Hlen_cl. lia.
        * (* not two literals or more *)
          cbn [length] in Hlen_cl. lia.
  Qed.

  (* The loop body of clause k: the range of the clause, then its watchers.

       {{ IndexInv k /\ k < ncl }}
         int b = s->cstart[k];
         int len = s->cstart[k + 1] - b;
       {{ IndexAt (ictx k) /\ b }}
         ...                                                     (index_watch_correct) *)
  Lemma index_body_correct: forall (ts: nat -> Z) (k: nat) (le: temp_env) (m: mem),
    k < length lss -> IndexInv ts k le m -> Exec ge le m index_body (IndexK k).
  Proof.
    intros ts k le m Hlt HI.
    destruct HI as [Hs Hk Hns Hkl [HRep [_ [tp [Apool Hpool]]]] Ats Hts].
    pose proof (r_lss_small HRep) as Hlss.
    pose proof (r_nclits_small HRep) as Hncl.
    pose proof (Rep.r_starts HRep k Hlt) as Hrange.
    pose proof (r_cstart HRep) as Fcstart.
    pose proof (a_starts HRep) as Astarts.
    assert (Hadd: Int.add (Int.repr (Z.of_nat k)) (Int.repr 1)
                  = Int.repr (Z.of_nat (S k))).
    { rewrite add_repr. f_equal. lia. }
    assert (Hsub: Int.sub (Int.repr (Z.of_nat (starts sh (S k))))
                    (Int.repr (Z.of_nat (starts sh k)))
                  = Int.repr (Z.of_nat (starts sh (S k) - starts sh k))).
    { rewrite sub_repr. f_equal. lia. }
    unfold index_body, index_loop, f_index_clauses.
    cbn [fn_body drop_stmts first_stmt loop_body Swhile].
    (* int b = s->cstart[k]; int len = s->cstart[k + 1] - b; *)
    run. ints. clear Fcstart Astarts.
    apply (index_watch_correct ts tp k).
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
  Lemma index_loop_correct: forall (le: temp_env) (m: mem),
    (1 <= N)%nat -> index_inv 0 le m -> Exec ge le m index_loop IndexPost.
  Proof.
    intros le m HN1 HI0.
    unfold index_loop, f_index_clauses. cbn [fn_body drop_stmts first_stmt].
    apply exec_loop with (R := index_variant) (I := index_inv) (a := 0).
    - apply well_founded_ltof.
    - intros k le1 m1 [ts HI]. pose proof HI as HI'.
      destruct HI' as [Hs Hk Hns Hkl [HRep [_ [tp [Apool Hpool]]]] Ats Hts].
      pose proof (r_lss_small HRep) as Hlss.
      pose proof (Rep.r_ncl HRep) as Fncl.
      (* if (k < s->ncl) ... else break; *)
      run. branch.
      + (* k < ncl: the body *)
        intros Hlt_z. assert (Hlt: (k < length lss)%nat) by lia.
        apply exec_skip. normal. clear Fncl.
        apply (index_body_correct ts k).
        * assumption.
        * constructor.
          -- tmp.
          -- tmp.
          -- tmp.
          -- assumption.
          -- split.
             ++ assumption.
             ++ split.
                ** reflexivity.
                ** exists tp. split; assumption.
          -- assumption.
          -- assumption.
      + (* k = ncl: break; every clause is indexed *)
        intros Hge.
        apply exec_break. abrupt. apply loopk_break. left. split.
        * reflexivity.
        * replace k with (length lss) in * by lia. exists ts. constructor.
          -- tmp.
          -- tmp.
          -- tmp.
          -- lia.
          -- split.
             ++ assumption.
             ++ split.
                ** reflexivity.
                ** exists tp. split; assumption.
          -- assumption.
          -- assumption.
    - assumption.
  Qed.

  (* index_clauses watches the first literals of every clause and collects the short
     ones:

       {{ Rep (ictx ... 0) /\ Arr shorts tsh }}
         int k = 0;
         int ns = 0;
         while (k < s->ncl) { ... }                                 (index_loop_correct)
       {{ result = -1 (out of room) }}
         return ns;
       {{ result = the number of short clauses /\ Rep (ictx ... ncl) /\
          they are in shorts }}                                                        *)
  Lemma index_clauses_correct: forall (tsh: nat -> Z),
    {{ m | Rep m sh N lss (ictx lss al nl N rc 0) /\
      Arr m (b_shorts sh) (length lss) tsh /\ (1 <= N)%nat }}
      f_index_clauses(sptr sh)
    {{ m', v | v = vint (-1) \/ exists (tsh': nat -> Z),
               v = vnat (length (ish (idx lss (length lss)))) /\
               Rep m' sh N lss (ictx lss al nl N rc (length lss)) /\
               Arr m' (b_shorts sh) (length lss) tsh' /\
               StackIn tsh' (ish (idx lss (length lss))) }}.
  Proof.
    intros tsh m (HRep & Ash & HN1).
    eapply call_simple.
    - reflexivity.
    - reflexivity.
    - unfold f_index_clauses. cbn [fn_body fn_return].
      (* int k = 0; int ns = 0; *)
      run. apply exec_weaken with (Q := IndexPost).
      + apply index_loop_correct.
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
          destruct HI as [Hs Hk Hns Hkl HRep' Ats Hts]. normal. return_int.
          right. exists ts. split.
          -- reflexivity.
          -- split.
             ++ assumption.
             ++ split; assumption.
        * (* out of room *)
          abrupt. exists (vint (-1)). split.
          -- apply result_int.
          -- now left.
  Qed.

End Loop.

Lemma index_clauses_fun: FunAt _index_clauses f_index_clauses.
Proof. apply find_fun. reflexivity. Qed.
