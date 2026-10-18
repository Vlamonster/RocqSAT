(* wpush appends a watcher, a clause and its blocker, to the watch list of a literal, or
   gives up when it has no room. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Propagate.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep.
Import ListNotations.

(* The blocks wpush leaves unchanged: all but the watch pool and the watch list
   lengths. *)
Abbreviation PoolFrame sh := (fun (b: block) (_: Z) => b <> b_wpool sh /\ b <> b_wlen sh).
(* x with watcher e appended to the watch list of l. *)
Abbreviation pushed x l e := (set_watching x l (watching (wls x) l ++ [e])).

(* The pool t with watcher e stored just past the watch list of l in x. *)
Abbreviation push_pool sh x l t e :=
  (set_watcher t (offs sh (lit_key l) + length (watching (wls x) l)) e).

(* Appending watcher e to the watch list of key k, when it has room, keeps the pool of
   the other watchers. *)
Lemma pool_push: forall (m: mem) (sh: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (t: nat -> Z) (skip: nat -> nat -> Prop) (k: nat) (e: Watcher),
  RepL m sh N lss x -> PoolOf sh N t (wls x) skip -> (k < 2 * N)%nat ->
  (forall (q: nat), skip k q -> (q < length (tget (wls x) k))%nat) ->
  (length (tget (wls x) k) < caps sh k)%nat ->
  PoolOf sh N (set_watcher t (offs sh k + length (tget (wls x) k)) e)
    (tset (wls x) k (tget (wls x) k ++ [e])) skip.
Proof.
  intros m sh N lss x t skip k e HRep Hpool Hk Hskip Hroom k' q Hk' Hq Hns.
  rewrite tget_tset in Hq |- *.
  destruct (Nat.eq_dec k k') as [<- | Hne].
  - rewrite length_app in Hq. cbn [length] in Hq.
    destruct (Nat.eq_dec q (length (tget (wls x) k))) as [-> | Hq'].
    + rewrite nth_middle. apply set_watcher_same.
    + rewrite app_nth1 by lia.
      apply set_watcher_other.
      * lia.
      * apply Hpool.
        -- assumption.
        -- lia.
        -- assumption.
  - assert (Hfar: (offs sh k' + q)%nat <> (offs sh k + length (tget (wls x) k))%nat).
    + pose proof (r_wlen_le HRep k' Hk'). destruct (Nat.lt_ge_cases k k') as [Hlt | Hge].
      * pose proof (r_apart HRep k k' (conj Hlt Hk')). lia.
      * assert (Hlt: (k' < k)%nat) by lia. pose proof (r_apart HRep k' k (conj Hlt Hk)).
        lia.
    + apply set_watcher_other.
      * assumption.
      * now apply Hpool.
Qed.

(* wpush stores the watcher of clause i with blocker b at the end of the watch list of l
   in the pool and makes the list one longer, unless it has no room. Writing n for its
   length, k for lit_key l and w = woff[l] + n for the new watcher:

     {{ RepL m x /\ Arr m pool t /\ PoolOf t (wls x) skip /\ extract l < N /\ i < ncl /\
        extract b < N }}
       int n = s->wlen[l];
       if (n >= s->wcap[l]) return 0;
     {{ result = 0 (no room) }}
       int q = 2 * (s->woff[l] + n);
       s->wpool[q] = i;                                             (rep_store_pool)
       s->wpool[q + 1] = b;                                         (rep_store_pool)
       s->wlen[l] = n + 1;                                          (rep_store_wlen)
       return 1;
     {{ result = 1 /\ RepL (pushed x l (i, b)) /\ the pool is push_pool, which holds
        the new watcher /\ only the pool and wlen changed }}                         *)
Lemma wpush_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (l: Lit) (i: nat) (b: Lit) (t: nat -> Z) (skip: nat -> nat -> Prop),
  {{ m | RepL m sh N lss x /\ PoolArr m sh t /\
         PoolOf sh N t (wls x) skip /\
         (forall (q: nat), skip (lit_key l) q ->
            (q < length (watching (wls x) l))%nat) /\
         (extract l < N)%nat /\ (i < length lss)%nat /\ (extract b < N)%nat }}
    f_wpush(sptr sh, vint (key l), vnat i, vint (key b))
  {{ m', v | v = vint 0 \/
             (v = vint 1 /\
                RepL m' sh N lss (pushed x l (i, b)) /\
                PoolArr m' sh (push_pool sh x l t (i, b)) /\
                PoolOf sh N (push_pool sh x l t (i, b))
                  (tset (wls x) (lit_key l) (watching (wls x) l ++ [(i, b)])) skip /\
                Mem.unchanged_on
                  (PoolFrame sh) m m') }}.
Proof.
  intros sh N lss x l i b t skip m (HRep & Apool & Hpool & Hskip & Hl & Hi & Hb).
  pose proof (key_small l N Hl (r_n HRep)) as Hkey.
  pose proof (key_small b N Hb (r_n HRep)) as Hkeyb.
  pose proof (lit_key_lt l N Hl) as Hk.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_wpush. cbn [fn_body fn_return].
    pose proof HRep as HRep'. destruct HRep'. unpack.
    pose proof (r_wlen_le (lit_key l) Hk) as Hlen.
    pose proof (r_room (lit_key l) Hk) as Hroom.
    set (n := length (watching (wls x) l)) in *.
    assert (Hn: n = length (tget (wls x) (lit_key l))) by reflexivity.
    (* int n = s->wlen[l]; if (n >= s->wcap[l]) return 0; *)
    run. eapply exec_if_ge.
    + ev.
    + ev.
    + reflexivity.
    + lia.
    + (* no room: return 0; *)
      intros Hfull.
      eapply exec_return.
      * ev.
      * ret. exists (vint 0). split.
        -- apply result_int.
        -- now left.
    + (* the list has room *)
      intros Hroom_z.
      assert (Hlt: (length (tget (wls x) (lit_key l)) < caps sh (lit_key l))%nat) by lia.
      set (w := (offs sh (lit_key l) + n)%nat).
      assert (Hw: (w < npool sh)%nat) by (subst w; lia).
      (* The entries of watcher w, 2 w and 2 w + 1, as C computes them *)
      assert (Hq: Int.mul (Int.repr 2)
                    (Int.add (Int.repr (Z.of_nat (offs sh (lit_key l))))
                       (Int.repr (Z.of_nat (length (tget (wls x) (lit_key l))))))
                  = Int.repr (Z.of_nat (2 * w))).
      { rewrite add_repr by lia. rewrite mul_repr. f_equal. subst w. lia. }
      assert (Hq1: Int.add (Int.repr (Z.of_nat (2 * w))) (Int.repr 1)
                   = Int.repr (Z.of_nat (2 * w + 1))).
      { rewrite add_repr by lia. f_equal. lia. }
      assert (Hadd1: Int.add (Int.repr (Z.of_nat (length (tget (wls x) (lit_key l)))))
                       (Int.repr 1)
                     = Int.repr (Z.of_nat (S n))).
      { rewrite add_repr by lia. f_equal. lia. }
      assert (H2w: (2 * w < 2 * npool sh)%nat) by lia.
      assert (H2w1: (2 * w + 1 < 2 * npool sh)%nat) by lia.
      pose proof r_nodup as Hnd.
      (* int q = 2 * (s->woff[l] + n); s->wpool[q] = i; *)
      run. eapply (exec_store_arr Apool H2w).
      * evl.
      * ofs.
      * reflexivity.
      * ev.
      * intros m1 Hst1. normal.
        pose proof (rep_store_pool m m1 _ _ HRep Hst1) as HRep1.
        pose proof (arr_store Apool H2w Hst1) as Apool1.
        pose proof (Rep.r_wpool HRep1) as Fwpool1.
        (* only the pool changes *)
        assert (Hun1: Mem.unchanged_on
                        (PoolFrame sh)
                        m m1).
        { apply (store_unchanged _ m m m1 _ _ _ _ (Mem.unchanged_on_refl _ m) Hst1).
          intros j [Hb' _]. now apply Hb'. }
        keep_mem m1.
        (* s->wpool[q + 1] = b; *)
        run. eapply (exec_store_arr Apool1 H2w1).
        -- evl.
        -- ofs.
        -- reflexivity.
        -- ev.
        -- intros m2 Hst2. normal.
           pose proof (rep_store_pool m1 m2 _ _ HRep1 Hst2) as HRep2.
           assert (Apool2: PoolArr m2 sh (set_watcher t w (i, b))).
           { apply (arr_store Apool1 H2w1 Hst2). }
           assert (Hun2: Mem.unchanged_on
                           (PoolFrame sh)
                           m m2).
           { apply (store_unchanged _ m m1 m2 _ _ _ _ Hun1 Hst2).
             intros j [Hb' _]. now apply Hb'. }
           pose proof (Rep.r_wlen HRep2) as Fwlen2.
           pose proof (Rep.a_wlen HRep2) as Awlen2.
           keep_mem m2.
           (* s->wlen[l] = n + 1; *)
           run. eapply (exec_store_arr Awlen2 Hk).
           ++ evl.
           ++ ofs.
           ++ reflexivity.
           ++ ev.
           ++ intros m3 Hst3. normal.
              cbn [cast_int_int] in Hst3. rewrite Hadd1 in Hst3.
              pose proof
                (rep_store_wlen m2 m3 l i b HRep2 Hl Hlt Hi Hb Hst3)
                as HRep3.
              (* return 1; *)
              eapply exec_return.
              ** ev.
              ** exists (vint 1). split.
                 --- apply result_int.
                 --- right. split.
                     +++ reflexivity.
                     +++ split.
                         { assumption. }
                         split.
                         { apply (arr_store_other Apool2 Hst3). neq Hnd. }
                         split.
                         { apply (pool_push m sh N lss x).
                           - assumption.
                           - assumption.
                           - assumption.
                           - assumption.
                           - assumption. }
                         (* and the store to wlen keeps the rest *)
                         apply (store_unchanged _ m m2 m3 _ _ _ _ Hun2 Hst3).
                         intros j [_ Hb']. now apply Hb'.
Qed.

Lemma wpush_fun: FunAt _wpush f_wpush.
Proof. apply find_fun. reflexivity. Qed.
