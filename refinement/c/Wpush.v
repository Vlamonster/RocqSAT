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

(* Appending watcher e to a watch list with room keeps the pool of the others. *)
Lemma pool_push: forall (S: Shape) (N: nat) (t: nat -> Z) (wl: WatchLists)
  (skip: nat -> nat -> Prop) (k: nat) (e: Watcher),
  PoolOf S N t wl skip ->
  (k < 2 * N)%nat ->
  (forall (q: nat), skip k q -> (q < length (tget wl k))%nat) ->
  (length (tget wl k) < caps S k)%nat ->
  (forall (k1 k2: nat), (k1 < k2 < 2 * N)%nat ->
     (offs S k1 + caps S k1 <= offs S k2)%nat) ->
  (forall (k': nat), (k' < 2 * N)%nat -> (length (tget wl k') <= caps S k')%nat) ->
  PoolOf S N (set_watcher t (offs S k + length (tget wl k)) e)
    (tset wl k (tget wl k ++ [e])) skip.
Proof.
  intros S N t wl skip k e Hpool Hk Hskip Hroom Happart Hle k' q Hk' Hq Hns.
  rewrite tget_tset in Hq |- *.
  destruct (Nat.eq_dec k k') as [<- | Hne].
  - rewrite length_app in Hq. cbn [length] in Hq.
    destruct (Nat.eq_dec q (length (tget wl k))) as [-> | Hq'].
    + rewrite nth_middle. apply set_watcher_same.
    + rewrite app_nth1 by lia.
      apply set_watcher_other.
      * lia.
      * apply Hpool.
        -- assumption.
        -- lia.
        -- assumption.
  - assert (Hfar: (offs S k' + q)%nat <> (offs S k + length (tget wl k))%nat).
    + pose proof (Hle k' Hk'). destruct (Nat.lt_ge_cases k k') as [Hlt | Hge].
      * pose proof (Happart k k' (conj Hlt Hk')). lia.
      * assert (Hlt: (k' < k)%nat) by lia. pose proof (Happart k' k (conj Hlt Hk)). lia.
    + apply set_watcher_other.
      * assumption.
      * now apply Hpool.
Qed.

(* wpush stores the watcher of clause i with blocker b at the end of the watch list of l
   in the pool and makes the list one longer, unless it has no room. Writing n for its
   length, k for lit_key l and w = woff[l] + n for the new watcher:

     {{ RepB m x /\ Arr m pool t /\ PoolOf t (wls x) skip /\ extract l < N /\ i < ncl /\
        extract b < N }}
       int n = s->wlen[l];
       if (n >= s->wcap[l]) return 0;
     {{ result = 0 (no room) }}
       int q = 2 * (s->woff[l] + n);
       s->wpool[q] = i;                                             (rep_store_pool)
       s->wpool[q + 1] = b;                                         (rep_store_pool)
       s->wlen[l] = n + 1;                                          (rep_store_wlen)
       return 1;
     {{ result = 1 /\ RepB (set_watching x l (ws ++ [(i, b)])) /\ the pool holds it, and
        is t with watcher w set /\ only the pool and wlen changed }}               *)
Lemma wpush_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (l: Lit) (i: nat) (b: Lit) (t: nat -> Z) (skip: nat -> nat -> Prop),
  {{ m | RepB m S N lss x lims /\ Arr m (b_wpool S) (2 * npool S) t /\
         PoolOf S N t (wls x) skip /\
         (forall (q: nat), skip (lit_key l) q ->
            (q < length (watching (wls x) l))%nat) /\
         (extract l < N)%nat /\ (i < length lss)%nat /\ (extract b < N)%nat }}
    f_wpush(sptr S, vint (key l), vint (Z.of_nat i), vint (key b))
  {{ m', v | v = vint 0 \/
             (v = vint 1 /\
                RepB m' S N lss
                  (set_watching x l (watching (wls x) l ++ [(i, b)])) lims /\
                Arr m' (b_wpool S) (2 * npool S)
                  (set_watcher t (offs S (lit_key l) + length (watching (wls x) l))
                    (i, b)) /\
                PoolOf S N
                  (set_watcher t (offs S (lit_key l) + length (watching (wls x) l))
                    (i, b))
                  (tset (wls x) (lit_key l) (watching (wls x) l ++ [(i, b)])) skip /\
                Mem.unchanged_on
                  (fun (b: block) (_: Z) => b <> b_wpool S /\ b <> b_wlen S) m m') }}.
Proof.
  intros S N lss x lims l i b t skip m (HRep & Apool & Hpool & Hskip & Hl & Hi & Hb).
  pose proof (key_small l N Hl (r_n _ _ _ _ _ _ HRep)) as Hkey.
  pose proof (key_small b N Hb (r_n _ _ _ _ _ _ HRep)) as Hkeyb.
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
    run. eapply (exec_if_cmp _ _ _ Cge).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + unfold Small. lia.
    + unfold Small. lia.
    + destruct (Nat.lt_ge_cases (length (tget (wls x) (lit_key l))) (caps S (lit_key l)))
        as [Hlt | Hge].
      * (* the list has room *)
        replace (zcmp Cge (Z.of_nat (length (tget (wls x) (lit_key l))))
                   (Z.of_nat (caps S (lit_key l))))
          with false by (symmetry; cbn [zcmp]; apply Z.leb_gt; lia).
        set (w := (offs S (lit_key l) + n)%nat).
        assert (Hw: (w < npool S)%nat) by (subst w; lia).
        (* The entries of watcher w, 2 w and 2 w + 1, as C computes them *)
        assert (Hq: Int.mul (Int.repr 2)
                      (Int.add (Int.repr (Z.of_nat (offs S (lit_key l))))
                         (Int.repr (Z.of_nat (length (tget (wls x) (lit_key l))))))
                    = Int.repr (Z.of_nat (2 * w))).
        { rewrite add_repr by lia. rewrite mul_repr. f_equal. subst w. lia. }
        assert (Hq1: Int.add (Int.repr (Z.of_nat (2 * w))) (Int.repr 1)
                     = Int.repr (Z.of_nat (2 * w + 1))).
        { rewrite add_repr by lia. f_equal. lia. }
        assert (Hadd1: Int.add (Int.repr (Z.of_nat (length (tget (wls x) (lit_key l)))))
                         (Int.repr 1)
                       = Int.repr (Z.of_nat (Datatypes.S n))).
        { rewrite add_repr by lia. f_equal. lia. }
        (* int q = 2 * (s->woff[l] + n); s->wpool[q] = i; *)
        cbv beta iota. run. eapply exec_store.
        -- evl.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- ofs. bound.
        -- ofs. cbn [cast_int_int].
           destruct (arr_storable m (b_wpool S) (2 * npool S) (2 * w) t
                       (Z.of_nat i) Apool ltac:(lia)) as [m1 Hst1].
           exists m1. split.
           ++ apply Hst1.
           ++ normal.
              pose proof (rep_store_pool m m1 S N lss x lims _ _ HRep Hst1) as HRep1.
              pose proof (arr_store _ _ _ _ (2 * w) _ _ Apool ltac:(lia) Hst1) as Apool1.
              pose proof (Rep.r_wpool _ _ _ _ _ _ HRep1) as Fwpool1.
              pose proof r_nodup as Hnd. keep_mem m1.
              (* s->wpool[q + 1] = b; *)
              run. eapply exec_store.
              ** evl.
              ** ev.
              ** reflexivity.
              ** reflexivity.
              ** ofs. bound.
              ** ofs. cbn [cast_int_int].
                 destruct (arr_storable m1 (b_wpool S) (2 * npool S) (2 * w + 1) _
                             (key b) Apool1 ltac:(lia)) as [m2 Hst2].
                 exists m2. split.
                 --- apply Hst2.
                 --- normal.
                     pose proof (rep_store_pool m1 m2 S N lss x lims _ _ HRep1 Hst2)
                       as HRep2.
                     assert (Apool2: Arr m2 (b_wpool S) (2 * npool S)
                       (set_watcher t w (i, b))).
                     { apply (arr_store m1 m2 (b_wpool S) (2 * npool S)
                         (2 * w + 1) _ _ Apool1).
                       - lia.
                       - apply Hst2. }
                     pose proof (Rep.r_wlen _ _ _ _ _ _ HRep2) as Fwlen2.
                     pose proof (Rep.a_wlen _ _ _ _ _ _ HRep2) as Awlen2.
                     keep_mem m2.
                     (* s->wlen[l] = n + 1; *)
                     run. eapply exec_store.
                     +++ evl.
                     +++ ev.
                     +++ reflexivity.
                     +++ reflexivity.
                     +++ ofs. bound.
                     +++ ofs. cbn [cast_int_int]. ints.
                         destruct (arr_storable m2 (b_wlen S) (2 * N) (lit_key l) _
                                     (Z.of_nat (Datatypes.S n)) Awlen2 Hk) as [m3 Hst3].
                         exists m3. split.
                         *** apply Hst3.
                         *** normal.
                             pose proof
                               (rep_store_wlen m2 m3 S N lss x lims l i b HRep2 Hl
                                           Hlt Hi Hb Hst3) as HRep3.
                             (* return 1; *)
                             eapply exec_return.
                             ---- ev.
                             ---- exists (vint 1). split.
                                  ++++ apply result_int.
                                  ++++ right. split.
                                       **** reflexivity.
                                       **** split.
                                            { assumption. }
                                            split.
                                            { apply (arr_store_other _ _ _ _ _ _ _ _ _
                                                       Apool2 Hst3).
                                              neq Hnd. }
                                            split.
                                            { apply pool_push; assumption. }
                                            (* only the pool and wlen changed *)
                                            apply (store_unchanged _ m m2 m3 Mint32
                                                     (b_wlen S) (4 * Z.of_nat (lit_key l))
                                                     (vint (Z.of_nat (Datatypes.S n)))).
                                            ----- apply (store_unchanged _ m m1 m2 Mint32
                                                           (b_wpool S)
                                                           (4 * Z.of_nat (2 * w + 1))
                                                           (vint (key b))).
                                                  +++++ apply (store_unchanged _ m m m1
                                                                 Mint32 (b_wpool S)
                                                                 (4 * Z.of_nat (2 * w))
                                                                 (vint (Z.of_nat i))).
                                                        ***** apply Mem.unchanged_on_refl.
                                                        ***** apply Hst1.
                                                        ***** intros j [Hb' _].
                                                              now apply Hb'.
                                                  +++++ apply Hst2.
                                                  +++++ intros j [Hb' _]. now apply Hb'.
                                            ----- apply Hst3.
                                            ----- intros j [_ Hb']. now apply Hb'.
      * (* no room: return 0; *)
        replace (zcmp Cge (Z.of_nat (length (tget (wls x) (lit_key l))))
                   (Z.of_nat (caps S (lit_key l))))
          with true by (symmetry; cbn [zcmp]; apply Z.leb_le; lia).
        cbv beta iota. eapply exec_return.
        -- ev.
        -- ret. exists (vint 0). split.
           ++ apply result_int.
           ++ now left.
Qed.

Lemma wpush_fun: exists (b: block),
  Genv.find_symbol ge _wpush = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_wpush).
Proof. apply find_fun. reflexivity. Qed.
