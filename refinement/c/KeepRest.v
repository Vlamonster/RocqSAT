(* keep_rest ends a visit at a conflict: the watchers kept and those not yet visited
   become the watch list of p (the rev_append of visit_t).

   This file also holds what visit (Visit.v) and keep_rest share: the temporaries and the
   memory during a visit of the watch list ws of p (VisitTemps, VisitMem), and what
   keeping a watcher, appending one to another list, and ending the visit do to them. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs Ctypes
  Ctypesdefs Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Propagate CStep.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep.
Import ListNotations.

Section Pool.
  (* During a visit of the watch list of key P, its first n watchers are not in the
     pool. *)
  Definition SkipP (P n k q: nat): Prop := k = P /\ (q < n)%nat.

  (* Ending a visit: the watch list of key P becomes L, which the pool holds at its
     front. *)
  Lemma pool_finish: forall (S: Shape) (N: nat) (t: nat -> Z) (wl: WatchLists)
    (P n: nat) (L: list Watcher),
    PoolOf S N t wl (SkipP P n) ->
    (forall (q: nat), (q < length L)%nat ->
       WatcherAt t (offs S P + q) (nth q L (0%nat, Pos 0%nat))) ->
    PoolOf S N t (tset wl P L) (fun (_ _: nat) => False).
  Proof.
    intros S N t wl P n L Hpool HL k q Hk Hq _. rewrite tget_tset in Hq |- *.
    destruct (Nat.eq_dec P k) as [<- | Hne].
    - apply HL. assumption.
    - apply Hpool.
      + assumption.
      + assumption.
      + intros [Heq _]. congruence.
  Qed.

  (* Watcher q of the watch list of P is apart from watcher z of the list of k. *)
  Lemma pool_apart: forall (m: mem) (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
    (lims: list nat) (P k q z: nat),
    RepB m S N lss x lims -> (P < 2 * N)%nat -> (k < 2 * N)%nat -> P <> k ->
    (q < caps S P)%nat -> (z < caps S k)%nat ->
    (offs S P + q <> offs S k + z)%nat.
  Proof.
    intros m S N lss x lims P k q z HRep HP Hk Hne Hq Hz.
    destruct (Nat.lt_ge_cases P k) as [Hlt | Hge].
    - pose proof (r_apart _ _ _ _ _ _ HRep P k (conj Hlt Hk)). lia.
    - assert (Hlt: (k < P)%nat) by lia.
      pose proof (r_apart _ _ _ _ _ _ HRep k P (conj Hlt HP)). lia.
  Qed.

  (* Setting a watcher in the skipped part of the watch list of P keeps the pool of the
     others. *)
  Lemma pool_set_skipped: forall (m: mem) (S: Shape) (N: nat) (lss: list (list Lit))
    (x: Ctx) (lims: list nat) (t: nat -> Z) (P n q: nat) (e: Watcher),
    RepB m S N lss x lims -> PoolOf S N t (wls x) (SkipP P n) -> (P < 2 * N)%nat ->
    (q < n)%nat -> (n <= length (tget (wls x) P))%nat ->
    PoolOf S N (set_watcher t (offs S P + q) e) (wls x) (SkipP P n).
  Proof.
    intros m S N lss x lims t P n q e HRep Hpool HP Hq Hn k y Hk Hy Hns.
    apply set_watcher_other.
    - destruct (Nat.eq_dec P k) as [<- | Hne].
      + intros Heq. apply Hns. split.
        * reflexivity.
        * lia.
      + pose proof (r_wlen_le _ _ _ _ _ _ HRep P HP).
        pose proof (r_wlen_le _ _ _ _ _ _ HRep k Hk).
        intros Heq. symmetry in Heq. revert Heq.
        apply (pool_apart m S N lss x lims P k q y HRep).
        * assumption.
        * assumption.
        * assumption.
        * lia.
        * lia.
    - now apply Hpool.
  Qed.
End Pool.

(* The temporaries of a visit of the watch list ws of p in x, at position k with j
   watchers kept: base is the entry of the first watcher of p in the pool. *)
Record VisitTemps (S: Shape) (x: Ctx) (p: Lit) (j k: nat) (le: temp_env): Prop := {
  vt_s: le ! _s = Some (sptr S);
  vt_p: le ! _p = Some (vint (key p));
  vt_base: le ! _base = Some (vint (Z.of_nat (2 * offs S (lit_key p))));
  vt_n: le ! _n = Some (vint (Z.of_nat (length (watching (wls x) p))));
  vt_j: le ! _j = Some (vint (Z.of_nat j));
  vt_k: le ! _k = Some (vint (Z.of_nat k));
}.

(* The memory m at position k of ws: it represents the context xc reached, whose watch
   list of p still starts with ws; the pool t holds the watchers kept at the front of the
   list of p (newest last), ws from k on, and the other watch lists. *)
Record VisitMem (S: Shape) (N: nat) (lss: list (list Lit)) (lims: list nat) (x: Ctx)
  (p: Lit) (k: nat) (kept: list Watcher) (xc: Ctx) (t: nat -> Z) (m: mem): Prop := {
  vm_atom: (extract p < N)%nat;
  vm_le: (length kept <= k <= length (watching (wls x) p))%nat;
  vm_rep: RepB m S N lss xc lims;
  vm_pool: Arr m (b_wpool S) (2 * npool S) t;
  vm_poolof: PoolOf S N t (wls xc) (SkipP (lit_key p) (length (watching (wls x) p)));
  vm_front: forall (q: nat), (q < length kept)%nat ->
    WatcherAt t (offs S (lit_key p) + q) (nth q (rev kept) (0%nat, Pos 0%nat));
  vm_back: forall (q: nat), (k <= q < length (watching (wls x) p))%nat ->
    WatcherAt t (offs S (lit_key p) + q) (nth q (watching (wls x) p) (0%nat, Pos 0%nat));
  vm_prefix: exists (extra: list Watcher), watching (wls xc) p = watching
    (wls x) p ++ extra;
  vm_kept: forall (i: nat) (b: Lit), In (i, b) kept -> (i < length lss)%nat /\
    (extract b < N)%nat
}.

(* The entry of watcher w of the list of p, and its blocker, as C computes them from base:
   base + 2 w and base + 2 w + 1. *)
Lemma watcher_entry: forall (o w: nat), Z.of_nat (o + w) < 1073741824 ->
  Int.add (Int.repr (Z.of_nat (2 * o))) (Int.mul (Int.repr 2) (Int.repr (Z.of_nat w))) =
    Int.repr (Z.of_nat (2 * (o + w))) /\
  Int.add (Int.repr (Z.of_nat (2 * (o + w)))) (Int.repr 1) =
    Int.repr (Z.of_nat (2 * (o + w) + 1)).
Proof.
  intros o w Hsmall. split.
  - rewrite mul_repr, add_repr. f_equal. lia.
  - rewrite add_repr. f_equal. lia.
Qed.

Section Memory.
  Variables (S: Shape) (N: nat) (lss: list (list Lit)) (lims: list nat) (x: Ctx)
    (p: Lit).

  (* The watch list of p fits in its room of the pool, which is small. *)
  Lemma visit_room: forall (k: nat) (kept: list Watcher) (xc: Ctx) (t: nat -> Z) (m: mem),
    VisitMem S N lss lims x p k kept xc t m ->
    (length (watching (wls x) p) <= caps S (lit_key p))%nat /\
    (offs S (lit_key p) + caps S (lit_key p) <= npool S)%nat /\
    Z.of_nat (npool S) < 1073741824.
  Proof.
    intros k kept xc t m HM. destruct HM as [Hp _ HRep _ _ _ _ [extra Hext] _].
    pose proof (lit_key_lt p N Hp) as HP.
    pose proof (r_wlen_le _ _ _ _ _ _ HRep (lit_key p) HP) as Hcap.
    fold (watching (wls xc) p) in Hcap. rewrite Hext, length_app in Hcap.
    split.
    - lia.
    - split.
      + apply (r_room _ _ _ _ _ _ HRep). assumption.
      + apply (r_pool_small _ _ _ _ _ _ HRep).
  Qed.

  (* The watchers of ws are of clauses, with blockers of atoms below N. *)
  Lemma visit_watcher: forall (k: nat) (kept: list Watcher) (xc: Ctx) (t: nat -> Z)
    (m: mem) (z: nat),
    VisitMem S N lss lims x p k kept xc t m -> (z < length (watching (wls x) p))%nat ->
    (fst (nth z (watching (wls x) p) (0%nat, Pos 0%nat)) < length lss)%nat /\
    (extract (snd (nth z (watching (wls x) p) (0%nat, Pos 0%nat))) < N)%nat.
  Proof.
    intros k kept xc t m z HM Hz. destruct HM as [Hp _ HRep _ _ _ _ [extra Hext] _].
    pose proof (lit_key_lt p N Hp) as HP.
    assert (Hin: In (nth z (watching (wls x) p) (0%nat, Pos 0%nat))
      (tget (wls xc) (lit_key p))).
    - fold (watching (wls xc) p). rewrite Hext. apply in_or_app. left. apply nth_In.
      assumption.
    - destruct (nth z (watching (wls x) p) (0%nat, Pos 0%nat)) as [i b]. cbn [fst snd].
      split.
      + apply (r_wls_cls _ _ _ _ _ _ HRep (lit_key p) i b); assumption.
      + apply (r_wls_blk _ _ _ _ _ _ HRep (lit_key p) i b); assumption.
  Qed.

  (* Moving past a watcher that is not kept. *)
  Lemma visit_mem_next: forall (k: nat) (kept: list Watcher) (xc: Ctx) (t: nat -> Z)
    (m: mem),
    VisitMem S N lss lims x p k kept xc t m -> (k < length (watching (wls x) p))%nat ->
    VisitMem S N lss lims x p (Datatypes.S k) kept xc t m.
  Proof.
    intros k kept xc t m HM Hk.
    destruct HM as [Hp Hle HRep Apool Hpool Hfront Hback Hext Hkept].
    constructor; try assumption.
    - (* k + 1 is still within ws *)
      lia.
    - (* ws from k + 1 on *)
      intros q Hq. apply Hback. lia.
  Qed.

  (* Keeping watcher e, at position k: it is stored after the watchers kept.

       s->wpool[base + 2 * j] = i; s->wpool[base + 2 * j + 1] = kb;    (rep_store_pool) *)
  Lemma visit_mem_keep: forall (k: nat) (kept: list Watcher) (xc: Ctx) (t: nat -> Z)
    (e: Watcher) (m m1 m2: mem),
    VisitMem S N lss lims x p k kept xc t m -> (k < length (watching (wls x) p))%nat ->
    (fst e < length lss)%nat -> (extract (snd e) < N)%nat ->
    Mem.store Mint32 m (b_wpool S) (4 * Z.of_nat (2 * (offs S (lit_key p) + length kept)))
      (vint (Z.of_nat (fst e))) = Some m1 ->
    Mem.store Mint32 m1 (b_wpool S)
      (4 * Z.of_nat (2 * (offs S (lit_key p) + length kept) + 1)) (vint (key (snd e))) =
      Some m2 ->
    VisitMem S N lss lims x p (Datatypes.S k) (e :: kept) xc
      (set_watcher t (offs S (lit_key p) + length kept) e) m2.
  Proof.
    intros k kept xc t e m m1 m2 HM Hk Hi Hb Hst1 Hst2.
    pose proof (visit_room k kept xc t m HM) as (Hcap & Hroom & Hsmall).
    destruct HM as [Hp Hle HRep Apool Hpool Hfront Hback [extra Hext] Hkept].
    pose proof (lit_key_lt p N Hp) as HP.
    constructor; try assumption.
    - (* one more kept *)
      cbn [length]. lia.
    - (* the stores are to the pool *)
      pose proof (rep_store_pool m m1 S N lss xc lims _ _ HRep Hst1) as HRep1.
      apply (rep_store_pool m1 m2 S N lss xc lims _ _ HRep1 Hst2).
    - apply (arr_store_watcher m m1 m2 (b_wpool S) (npool S) _ t e Apool).
      + lia.
      + assumption.
      + assumption.
    - (* the stores are in the skipped part of the list of p *)
      apply (pool_set_skipped m S N lss xc lims).
      + assumption.
      + assumption.
      + assumption.
      + lia.
      + fold (watching (wls xc) p). rewrite Hext, length_app. lia.
    - (* e is the newest watcher kept *)
      intros q Hq. cbn [length rev] in Hq |- *.
      destruct (Nat.eq_dec q (length kept)) as [-> | Hne].
      + rewrite <- length_rev, nth_middle. apply set_watcher_same.
      + apply set_watcher_other.
        * lia.
        * rewrite app_nth1 by (rewrite length_rev; lia). apply Hfront. lia.
    - (* ws from k + 1 on is untouched *)
      intros q Hq. apply set_watcher_other.
      + lia.
      + apply Hback. lia.
    - exists extra. assumption.
    - intros i b [Heq | Hin].
      + rewrite Heq in Hi, Hb. cbn [fst snd] in Hi, Hb. split.
        * assumption.
        * assumption.
      + apply Hkept. assumption.
  Qed.

  (* A call or store that changes the context to xc' but not its watch lists, nor the
     pool. *)
  Lemma visit_mem_ctx: forall (k: nat) (kept: list Watcher) (xc xc': Ctx) (t: nat -> Z)
    (m m': mem),
    VisitMem S N lss lims x p k kept xc t m -> RepB m' S N lss xc' lims ->
    Arr m' (b_wpool S) (2 * npool S) t -> wls xc' = wls xc ->
    VisitMem S N lss lims x p k kept xc' t m'.
  Proof.
    intros k kept xc xc' t m m' HM HRep' Apool' Hwls.
    destruct HM as [Hp Hle HRep Apool Hpool Hfront Hback Hext Hkept].
    constructor; try assumption.
    - rewrite Hwls. assumption.
    - unfold watching. rewrite Hwls. apply Hext.
  Qed.

  (* Appending the watcher of clause i with blocker b to the watch list of r, as wpush
     does (wpush_correct): the new watcher is past the end of ws, so the pool keeps the
     watchers kept and ws from k on. *)
  Lemma visit_mem_push: forall (k: nat) (kept: list Watcher) (xc: Ctx) (t: nat -> Z)
    (i: nat) (r b: Lit) (m m': mem),
    VisitMem S N lss lims x p k kept xc t m -> (extract r < N)%nat ->
    RepB m' S N lss (set_watching xc r (watching (wls xc) r ++ [(i, b)])) lims ->
    Arr m' (b_wpool S) (2 * npool S)
      (set_watcher t (offs S (lit_key r) + length (watching (wls xc) r)) (i, b)) ->
    PoolOf S N (set_watcher t (offs S (lit_key r) + length (watching (wls xc) r)) (i, b))
      (tset (wls xc) (lit_key r) (watching (wls xc) r ++ [(i, b)]))
      (SkipP (lit_key p) (length (watching (wls x) p))) ->
    VisitMem S N lss lims x p k kept
      (set_watching xc r (watching (wls xc) r ++ [(i, b)]))
      (set_watcher t (offs S (lit_key r) + length (watching (wls xc) r)) (i, b)) m'.
  Proof.
    intros k kept xc t i r b m m' HM Hr HRep' Apool' Hpool'.
    destruct HM as [Hp Hle HRep Apool Hpool Hfront Hback [extra Hext] Hkept].
    pose proof (lit_key_lt p N Hp) as HP.
    pose proof (lit_key_lt r N Hr) as HR.
    (* The new watcher is apart from ws. *)
    assert (Hapart: forall (q: nat), (q < length (watching (wls x) p))%nat ->
              (offs S (lit_key p) + q <>
               offs S (lit_key r) + length (watching (wls xc) r))%nat).
    { intros q Hq. pose proof (r_wlen_le _ _ _ _ _ _ HRep (lit_key p) HP) as Hcap_p.
      pose proof (r_wlen_le _ _ _ _ _ _ HRep' (lit_key r) HR) as Hcap_r.
      cbn [set_watching wls] in Hcap_r. rewrite tget_tset_same, length_app in Hcap_r.
      cbn [length] in Hcap_r. unfold watching in *.
      destruct (Nat.eq_dec (lit_key r) (lit_key p)) as [Heq | Hne].
      - (* the list of p itself: its end is past ws *)
        rewrite Heq, Hext, length_app. lia.
      - (* another list: its room is apart *)
        rewrite Hext, length_app in Hcap_p.
        apply (pool_apart m S N lss xc lims (lit_key p) (lit_key r) q _ HRep).
        + assumption.
        + assumption.
        + intros Heq. apply Hne. symmetry. assumption.
        + lia.
        + lia. }
    constructor; try assumption.
    - (* the watchers kept *)
      intros q Hq. apply set_watcher_other.
      + apply Hapart. lia.
      + apply Hfront. assumption.
    - (* ws from k on *)
      intros q Hq. apply set_watcher_other.
      + apply Hapart. lia.
      + apply Hback. lia.
    - (* the list of p grows when r is p *)
      cbn [set_watching wls]. rewrite watching_add.
      destruct (Lit.eq_dec r p) as [<- | Hne].
      + exists (extra ++ [(i, b)]). rewrite Hext, app_assoc. reflexivity.
      + exists extra. assumption.
  Qed.

  (* Ending the visit: the watchers kept become the watch list of p.

       s->wlen[p] = j;                                             (rep_store_watching) *)
  Lemma visit_mem_finish: forall (k: nat) (kept: list Watcher) (xc: Ctx) (t: nat -> Z)
    (m m': mem),
    VisitMem S N lss lims x p k kept xc t m ->
    Mem.store Mint32 m (b_wlen S) (4 * Z.of_nat (lit_key p))
      (vint (Z.of_nat (length kept))) = Some m' ->
    Rep m' S N lss (set_watching xc p (rev kept)) lims.
  Proof.
    intros k kept xc t m m' HM Hst.
    pose proof (visit_room k kept xc t m HM) as (Hcap & Hroom & Hsmall).
    destruct HM as [Hp Hle HRep Apool Hpool Hfront _ _ Hkept].
    pose proof (r_nodup _ _ _ _ _ _ HRep) as Hnd.
    rewrite <- (length_rev kept) in Hst. split.
    - apply (rep_store_watching m m' S N lss xc lims p (rev kept) HRep Hp).
      + rewrite length_rev. lia.
      + intros i b Hin. apply Hkept. apply in_rev. assumption.
      + assumption.
    - exists t. split.
      + apply (arr_store_other _ _ _ _ _ _ _ _ _ Apool Hst). neq Hnd.
      + apply (pool_finish S N t (wls xc) (lit_key p) (length (watching (wls x) p))).
        * assumption.
        * intros q Hq. rewrite length_rev in Hq. apply Hfront. assumption.
  Qed.
End Memory.

(* The invariant of the loop of keep_rest at position z: the watchers kept and ws from z
   on are the watch list L that the visit leaves. *)
Definition rest_inv (S: Shape) (N: nat) (lss: list (list Lit)) (lims: list nat)
  (x: Ctx) (p: Lit) (xc: Ctx) (L: list Watcher) (z: nat) (le: temp_env) (m: mem): Prop :=
  exists (kept: list Watcher) (t: nat -> Z),
  VisitTemps S x p (length kept) z le /\ VisitMem S N lss lims x p z kept xc t m /\
  rev_append kept (skipn z (watching (wls x) p)) = L.

(* keep_rest keeps the watchers of ws from k on, after the j = length kept already kept,
   and ends the visit:

     {{ VisitMem k kept xc }}
       int base = 2 * s->woff[p];
     {{ rest_inv k }}
       while (k < n) {                                            (invariant rest_inv)
         s->wpool[base + 2 * j] = s->wpool[base + 2 * k];
         s->wpool[base + 2 * j + 1] = s->wpool[base + 2 * k + 1];      (visit_mem_keep)
         j++; k++;
       }
     {{ rest_inv n: the watchers kept are L }}
       s->wlen[p] = j;                                               (visit_mem_finish)
       return 1;
     {{ result = 1 /\ Rep (set_watching xc p L), L = rev_append kept (ws from k on) }}

   The loop ends: n - k decreases. *)
Lemma keep_rest_correct: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (lims: list nat) (x: Ctx) (p: Lit) (k: nat) (kept: list Watcher) (xc: Ctx)
    (t: nat -> Z),
  {{ m | VisitMem S N lss lims x p k kept xc t m }}
    f_keep_rest(sptr S, vint (key p), vint (Z.of_nat (length kept)), vint (Z.of_nat k),
                vint (Z.of_nat (length (watching (wls x) p))))
  {{ m', v | v = vint 1 /\
             Rep m' S N lss
               (set_watching xc p (rev_append kept (skipn k (watching (wls x) p)))) lims
                 }}.
Proof.
  intros S N lss lims x p k kept xc t m HM.
  pose proof (visit_room S N lss lims x p k kept xc t m HM) as (Hcap & Hroom & Hsmall).
  pose proof HM as [Hp _ HRep _ _ _ _ _ _].
  pose proof (key_small p N Hp (r_n _ _ _ _ _ _ HRep)) as Hkp.
  pose proof (lit_key_lt p N Hp) as HP.
  set (L := rev_append kept (skipn k (watching (wls x) p))).
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_keep_rest. cbn [fn_body fn_return].
    pose proof (r_woff _ _ _ _ _ _ HRep) as Fwoff.
    pose proof (a_woff _ _ _ _ _ _ HRep) as Awoff.
    assert (Hbase: Int.mul (Int.repr 2) (Int.repr (Z.of_nat (offs S (lit_key p))))
                   = Int.repr (Z.of_nat (2 * offs S (lit_key p)))).
    { rewrite mul_repr. f_equal. lia. }
    (* int base = 2 * s->woff[p]; *)
    run. clear Fwoff Awoff. ints. unfold Swhile.
    apply exec_loop
      with (R := ltof nat (fun (z: nat) => length (watching (wls x) p) - z)%nat)
      (I := rest_inv S N lss lims x p xc L) (a := k).
    + apply well_founded_ltof.
    + intros z le1 m1 (kept1 & t1 & HT1 & HM1 & HL).
      pose proof HM1 as [_ Hle HRep1 Apool _ _ Hback _ _].
      pose proof (r_wpool _ _ _ _ _ _ HRep1) as Fwpool.
      pose proof HT1 as [Hs Hpk Hbase1 Hn Hj Hk].
      (* while (k < n) *)
      apply exec_seq. eapply (exec_if_cmp _ _ _ Clt).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * destruct (Nat.lt_ge_cases z (length (watching (wls x) p))) as [Hzn | Hzn].
        -- (* copy watcher z to position j; j++; k++; *)
           replace (zcmp Clt (Z.of_nat z) (Z.of_nat (length (watching (wls x) p))))
             with true by (symmetry; cbn [zcmp]; apply Z.ltb_lt; lia).
           destruct (visit_watcher S N lss lims x p z kept1 xc t1 m1 z HM1 Hzn) as
             [Hi Hb].
           destruct (Hback z) as [Hz1 Hz2].
           { lia. }
           set (e := nth z (watching (wls x) p) (0%nat, Pos 0%nat)) in *.
           pose proof (key_small (snd e) N Hb (r_n _ _ _ _ _ _ HRep1)) as Hkb.
           destruct (watcher_entry (offs S (lit_key p)) z ltac:(lia)) as [Hez Hez1].
           destruct (watcher_entry (offs S (lit_key p)) (length kept1) ltac:(lia))
             as [Hej Hej1].
           assert (Hj_incr: Int.add (Int.repr (Z.of_nat (length kept1))) (Int.repr 1)
                            = Int.repr (Z.of_nat (length (e :: kept1)))).
           { apply incr_nat. lia. }
           assert (Hz_incr: Int.add (Int.repr (Z.of_nat z)) (Int.repr 1)
                            = Int.repr (Z.of_nat (Datatypes.S z))).
           { apply incr_nat. lia. }
           assert (Hlt: (2 * (offs S (lit_key p) + length kept1) + 1 < 2 * npool S)%nat)
             by lia.
           cbv beta iota. apply exec_skip. normal.
           (* s->wpool[base + 2 * j] = s->wpool[base + 2 * k]; *)
           run. rewrite Hz1. eapply exec_store.
           ++ evl.
           ++ ev.
           ++ reflexivity.
           ++ reflexivity.
           ++ ofs. bound.
           ++ ofs. cbn [cast_int_int].
              destruct (arr_storable m1 (b_wpool S) (2 * npool S)
                          (2 * (offs S (lit_key p) + length kept1)) t1
                          (Z.of_nat (fst e)) Apool ltac:(lia)) as [m2 Hst2].
              exists m2. split.
              ** apply Hst2.
              ** normal.
                 pose proof
                   (arr_store _ _ _ _ (2 * (offs S (lit_key p) + length kept1)) _ _
                               Apool ltac:(lia) Hst2) as Apool2.
                 assert (Hz2': (if Nat.eqb (2 * (offs S (lit_key p) + length kept1))
                                     (2 * (offs S (lit_key p) + z) + 1)
                                then Z.of_nat (fst e) else t1
                                  (2 * (offs S (lit_key p) + z) + 1)%nat)
                               = key (snd e)).
                 { replace (Nat.eqb _ _) with false by (symmetry; apply Nat.eqb_neq; lia).
                   assumption. }
                 pose proof
                   (rep_store_pool m1 m2 S N lss xc lims _ _ HRep1 Hst2) as HRep2.
                 pose proof (Rep.r_wpool _ _ _ _ _ _ HRep2) as Fwpool2.
                 (* s->wpool[base + 2 * j + 1] = s->wpool[base + 2 * k + 1]; *)
                 run. rewrite Hz2'. eapply exec_store.
                 --- evl.
                 --- ev.
                 --- reflexivity.
                 --- reflexivity.
                 --- ofs. bound.
                 --- ofs. cbn [cast_int_int].
                     destruct (arr_storable m2 (b_wpool S) (2 * npool S)
                                 (2 * (offs S (lit_key p) + length kept1) + 1) _
                                 (key (snd e)) Apool2 Hlt) as [m3 Hst3].
                     exists m3. split.
                     +++ apply Hst3.
                     +++ normal. run. ints. apply loopk_next with (Datatypes.S z).
                         *** unfold ltof. lia.
                         *** exists (e :: kept1). eexists. split.
                             ---- constructor; tmp.
                             ---- split.
                                  ++++ apply (visit_mem_keep S N lss lims x p z kept1 xc
                                         t1 e
                                                m1 m2 m3).
                                       **** assumption.
                                       **** assumption.
                                       **** assumption.
                                       **** assumption.
                                       **** assumption.
                                       **** assumption.
                                  ++++ (* watcher z moved from ws to the watchers kept *)
                                       rewrite (skipn_nth (watching (wls x) p)
                                         (0%nat, Pos 0%nat) z Hzn) in HL.
                                       fold e in HL. cbn [rev_append]. assumption.
        -- (* break; s->wlen[p] = j; return 1; *)
           replace (zcmp Clt (Z.of_nat z) (Z.of_nat (length (watching (wls x) p))))
             with false by (symmetry; cbn [zcmp]; apply Z.ltb_ge; lia).
           cbv beta iota. apply exec_break. abrupt. apply loopk_break. normal.
           pose proof (r_nodup _ _ _ _ _ _ HRep1) as Hnd.
           pose proof (r_wlen _ _ _ _ _ _ HRep1) as Fwlen.
           pose proof (a_wlen _ _ _ _ _ _ HRep1) as Awlen.
           pose proof Hkp as Hkp'. unfold key in Hkp'.
           run. eapply exec_store.
           ++ evl.
           ++ ev.
           ++ reflexivity.
           ++ reflexivity.
           ++ ofs. bound.
           ++ ofs. cbn [cast_int_int].
              destruct (arr_storable m1 (b_wlen S) (2 * N) (lit_key p) _
                          (Z.of_nat (length kept1)) Awlen HP) as [m2 Hst2].
              exists m2. split.
              ** apply Hst2.
              ** normal. eapply exec_return.
                 --- ev.
                 --- exists (vint 1). split.
                     +++ apply result_int.
                     +++ split.
                         *** reflexivity.
                         *** (* nothing is left of ws: the watchers kept are L *)
                             rewrite skipn_all2 in HL by lia.
                             rewrite rev_append_rev, app_nil_r in HL.
                             rewrite <- HL.
                             apply (visit_mem_finish S N lss lims x p z kept1 xc t1 m1
                               m2).
                             ---- assumption.
                             ---- assumption.
    + (* The invariant holds at k. *)
      exists kept, t. split.
      * constructor; tmp.
      * split.
        -- assumption.
        -- reflexivity.
Qed.

Lemma keep_rest_fun: exists (b: block),
  Genv.find_symbol ge _keep_rest = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_keep_rest).
Proof. apply find_fun. reflexivity. Qed.
