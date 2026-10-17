(* The store lemmas of the analysis and the reason clauses (see Rep.v): what a store to
   the marks, reasons, levels, lower literals or reason clauses does to the represented
   context, and jumping back to an older level. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs Ctypes Cop
  Clight ClightBigstep.
From RocqSAT Require Import Lit Assignment.
From RocqSAT.refinement Require Import Table Lookup Watches Heur Propagate Analysis Step
  CStep SolverStep.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep.
Import ListNotations.

(* The first entries of the reversal of a list are those of the reversal of its end. *)
Lemma nth_rev_skipn: forall {A: Type} (l: list A) (n j: nat) (d: A),
  (j < length (skipn n l))%nat -> nth j (rev l) d = nth j (rev (skipn n l)) d.
Proof.
  intros A l n j d Hj. rewrite <- (firstn_skipn n l) at 1. rewrite rev_app_distr.
  apply app_nth1. rewrite length_rev. assumption.
Qed.

(* Jumping back over the k + 1 newest decisions: the cursor c0 saved for the oldest of
   them comes back, and the length st of the saved cursors left is the decision level.
   s->cur = s->saved[d]; s->dl = d, for d = length st. *)
Lemma rep_store_level {lt: list Lit}: forall (m m1 m2: mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (k c0: nat) (st: list nat),
  RepL m S N lss x lims lt -> skipn k (saved x) = c0 :: st ->
  Mem.store Mint32 m (b_s S) 116 (vint (Z.of_nat c0)) = Some m1 ->
  Mem.store Mint32 m1 (b_s S) 136 (vint (Z.of_nat (length st))) = Some m2 ->
  RepL m2 S N lss (set_level x c0 st (length st)) (skipn (Datatypes.S k) lims) lt.
Proof.
  intros m m1 m2 S N lss x lims k c0 st HRep Hsv Hst1 Hst2.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_saved_le _ _ _ _ _ _ _ HRep) as Hsle.
  pose proof (r_saved_len _ _ _ _ _ _ _ HRep) as Hslen.
  pose proof (r_dl_le _ _ _ _ _ _ _ HRep) as Hdle.
  pose proof (a_saved _ _ _ _ _ _ _ HRep) as (tsv & Asaved & Htsv).
  pose proof (a_lims _ _ _ _ _ _ _ HRep) as (tl & Alims & Htl).
  pose proof (r_dl _ _ _ _ _ _ _ HRep) as Fdl.
  pose proof (fld_store m m1 (b_s S) 116 Mint32 _ _ (r_cur _ _ _ _ _ _ _ HRep) Hst1)
    as Fcur1.
  (* The saved cursors are those before position k, c0 and st; as many as decisions. *)
  assert (Hsplit: saved x = firstn k (saved x) ++ c0 :: st).
  { rewrite <- Hsv. symmetry. apply firstn_skipn. }
  assert (Hin: forall (c: nat), In c (c0 :: st) -> In c (saved x)).
  { intros c Hc. rewrite Hsplit. apply in_or_app. now right. }
  assert (Hlen: length st = length (skipn (Datatypes.S k) lims)).
  { rewrite length_skipn, <- Hslen.
    assert (Hk: length (skipn k (saved x)) = Datatypes.S (length st))
      by now rewrite Hsv.
    rewrite length_skipn in Hk. lia. }
  assert (Hst: st = skipn (Datatypes.S k) (saved x)).
  { rewrite <- (skipn_skipn 1 k), Hsv. reflexivity. }
  destruct HRep. unpack. carry Hst1 Hnd.
  pose proof (fld_store m1 m2 (b_s S) 136 Mint32 _ _ Fdl Hst2) as Fdl2.
  carry Hst2 Hnd. cbn [Val.load_result] in Fcur1, Fdl2.
  (* Every field is as before, but the cursor, the saved cursors and the decision
     positions, which lose their newest k + 1 entries; Hlen gives their number. *)
  constructor; try assumption.
  - (* the number of decisions *)
    rewrite <- Hlen. assumption.
  - repack.
  - repack.
  - repack.
  - (* the saved cursors: the first entries of the same array *)
    exists tsv. split.
    + assumption.
    + intros j Hj. cbn [set_level saved] in Hj |- *. rewrite Htsv.
      * rewrite Hst. f_equal. apply nth_rev_skipn. rewrite <- Hst. assumption.
      * rewrite Hslen. rewrite Hlen, length_skipn in Hj. lia.
  - (* the decision positions: the first entries of the same array *)
    exists tl. split.
    + assumption.
    + intros j Hj. rewrite Htl.
      * f_equal. apply nth_rev_skipn. assumption.
      * rewrite length_skipn in Hj. lia.
  - (* the cursor was saved, so it is within the literals to decide on *)
    cbn [set_level cur nlits]. apply Hsle. apply Hin. now left.
  - (* the cursors still saved *)
    intros c Hc. cbn [set_level saved nlits] in *. apply Hsle. apply Hin. now right.
  - (* the decisions within the atoms *)
    rewrite length_skipn. lia.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
Qed.

(* Marking (b = true) or unmarking the literal with key k: s->mrk[k] = enc_mark b. *)
Lemma rep_store_mrk {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (k: nat) (b: bool),
  RepL m S N lss x lims lt -> (k < 2 * N)%nat ->
  Mem.store Mint32 m (b_mrk S) (4 * Z.of_nat k) (vint (enc_mark b)) = Some m' ->
  RepL m' S N lss (set_mrk x (tset (mrk x) k b)) lims lt.
Proof.
  intros m m' S N lss x lims k b HRep Hk Hst.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (arr_store m m' (b_mrk S) (2 * N) k _ _ (a_mrk _ _ _ _ _ _ _ HRep) Hk Hst)
    as Amrk.
  destruct HRep. unpack. carry Hst Hnd.
  (* Every field but the marks is as before. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* the marks: key k now has mark b *)
    cbn [set_mrk mrk]. arr_tset.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
Qed.

(* Storing the reason r of atom a: s->rsn[a] = enc_reason r. *)
Lemma rep_store_rsn {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (a: nat) (r: Reason),
  RepL m S N lss x lims lt -> (a < N)%nat -> ReasonBelow (length lss) N r ->
  Mem.store Mint32 m (b_rsn S) (4 * Z.of_nat a) (vint (enc_reason r)) = Some m' ->
  RepL m' S N lss (set_rsn x (tset (rsn x) a r)) lims lt.
Proof.
  intros m m' S N lss x lims a r HRep Ha Hr Hst.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_rsn_below _ _ _ _ _ _ _ HRep) as Hbelow.
  pose proof (arr_store m m' (b_rsn S) N a _ _ (a_rsn _ _ _ _ _ _ _ HRep) Ha Hst) as
    Arsn.
  destruct HRep. unpack. carry Hst Hnd.
  (* Every field but the reasons is as before. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* the reasons: atom a now has reason r *)
    cbn [set_rsn rsn]. arr_tset.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* the reasons have clauses that C can find, r too *)
    intros a' Ha'. cbn [set_rsn rsn]. rewrite tget_tset.
    destruct (Nat.eq_dec a a') as [<- | Hne].
    + assumption.
    + apply Hbelow. assumption.
Qed.

(* Storing the level d of atom a: s->lvl[a] = d. *)
Lemma rep_store_lvl {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (a d: nat),
  RepL m S N lss x lims lt -> (a < N)%nat -> (d <= N)%nat ->
  Mem.store Mint32 m (b_lvl S) (4 * Z.of_nat a) (vint (Z.of_nat d)) = Some m' ->
  RepL m' S N lss (set_lvl x (tset (lvl x) a d)) lims lt.
Proof.
  intros m m' S N lss x lims a d HRep Ha Hd Hst.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_lvl_le _ _ _ _ _ _ _ HRep) as Hlvl.
  pose proof (arr_store m m' (b_lvl S) N a _ _ (a_lvl _ _ _ _ _ _ _ HRep) Ha Hst) as
    Alvl.
  destruct HRep. unpack. carry Hst Hnd.
  (* Every field but the levels is as before. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* the levels: atom a now has level d *)
    cbn [set_lvl lvl]. arr_tset.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* the levels are at most N, d too *)
    intros a' Ha'. cbn [set_lvl lvl]. rewrite tget_tset.
    destruct (Nat.eq_dec a a') as [<- | Hne].
    + assumption.
    + apply Hlvl. assumption.
Qed.

(* Appending y to the lower literals of the analysis: s->lt[n] = y; s->ltlen = n + 1, for
   n = length lt. *)
Lemma rep_store_lt {lt: list Lit}: forall (m m1 m2: mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (y: Lit),
  RepL m S N lss x lims lt -> (length lt < N)%nat -> (extract y < N)%nat ->
  Mem.store Mint32 m (b_lt S) (4 * Z.of_nat (length lt)) (vint (key y)) = Some m1 ->
  Mem.store Mint32 m1 (b_s S) 184 (vint (Z.of_nat (Datatypes.S (length lt)))) = Some m2
    ->
  RepL m2 S N lss x lims (lt ++ [y]).
Proof.
  intros m m1 m2 S N lss x lims y HRep Hlen Hy Hst1 Hst2.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_lt_atoms _ _ _ _ _ _ _ HRep) as Hatoms.
  pose proof (a_lt _ _ _ _ _ _ _ HRep) as (tlt & Alt & Htlt).
  pose proof (r_ltlen _ _ _ _ _ _ _ HRep) as Fltlen.
  pose proof (arr_store m m1 (b_lt S) N (length lt) _ _ Alt Hlen Hst1) as Alt1.
  destruct HRep. unpack. carry Hst1 Hnd.
  pose proof (fld_store m1 m2 (b_s S) 184 Mint32 _ _ Fltlen Hst2) as Fltlen2.
  carry Hst2 Hnd. cbn [Val.load_result] in Fltlen2.
  (* Every field but the lower literals is as before. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* their number *)
    rewrite length_app. cbn [length]. rewrite Nat.add_1_r. assumption.
  - (* y is the new last entry *)
    eexists. split.
    + apply Alt1.
    + intros k Hk. rewrite length_app in Hk. cbn [length] in Hk.
      destruct (Nat.eq_dec (length lt) k) as [<- | Hne].
      * rewrite Nat.eqb_refl, nth_middle. reflexivity.
      * replace (Nat.eqb (length lt) k) with false by (symmetry; now apply Nat.eqb_neq).
        rewrite app_nth1 by lia. apply Htlt. lia.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* at most N of them *)
    rewrite length_app. cbn [length]. lia.
  - (* with atoms below N, y too *)
    intros y' Hy'. apply in_app_or in Hy' as [Hy' | [<- | []]].
    + apply Hatoms. assumption.
    + assumption.
Qed.

(* Ending the analysis: s->ltlen = 0. *)
Lemma rep_store_ltlen_zero {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat),
  RepL m S N lss x lims lt -> Mem.store Mint32 m (b_s S) 184 (vint 0) = Some m' ->
  RepB m' S N lss x lims.
Proof.
  intros m m' S N lss x lims HRep Hst.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (fld_store m m' (b_s S) 184 Mint32 _ _ (r_ltlen _ _ _ _ _ _ _ HRep) Hst)
    as Fltlen.
  cbn [Val.load_result] in Fltlen. destruct HRep. unpack. carry Hst Hnd.
  (* Every field but the lower literals is as before, and there are none. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - eexists. split.
    + eassumption.
    + intros k Hk. cbn [length] in Hk. lia.
  - repack.
  - repack.
  - repack.
  - repack.
  - cbn [length]. lia.
  - intros y [].
Qed.

(* Dropping the reason clauses from n on, n <= nr x: s->rtop = s->rbeg[n]; s->nr = n. *)
Lemma rep_store_pop {lt: list Lit}: forall (m m1 m2: mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (n: nat),
  RepL m S N lss x lims lt -> (n <= nr x)%nat ->
  Mem.store Mint32 m (b_s S) 204 (vint (Z.of_nat (reasons_size (rcl x) n))) = Some m1 ->
  Mem.store Mint32 m1 (b_s S) 232 (vint (Z.of_nat n)) = Some m2 ->
  RepL m2 S N lss (set_nr x n) lims lt.
Proof.
  intros m m1 m2 S N lss x lims n HRep Hn Hst1 Hst2.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_rsize_le _ _ _ _ _ _ _ HRep) as Hsize.
  pose proof (r_rcl_atoms _ _ _ _ _ _ _ HRep) as Hatoms.
  pose proof (r_rps_le _ _ _ _ _ _ _ HRep) as Hrps.
  pose proof (a_rlits _ _ _ _ _ _ _ HRep) as (trl & Arl & Htrl).
  pose proof (a_rbeg _ _ _ _ _ _ _ HRep) as (tb & Arb & Htb).
  pose proof (a_rlen _ _ _ _ _ _ _ HRep) as (tn & Arn & Htn).
  pose proof (a_rpos _ _ _ _ _ _ _ HRep) as (tp & Arp & Htp).
  pose proof (r_nr _ _ _ _ _ _ _ HRep) as Fnr.
  pose proof (fld_store m m1 (b_s S) 204 Mint32 _ _ (r_rtop _ _ _ _ _ _ _ HRep) Hst1)
    as Frtop.
  destruct HRep. unpack. carry Hst1 Hnd.
  pose proof (fld_store m1 m2 (b_s S) 232 Mint32 _ _ Fnr Hst2) as Fnr2.
  carry Hst2 Hnd. cbn [Val.load_result] in Frtop, Fnr2.
  (* Every field is as before, but the reason clauses, which keep their first n. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* their literals *)
    exists trl. split.
    + assumption.
    + intros j k Hj Hk. apply Htrl.
      * cbn [set_nr nr] in Hj. lia.
      * assumption.
  - (* their starts *)
    exists tb. split.
    + assumption.
    + intros j Hj. apply Htb. cbn [set_nr nr] in Hj. lia.
  - (* their lengths *)
    exists tn. split.
    + assumption.
    + intros j Hj. apply Htn. cbn [set_nr nr] in Hj. lia.
  - (* their trail positions *)
    exists tp. split.
    + assumption.
    + intros j Hj. apply Htp. cbn [set_nr nr] in Hj. lia.
  - (* at most N of them *)
    cbn [set_nr nr]. lia.
  - (* within the room, as the first n take less than all *)
    cbn [set_nr nr rcl rcap]. transitivity (reasons_size (rcl x) (nr x)).
    + apply reasons_size_le. assumption.
    + assumption.
  - (* their atoms *)
    intros j y Hj Hy. apply (Hatoms j y).
    + cbn [set_nr nr] in Hj. lia.
    + assumption.
  - (* their trail positions are at most N *)
    intros j Hj. apply Hrps. cbn [set_nr nr] in Hj. lia.
Qed.

(* Setting the marks to what they are keeps the representation. *)
Lemma rep_mrk_same {lt: list Lit}: forall (m: mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat),
  RepL m S N lss x lims lt -> RepL m S N lss (set_mrk x (mrk x)) lims lt.
Proof. intros m S N lss x lims HRep. destruct HRep. constructor; assumption. Qed.

(* Keeping all the reason clauses keeps the representation. *)
Lemma rep_nr_same {lt: list Lit}: forall (m: mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (n: nat),
  RepL m S N lss x lims lt -> n = nr x -> RepL m S N lss (set_nr x n) lims lt.
Proof. intros m S N lss x lims n HRep ->. destruct HRep. constructor; assumption. Qed.

(* Pushing reason clause nr x after its literals, start, length and trail position were
   stored in the blocks rlits, rbeg, rlen and rpos, with nothing else changed:
   s->rtop = reasons_size; s->nr = nr x + 1, for x' = add_reason x c. *)
Lemma rep_store_push {lt: list Lit}: forall (m m1 m2 m3: mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (c: list Lit)
    (trl tb tn tp: nat -> Z),
  RepL m S N lss x lims lt -> (nr x < N)%nat ->
  (reasons_size (rcl x) (nr x) + length c <= rcap x)%nat ->
  (forall (y: Lit), In y c -> (extract y < N)%nat) ->
  Mem.unchanged_on
    (fun (b: block)
      (_: Z) => b <> b_rlits S /\ b <> b_rbeg S /\ b <> b_rlen S /\ b <> b_rpos S) m m1
        ->
  Arr m1 (b_rlits S) (rcap x) trl -> ReasonsIn trl (rcl (add_reason x c))
    (nr (add_reason x c)) ->
  Arr m1 (b_rbeg S) N tb ->
  (forall (j: nat), (j <= nr x)%nat -> tb j = Z.of_nat (reasons_size (rcl x) j)) ->
  Arr m1 (b_rlen S) N tn ->
  (forall (j: nat), (j <= nr x)%nat -> tn j = Z.of_nat (length (tget (rcl (add_reason x
    c)) j))) ->
  Arr m1 (b_rpos S) N tp ->
  (forall (j: nat), (j <= nr x)%nat -> tp j = Z.of_nat (tget (rps (add_reason x c)) j))
    ->
  Mem.store Mint32 m1 (b_s S) 204
    (vint (Z.of_nat (reasons_size (rcl x) (nr x) + length c))) = Some m2 ->
  Mem.store Mint32 m2 (b_s S) 232 (vint (Z.of_nat (Datatypes.S (nr x)))) = Some m3 ->
  RepL m3 S N lss (add_reason x c) lims lt.
Proof.
  intros m m1 m2 m3 S N lss x lims c trl tb tn tp HRep Hnr Hroom Hc Hun Arl Htrl Arb Htb
    Arn Htn Arp Htp Hst2 Hst3.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_tlen_le _ _ _ _ _ _ _ HRep) as Htlen.
  pose proof (r_rcl_atoms _ _ _ _ _ _ _ HRep) as Hatoms.
  pose proof (r_rps_le _ _ _ _ _ _ _ HRep) as Hrps.
  pose proof (r_nr _ _ _ _ _ _ _ HRep) as Fnr.
  pose proof (r_rtop _ _ _ _ _ _ _ HRep) as Frtop.
  (* The size of the reason clauses with c. *)
  assert (Hsize: reasons_size (rcl (add_reason x c)) (nr (add_reason x c))
                 = (reasons_size (rcl x) (nr x) + length c)%nat).
  { cbn [add_reason rcl nr reasons_size]. rewrite reasons_size_tset by lia.
    rewrite tget_tset_same. reflexivity. }
  destruct HRep. unpack. transfer Hun Hnd. keep_mem m1.
  pose proof (fld_store m1 m2 (b_s S) 204 Mint32 _ _ Frtop Hst2) as Frtop2.
  carry Hst2 Hnd.
  pose proof (fld_store m2 m3 (b_s S) 232 Mint32 _ _ Fnr Hst3) as Fnr3.
  carry Hst3 Hnd. cbn [Val.load_result] in Frtop2, Fnr3. rewrite <- Hsize in Frtop2.
  (* Every field is as before, but the reason clauses, which get c; Hnr bounds their
     number. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* their literals *)
    exists trl. split.
    + assumption.
    + assumption.
  - (* their starts *)
    exists tb. split.
    + assumption.
    + intros j Hj. cbn [add_reason nr rcl] in Hj |- *. rewrite reasons_size_tset by lia.
      apply Htb. lia.
  - (* their lengths *)
    exists tn. split.
    + assumption.
    + intros j Hj. apply Htn. cbn [add_reason nr] in Hj. lia.
  - (* their trail positions *)
    exists tp. split.
    + assumption.
    + intros j Hj. apply Htp. cbn [add_reason nr] in Hj. lia.
  - (* within the room *)
    rewrite Hsize. cbn [add_reason rcap]. assumption.
  - (* their atoms, those of c too *)
    intros j y Hj Hy. cbn [add_reason nr rcl] in Hj, Hy. rewrite tget_tset in Hy.
    destruct (Nat.eq_dec (nr x) j) as [<- | Hne].
    + apply Hc. assumption.
    + apply (Hatoms j y).
      * lia.
      * assumption.
  - (* their trail positions are at most N, the end of the trail too *)
    intros j Hj. cbn [add_reason nr rps] in Hj |- *. rewrite tget_tset.
    destruct (Nat.eq_dec (nr x) j) as [<- | Hne].
    + assumption.
    + apply Hrps. lia.
Qed.
