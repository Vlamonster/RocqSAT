(* The store lemmas of the analysis and the reason clauses (see Rep.v): what a store to
   the marks, reasons, levels, lower literals or reason clauses does to the represented
   context, and jumping back to an older level. *)
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
From RocqSAT Require Import Assignment.
From RocqSAT.refinement Require Import Table.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import Heur.
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement Require Import Analysis.
From RocqSAT.refinement Require Import Step.
From RocqSAT.refinement Require Import SolverStep.
From RocqSAT.refinement.c Require Import Arrays.
From RocqSAT.refinement.c Require Import Logic.
From RocqSAT.refinement.c Require Import Common.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Rep.

(* Every block but the arrays of the reason clauses. *)
Abbreviation ReasonFrame sh :=
  (fun (b: block) (_: Z) =>
     b <> b_rlits sh /\ b <> b_rbeg sh /\ b <> b_rlen sh /\ b <> b_rpos sh).

(* Every block but the arrays of the reason clauses and s. *)
Abbreviation PushFrame sh :=
  (fun (b: block) (_: Z) =>
     b <> b_rlits sh /\ b <> b_rbeg sh /\ b <> b_rlen sh /\ b <> b_rpos sh /\
     b <> b_s sh).

(* The first entries of the reversal of a list are those of the reversal of its end. *)
Lemma nth_rev_skipn: forall {A: Type} (l: list A) (n j: nat) (d: A),
  (j < length (skipn n l))%nat -> nth j (rev l) d = nth j (rev (skipn n l)) d.
Proof.
  intros A l n j d Hj. rewrite <- (firstn_skipn n l) at 1. rewrite rev_app_distr.
  apply app_nth1. rewrite length_rev. assumption.
Qed.

Section Stores.
  Context {sh: Shape} {N: nat} {lss: list (list Lit)} {x: Ctx}.

  (* Jumping back over the k + 1 newest decisions: the cursor c0 saved for the oldest of
     them comes back, and the length st of the saved cursors left is the decision level.
     s->cur = s->saved[d]; s->dl = d, for d = length st. *)
  Lemma rep_store_level: forall (m m1 m2: mem) (k c0: nat) (st: list nat),
    RepL m sh N lss x -> skipn k (saved x) = c0 :: st ->
    Mem.store Mint32 m (b_s sh) o_cur (vnat c0) = Some m1 ->
    Mem.store Mint32 m1 (b_s sh) o_dl (vnat (length st)) = Some m2 ->
    RepL m2 sh N lss (set_level x c0 st (length st) (skipn (S k) (lims x))).
  Proof.
    intros m m1 m2 k c0 st HRep Hsv Hst1 Hst2.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (r_saved_le HRep) as Hsle.
    pose proof (r_saved_len HRep) as Hslen.
    pose proof (r_dl_le HRep) as Hdle.
    pose proof (a_saved HRep) as (tsv & Asaved & Htsv).
    pose proof (a_lims HRep) as (tl & Alims & Htl).
    pose proof (r_dl HRep) as Fdl.
    pose proof (fld_store (r_cur HRep) Hst1) as Fcur1.
    (* The saved cursors are those before position k, c0 and st; as many as decisions. *)
    assert (Hsplit: saved x = firstn k (saved x) ++ c0 :: st).
    { rewrite <- Hsv. symmetry. apply firstn_skipn. }
    assert (Hin: forall (c: nat), In c (c0 :: st) -> In c (saved x)).
    { intros c Hc. rewrite Hsplit. apply in_or_app. now right. }
    assert (Hlen: length st = length (skipn (S k) (lims x))).
    { rewrite length_skipn, <- Hslen.
      assert (Hk: length (skipn k (saved x)) = S (length st))
        by now rewrite Hsv.
      rewrite length_skipn in Hk. lia. }
    assert (Hst: st = skipn (S k) (saved x)).
    { rewrite <- (skipn_skipn 1 k), Hsv. reflexivity. }
    destruct HRep. carry Hst1 Hnd.
    pose proof (fld_store Fdl Hst2) as Fdl2.
    carry Hst2 Hnd. cbn [Val.load_result] in Fcur1, Fdl2.
    (* Every field is as before, but the cursor, the saved cursors and the decision
       positions, which lose their newest k + 1 entries; Hlen gives their number. *)
    constructor; try assumption.
    - (* the number of decisions *)
      cbn [set_level lims]. rewrite <- Hlen. assumption.
    - (* the saved cursors: the first entries of the same array *)
      exists tsv. split.
      + assumption.
      + intros j Hj. cbn [set_level saved] in Hj |- *. rewrite Htsv.
        * rewrite Hst. f_equal. apply nth_rev_skipn. rewrite <- Hst. assumption.
        * rewrite Hslen. rewrite Hlen, length_skipn in Hj. lia.
    - (* the decision positions: the first entries of the same array *)
      exists tl. split.
      + assumption.
      + intros j Hj. cbn [set_level lims] in Hj |- *. rewrite Htl.
        * f_equal. apply nth_rev_skipn. assumption.
        * rewrite length_skipn in Hj. lia.
    - (* the cursor was saved, so it is within the literals to decide on *)
      cbn [set_level cur nlits]. apply Hsle. apply Hin. now left.
    - (* the cursors still saved *)
      intros c Hc. cbn [set_level saved nlits] in *. apply Hsle. apply Hin. now right.
    - (* the decisions within the atoms *)
      cbn [set_level lims]. rewrite length_skipn. lia.
  Qed.

  (* Marking (b = true) or unmarking the literal with key k: s->mrk[k] = enc_mark b. *)
  Lemma rep_store_mrk: forall (m m': mem) (k: nat) (b: bool),
    RepL m sh N lss x -> (k < 2 * N)%nat ->
    Mem.store Mint32 m (b_mrk sh) (4 * Z.of_nat k) (vint (enc_mark b)) = Some m' ->
    RepL m' sh N lss (x <| mrk := tset (mrk x) k b |>).
  Proof.
    intros m m' k b HRep Hk Hst.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (arr_store (a_mrk HRep) Hk Hst) as Amrk.
    destruct HRep. carry Hst Hnd.
    (* Every field but the marks is as before. *)
    constructor; try assumption.
    - (* the marks: key k now has mark b *)
      cbn [set_mrk mrk]. arr_tset.
  Qed.

  (* Storing the reason r of atom a: s->rsn[a] = enc_reason r. *)
  Lemma rep_store_rsn: forall (m m': mem) (a: nat) (r: Reason),
    RepL m sh N lss x -> (a < N)%nat -> ReasonBelow (length lss) N r ->
    Mem.store Mint32 m (b_rsn sh) (4 * Z.of_nat a) (vint (enc_reason r)) = Some m' ->
    RepL m' sh N lss (x <| rsn := tset (rsn x) a r |>).
  Proof.
    intros m m' a r HRep Ha Hr Hst.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (r_rsn_below HRep) as Hbelow.
    pose proof (arr_store (a_rsn HRep) Ha Hst) as Arsn.
    destruct HRep. carry Hst Hnd.
    (* Every field but the reasons is as before. *)
    constructor; try assumption.
    - (* the reasons: atom a now has reason r *)
      cbn [set_rsn rsn]. arr_tset.
    - (* the reasons have clauses that C can find, r too *)
      intros a' Ha'. cbn [set_rsn rsn]. rewrite tget_tset.
      destruct (Nat.eq_dec a a') as [<- | Hne].
      + assumption.
      + apply Hbelow. assumption.
  Qed.

  (* Storing the level d of atom a: s->lvl[a] = d. *)
  Lemma rep_store_lvl: forall (m m': mem) (a d: nat),
    RepL m sh N lss x -> (a < N)%nat -> (d <= N)%nat ->
    Mem.store Mint32 m (b_lvl sh) (4 * Z.of_nat a) (vnat d) = Some m' ->
    RepL m' sh N lss (x <| lvl := tset (lvl x) a d |>).
  Proof.
    intros m m' a d HRep Ha Hd Hst.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (r_lvl_le HRep) as Hlvl.
    pose proof (arr_store (a_lvl HRep) Ha Hst) as Alvl.
    destruct HRep. carry Hst Hnd.
    (* Every field but the levels is as before. *)
    constructor; try assumption.
    - (* the levels: atom a now has level d *)
      cbn [set_lvl lvl]. arr_tset.
    - (* the levels are at most N, d too *)
      intros a' Ha'. cbn [set_lvl lvl]. rewrite tget_tset.
      destruct (Nat.eq_dec a a') as [<- | Hne].
      + assumption.
      + apply Hlvl. assumption.
  Qed.

  (* Appending y to the lower literals of the analysis: s->lt[n] = y; s->ltlen = n + 1,
     for n = length (lower x). *)
  Lemma rep_store_lt: forall (m m1 m2: mem) (y: Lit),
    RepL m sh N lss x -> (length (lower x) < N)%nat -> (extract y < N)%nat ->
    Mem.store Mint32 m (b_lt sh) (4 * Z.of_nat (length (lower x))) (vint (key y)) =
      Some m1 ->
    Mem.store Mint32 m1 (b_s sh) o_ltlen (vnat (S (length (lower x)))) = Some m2 ->
    RepL m2 sh N lss (x <| lower := ((lower x) ++ [y]) |>).
  Proof.
    intros m m1 m2 y HRep Hlen Hy Hst1 Hst2.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (r_lt_atoms HRep) as Hatoms.
    pose proof (a_lt HRep) as (tlt & Alt & Htlt).
    pose proof (r_ltlen HRep) as Fltlen.
    pose proof (arr_store Alt Hlen Hst1) as Alt1.
    destruct HRep. carry Hst1 Hnd.
    pose proof (fld_store Fltlen Hst2) as Fltlen2.
    carry Hst2 Hnd. cbn [Val.load_result] in Fltlen2.
    (* Every field but the lower literals is as before. *)
    constructor; try assumption.
    - (* their number *)
      cbn [set_lower lower]. rewrite length_app. cbn [length]. rewrite Nat.add_1_r.
      assumption.
    - (* y is the new last entry *)
      eexists. split.
      + apply Alt1.
      + intros k Hk. cbn [set_lower lower] in Hk |- *.
        rewrite length_app in Hk. cbn [length] in Hk.
        destruct (Nat.eq_dec (length (lower x)) k) as [<- | Hne].
        * rewrite Nat.eqb_refl, nth_middle. reflexivity.
        * replace (Nat.eqb (length (lower x)) k) with false
            by (symmetry; now apply Nat.eqb_neq).
          rewrite app_nth1 by lia. apply Htlt. lia.
    - (* at most N of them *)
      cbn [set_lower lower]. rewrite length_app. cbn [length]. lia.
    - (* with atoms below N, y too *)
      intros y' Hy'. cbn [set_lower lower] in Hy'.
      apply in_app_or in Hy' as [Hy' | [<- | []]].
      + apply Hatoms. assumption.
      + assumption.
  Qed.

  (* Ending the analysis: s->ltlen = 0. *)
  Lemma rep_store_ltlen_zero: forall (m m': mem),
    RepL m sh N lss x -> Mem.store Mint32 m (b_s sh) o_ltlen (vint 0) = Some m' ->
    RepL m' sh N lss (x <| lower := [] |>).
  Proof.
    intros m m' HRep Hst.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (fld_store (r_ltlen HRep) Hst) as Fltlen.
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
      + intros k Hk. cbn [set_lower lower length] in Hk. lia.
    - repack.
    - repack.
    - repack.
    - repack.
    - cbn [set_lower lower length]. lia.
    - intros y [].
  Qed.

  (* Dropping the reason clauses from n on, n <= nr x: s->rtop = s->rbeg[n]; s->nr = n. *)
  Lemma rep_store_pop: forall (m m1 m2: mem) (n: nat),
    RepL m sh N lss x -> (n <= nr x)%nat ->
    Mem.store Mint32 m (b_s sh) o_rtop (vnat (reasons_size (rcl x) n)) = Some m1 ->
    Mem.store Mint32 m1 (b_s sh) o_nr (vnat n) = Some m2 ->
    RepL m2 sh N lss (x <| nr := n |>).
  Proof.
    intros m m1 m2 n HRep Hn Hst1 Hst2.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (r_rsize_le HRep) as Hsize.
    pose proof (r_rcl_atoms HRep) as Hatoms.
    pose proof (r_rps_le HRep) as Hrps.
    pose proof (a_rlits HRep) as (trl & Arl & Htrl).
    pose proof (a_rbeg HRep) as (tb & Arb & Htb).
    pose proof (a_rlen HRep) as (tn & Arn & Htn).
    pose proof (a_rpos HRep) as (tp & Arp & Htp).
    pose proof (r_nr HRep) as Fnr.
    pose proof (fld_store (r_rtop HRep) Hst1) as Frtop.
    destruct HRep. carry Hst1 Hnd.
    pose proof (fld_store Fnr Hst2) as Fnr2.
    carry Hst2 Hnd. cbn [Val.load_result] in Frtop, Fnr2.
    (* Every field is as before, but the reason clauses, which keep their first n. *)
    constructor; try assumption.
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

  (* Pushing reason clause nr x after its literals, start, length and trail position were
     stored in the blocks rlits, rbeg, rlen and rpos, with nothing else changed:
     s->rtop = reasons_size; s->nr = nr x + 1, for x' = add_reason x c. *)
  Lemma rep_store_push: forall (m m1 m2 m3: mem) (c: list Lit) (trl tb tn tp: nat -> Z),
    RepL m sh N lss x -> (nr x < N)%nat ->
    (reasons_size (rcl x) (nr x) + length c <= rcap x)%nat ->
    (forall (y: Lit), In y c -> (extract y < N)%nat) ->
    Mem.unchanged_on (ReasonFrame sh) m m1 ->
    Arr m1 (b_rlits sh) (rcap x) trl -> ReasonsIn trl (rcl (add_reason x c))
      (nr (add_reason x c)) ->
    Arr m1 (b_rbeg sh) N tb ->
    (forall (j: nat), (j <= nr x)%nat -> tb j = Z.of_nat (reasons_size (rcl x) j)) ->
    Arr m1 (b_rlen sh) N tn ->
    (forall (j: nat), (j <= nr x)%nat ->
       tn j = Z.of_nat (length (tget (rcl (add_reason x c)) j))) ->
    Arr m1 (b_rpos sh) N tp ->
    (forall (j: nat), (j <= nr x)%nat ->
       tp j = Z.of_nat (tget (rps (add_reason x c)) j)) ->
    Mem.store Mint32 m1 (b_s sh) o_rtop
      (vnat (reasons_size (rcl x) (nr x) + length c)) = Some m2 ->
    Mem.store Mint32 m2 (b_s sh) o_nr (vnat (S (nr x))) = Some m3 ->
    RepL m3 sh N lss (add_reason x c).
  Proof.
    intros m m1 m2 m3 c trl tb tn tp HRep Hnr Hroom Hc Hun Arl Htrl Arb Htb
      Arn Htn Arp Htp Hst2 Hst3.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (r_tlen_le HRep) as Htlen.
    pose proof (r_rcl_atoms HRep) as Hatoms.
    pose proof (r_rps_le HRep) as Hrps.
    pose proof (r_nr HRep) as Fnr.
    pose proof (r_rtop HRep) as Frtop.
    (* The size of the reason clauses with c. *)
    assert (Hsize: reasons_size (rcl (add_reason x c)) (nr (add_reason x c))
                   = (reasons_size (rcl x) (nr x) + length c)%nat).
    { cbn [add_reason rcl nr reasons_size]. rewrite reasons_size_tset by lia.
      rewrite tget_tset_same. reflexivity. }
    destruct HRep. unpack. transfer Hun Hnd. keep_mem m1.
    pose proof (fld_store Frtop Hst2) as Frtop2.
    carry Hst2 Hnd.
    pose proof (fld_store Fnr Hst3) as Fnr3.
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
      exists trl. split; assumption.
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
End Stores.

(* Keeping all the reason clauses keeps the representation. *)
Lemma rep_nr_same: forall (m: mem) (sh: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (n: nat),
  RepL m sh N lss x -> n = nr x -> RepL m sh N lss (x <| nr := n |>).
Proof. intros m sh N lss x n HRep ->. destruct HRep. constructor; assumption. Qed.
