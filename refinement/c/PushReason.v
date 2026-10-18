(* push_reason stores a literal and the lower literals of the analysis as a new reason
   clause, if there is room (push_reason). *)
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
From RocqSAT.refinement Require Import Tactics.
From RocqSAT.refinement Require Import Table.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement Require Import Analysis.
From RocqSAT.refinement.c Require Import Arrays.
From RocqSAT.refinement.c Require Import Logic.
From RocqSAT.refinement.c Require Import Common.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Rep.
From RocqSAT.refinement.c Require Import RepReasons.

(* Where the literals after the first nr x reason clauses start (the field s->rtop). *)
Abbreviation rtop x := (reasons_size (rcl x) (nr x)).

(* Changing the literals of block rlits from the end of the first n reason clauses on
   keeps them. *)
Lemma reasons_in_ext: forall (t t': nat -> Z) (rc: Table (list Lit)) (n: nat),
  ReasonsIn t rc n -> (forall (k: nat), (k < reasons_size rc n)%nat -> t' k = t k) ->
  ReasonsIn t' rc n.
Proof.
  intros t t' rc n Hin Hext j k Hj Hk.
  assert (Hle: (reasons_size rc (S j) <= reasons_size rc n)%nat).
  { apply reasons_size_le. lia. }
  cbn [reasons_size] in Hle. rewrite Hext by lia. apply Hin; assumption.
Qed.

(* The literals of c after the first n reason clauses make c reason clause n. *)
Lemma reasons_in_add: forall (t: nat -> Z) (rc: Table (list Lit)) (n: nat)
  (c: list Lit), ReasonsIn t rc n ->
  (forall (k: nat), (k < length c)%nat ->
     t (reasons_size rc n + k)%nat = key (nth k c (Pos 0%nat))) ->
  ReasonsIn t (tset rc n c) (S n).
Proof.
  intros t rc n c Hin Hc j k Hj Hk. rewrite reasons_size_tset by lia.
  rewrite tget_tset in Hk |- *. destruct (Nat.eq_dec n j) as [<- | Hne].
  - apply Hc. assumption.
  - apply Hin.
    + lia.
    + assumption.
Qed.

(* What push_reason returns and leaves, from the memory m of the call: the reason r of
   push_reason x u, as enc_reason r, and its context; m' is m on PushFrame. *)
Definition PushPost (m: mem) (sh: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (u: Lit) (m': mem) (v: val): Prop :=
  match push_reason x u with
  | (x', r) =>
    ReasonBelow (length lss) N r /\
    Gives sh N lss (PushFrame sh) x' (vint (enc_reason r)) m m' v
  end.

(* With room, push_reason stores u :: lower x as reason clause nr x. *)
Lemma push_room: forall (x: Ctx) (u: Lit), (nr x < nvars x)%nat ->
  (rtop x + length (u :: lower x) <= rcap x)%nat ->
  push_reason x u = (add_reason x (u :: lower x), learnt (nr x)).
Proof.
  intros x u Hnr Hroom. unfold push_reason.
  replace (nr x <? nvars x)%nat with true by (symmetry; now apply Nat.ltb_lt).
  replace (rtop x + S (length (lower x)) <=? rcap x)%nat with true
    by (symmetry; now apply Nat.leb_le).
  reflexivity.
Qed.

(* The temporaries of push_reason after its loads: s, j = nr x, b = rtop x and
   n = length (lower x). *)
Record PushTemps (sh: Shape) (x: Ctx) (le: temp_env): Prop := {
  pt_s: le ! _s = Some (sptr sh);
  pt_j: le ! _j = Some (vnat (nr x));
  pt_b: le ! _b = Some (vnat (rtop x));
  pt_n: le ! _n = Some (vnat (length (lower x)));
}.

(* The statements of push_reason from the size of the reason clauses on: the two
   fields and the result. *)
Definition push_fields: statement := drop_stmts 11 (fn_body f_push_reason).

(* The end of push_reason, once the four arrays of the reason clauses hold
   add_reason x (u :: lower x) in the memory m1, which is the memory m of the call but
   for them. Writing b for rtop x, n for length (lower x) and j for nr x:

     {{ RepL m x /\ the arrays of add_reason x (u :: lower x) in m1 }}
       s->rtop = b + n + 1;
       s->nr = j + 1;                                                   (rep_store_push)
     {{ RepL (add_reason x (u :: lower x)) }}
       return -(j + 1);
     {{ PushPost: result = enc_reason (learnt j), by push_room }}                    *)
Lemma push_fields_correct: forall (sh: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (u: Lit) (trl tb tn tp: nat -> Z)
  (le: temp_env) (m m1: mem),
  RepL m sh N lss x -> (nr x < N)%nat ->
  (rtop x + length (u :: lower x) <= rcap x)%nat ->
  (forall (y: Lit), In y (u :: lower x) -> (extract y < N)%nat) ->
  Mem.unchanged_on (ReasonFrame sh) m m1 ->
  Arr m1 (b_rlits sh) (rcap x) trl ->
  ReasonsIn trl (rcl (add_reason x (u :: lower x))) (nr (add_reason x (u :: lower x))) ->
  Arr m1 (b_rbeg sh) N tb ->
  (forall (j: nat), (j <= nr x)%nat -> tb j = Z.of_nat (reasons_size (rcl x) j)) ->
  Arr m1 (b_rlen sh) N tn ->
  (forall (j: nat), (j <= nr x)%nat ->
     tn j = Z.of_nat (length (tget (rcl (add_reason x (u :: lower x))) j))) ->
  Arr m1 (b_rpos sh) N tp ->
  (forall (j: nat), (j <= nr x)%nat ->
     tp j = Z.of_nat (tget (rps (add_reason x (u :: lower x))) j)) ->
  PushTemps sh x le ->
  Exec ge le m1 push_fields (Returns f_push_reason (PushPost m sh N lss x u)).
Proof.
  intros sh N lss x u trl tb tn tp le m m1 HRep Hnr Hroom Hc Hun Arl Htrl Arb Htb
    Arn Htn Arp Htp [Hs Hj Hb Hn].
  pose proof (r_n HRep) as HN.
  pose proof (r_nodup HRep) as Hnd.
  pose proof (r_rcap_small HRep) as Hrcap.
  pose proof (r_rtop HRep) as Frtop.
  pose proof (r_nr HRep) as Fnr.
  transfer Hun Hnd.
  assert (Hpush: push_reason x u = (add_reason x (u :: lower x), learnt (nr x))).
  { apply push_room.
    - rewrite (r_nvars HRep). assumption.
    - assumption. }
  (* The sums C computes, and its result. *)
  assert (Hsize: Int.add (Int.add (Int.repr (Z.of_nat (rtop x)))
                                  (Int.repr (Z.of_nat (length (lower x))))) (Int.repr 1)
                 = Int.repr (Z.of_nat (rtop x + length (u :: lower x)))).
  { rewrite !add_repr. f_equal. cbn [length]. lia. }
  assert (Hj1: Int.add (Int.repr (Z.of_nat (nr x))) (Int.repr 1)
               = Int.repr (Z.of_nat (S (nr x)))).
  { rewrite add_repr. f_equal. lia. }
  assert (Hneg: Int.neg (Int.repr (Z.of_nat (S (nr x))))
                = Int.repr (enc_reason (learnt (nr x)))).
  { rewrite Int.neg_repr. f_equal. cbn [enc_reason]. lia. }
  unfold push_fields, f_push_reason. cbn [fn_body drop_stmts].
  (* s->rtop = b + n + 1; *)
  run. store Frtop as m2 Hst2.
  cbn [cast_int_int] in Hst2. rewrite Hsize in Hst2. normal.
  assert (Fnr2: IntAt m2 sh o_nr (nr x)).
  { apply (fld_store_other Fnr Hst2). right.
    unfold Mptr. cbv [Archi.ptr64]. cbn [size_chunk]. lia. }
  (* s->nr = j + 1; *)
  run. store Fnr2 as m3 Hst3.
  cbn [cast_int_int] in Hst3. rewrite Hj1 in Hst3. normal.
  (* return -(j + 1); *)
  eapply exec_return.
  - ev.
  - cbn [cast_int_int]. ints.
    exists (vint (enc_reason (learnt (nr x)))). split.
    + apply result_int.
    + unfold PushPost. rewrite Hpush. splits.
      * cbn [ReasonBelow]. assumption.
      * reflexivity.
      * apply (rep_store_push m m1 m2 m3 (u :: lower x) trl tb tn tp
                 HRep Hnr Hroom Hc Hun Arl Htrl Arb Htb Arn Htn Arp Htp Hst2 Hst3).
      * (* only the reason clauses and the struct changed *)
        frame.
Qed.

(* The statements of push_reason after the loop: the start, length and trail position of
   the new clause, then the fields. *)
Definition push_end: statement := drop_stmts 8 (fn_body f_push_reason).

(* The end of push_reason, once the literals t of block rlits hold u :: lower x as
   reason clause nr x after the others, in the memory m1, which is the memory m of the
   call but for rlits. Writing b for rtop x, n for length (lower x) and j for nr x:

     {{ RepL m x /\ Arr m1 rlits t /\ m1 is m but for rlits /\ j < N /\
        b + n + 1 <= rcap x }}
       s->rbeg[j] = b;
       s->rlen[j] = n + 1;
       s->rpos[j] = s->tlen;
     {{ the arrays of add_reason x (u :: lower x), and only the reason clauses changed }}
       the fields, and the result;                                (push_fields_correct)
     {{ PushPost }}                                                                   *)
Lemma push_end_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (u: Lit) (t: nat -> Z) (le: temp_env) (m m1: mem),
  RepL m sh N lss x -> (extract u < N)%nat -> (nr x < N)%nat ->
  (rtop x + length (u :: lower x) <= rcap x)%nat ->
  Mem.unchanged_on (AllBut (b_rlits sh)) m m1 ->
  Arr m1 (b_rlits sh) (rcap x) t ->
  ReasonsIn t (rcl (add_reason x (u :: lower x))) (nr (add_reason x (u :: lower x))) ->
  PushTemps sh x le ->
  Exec ge le m1 push_end (Returns f_push_reason (PushPost m sh N lss x u)).
Proof.
  intros sh N lss x u t le m m1 HRep Hu Hnr Hroom Hun Arl Htrl [Hs Hj Hb Hn].
  pose proof (r_n HRep) as HN.
  pose proof (r_nodup HRep) as Hnd.
  pose proof (r_rcap_small HRep) as Hrcap.
  pose proof (r_tlen_le HRep) as Htlen.
  pose proof (r_lt_atoms HRep) as Hatoms.
  pose proof (r_rbeg HRep) as Frbeg.
  pose proof (r_rlen HRep) as Frlen.
  pose proof (r_rpos HRep) as Frpos.
  pose proof (r_tlen HRep) as Ftlen.
  pose proof (a_rbeg HRep) as (tb & Arb & Htb).
  pose proof (a_rlen HRep) as (tn & Arn & Htn).
  pose proof (a_rpos HRep) as (tp & Arp & Htp).
  transfer Hun Hnd.
  assert (Hn1: Int.add (Int.repr (Z.of_nat (length (lower x)))) (Int.repr 1)
               = Int.repr (Z.of_nat (length (u :: lower x)))).
  { rewrite add_repr. f_equal. cbn [length]. lia. }
  unfold push_end, f_push_reason. cbn [fn_body drop_stmts].
  (* s->rbeg[j] = b; *)
  run. store Arb Hnr as m2 Hst2.
  pose proof (arr_store Arb Hnr Hst2) as Arb2.
  clear Arb. carry Hst2 Hnd.
  (* s->rlen[j] = n + 1; *)
  run. store Arn Hnr as m3 Hst3.
  cbn [cast_int_int] in Hst3. rewrite Hn1 in Hst3. normal.
  pose proof (arr_store Arn Hnr Hst3) as Arn3.
  clear Arn. carry Hst3 Hnd.
  (* s->rpos[j] = s->tlen; *)
  run. store Arp Hnr as m4 Hst4.
  pose proof (arr_store Arp Hnr Hst4) as Arp4.
  clear Arp. carry Hst4 Hnd.
  (* Only the four blocks of the reason clauses changed since the call. *)
  assert (Hun4: Mem.unchanged_on (ReasonFrame sh) m m4).
  { apply (store_unchanged _ m m3 m4 Mint32 (b_rpos sh)
             (4 * Z.of_nat (nr x)) (vnat (tlen x))).
    - frame.
    - assumption.
    - intros i (_ & _ & _ & Hi). now apply Hi. }
  (* the fields, and the result *)
  eapply (push_fields_correct sh N lss x u t _ _ _ _ m m4).
  - assumption.
  - assumption.
  - assumption.
  - (* the atoms of u :: lower x are below N *)
    intros y [<- | Hy].
    + assumption.
    + apply Hatoms. assumption.
  - assumption.
  - assumption.
  - assumption.
  - apply Arb2.
  - (* the starts: b for clause j *)
    intros j Hj'. cbv beta.
    destruct (Nat.eqb_spec (nr x) j) as [<- | Hne].
    + reflexivity.
    + apply Htb. lia.
  - apply Arn3.
  - (* the lengths: that of u :: lower x for clause j *)
    intros j Hj'. cbv beta. cbn [add_reason rcl].
    destruct (Nat.eqb_spec (nr x) j) as [<- | Hne].
    + rewrite tget_tset_same. reflexivity.
    + rewrite tget_tset_other by assumption. apply Htn. lia.
  - apply Arp4.
  - (* the trail positions: the end of the trail for clause j *)
    intros j Hj'. cbv beta. cbn [add_reason rps].
    destruct (Nat.eqb_spec (nr x) j) as [<- | Hne].
    + rewrite tget_tset_same. reflexivity.
    + rewrite tget_tset_other by assumption. apply Htp. lia.
  - constructor; tmp.
Qed.

(* The keys t of block rlits hold the reason clauses of x, then u at rtop x and the
   first q lower literals after it. *)
Record PushedLits (x: Ctx) (u: Lit) (q: nat) (t: nat -> Z): Prop := {
  pl_old: ReasonsIn t (rcl x) (nr x);
  pl_u: t (rtop x) = key u;
  pl_lower: forall (k: nat), (k < q)%nat ->
    t (rtop x + 1 + k)%nat = key (nth k (lower x) (Pos 0%nat));
}.

(* The invariant of the loop of push_reason at q: rlits holds the first q lower literals,
   and m1 is m but for rlits. *)
Record PushInv {m: mem} {sh: Shape} {x: Ctx} {u: Lit} {q: nat} {le: temp_env} {m1: mem}:
  Prop := {
  pu_temps: PushTemps sh x le;
  pu_q: le ! _q = Some (vnat q);
  pu_le: (q <= length (lower x))%nat;
  pu_rlits: exists (t: nat -> Z), Arr m1 (b_rlits sh) (rcap x) t /\ PushedLits x u q t;
  pu_frame: Mem.unchanged_on (AllBut (b_rlits sh)) m m1;
}.
Arguments PushInv : clear implicits.

(* Storing the lower literal at q at rtop x + 1 + q gives the invariant at q + 1. *)
Lemma push_inv_next: forall (m m1: mem) (sh: Shape) (x: Ctx) (u: Lit) (q: nat)
  (le: temp_env) (t: nat -> Z),
  (q < length (lower x))%nat -> PushedLits x u q t ->
  Arr m1 (b_rlits sh) (rcap x) (fun (i: nat) =>
    if Nat.eqb (rtop x + 1 + q) i then key (nth q (lower x) (Pos 0%nat)) else t i) ->
  Mem.unchanged_on (AllBut (b_rlits sh)) m m1 ->
  PushTemps sh x le -> le ! _q = Some (vnat (S q)) ->
  PushInv m sh x u (S q) le m1.
Proof.
  intros m m1 sh x u q le t Hq [Hold Hu Hlits] Arl Hun HT Hq'.
  constructor.
  - assumption.
  - assumption.
  - lia.
  - eexists. split.
    + apply Arl.
    + constructor.
      * (* the reason clauses are before rtop x *)
        apply (reasons_in_ext t).
        -- assumption.
        -- intros k Hk.
           replace (Nat.eqb (rtop x + 1 + q) k) with false
             by (symmetry; apply Nat.eqb_neq; lia).
           reflexivity.
      * (* u is at rtop x *)
        replace (Nat.eqb (rtop x + 1 + q) (rtop x)) with false
          by (symmetry; apply Nat.eqb_neq; lia).
        assumption.
      * (* the first q + 1 lower literals after it *)
        intros k Hk.
        destruct (Nat.eqb_spec (rtop x + 1 + q) (rtop x + 1 + k)) as [Heq | Hne].
        -- replace k with q by lia. reflexivity.
        -- apply Hlits. lia.
  - assumption.
Qed.

(* The statements of push_reason after its tests: the literals and the end. *)
Definition push_stores: statement := drop_stmts 5 (fn_body f_push_reason).

(* The stores of push_reason, when there is room. Writing b for rtop x, n for
   length (lower x) and j for nr x:

     {{ RepL m x /\ j < N /\ b + n + 1 <= rcap x }}
       s->rlits[b] = u;
       int q = 0;
     {{ PushInv 0 }}
       while (q < n) {
     {{ PushInv q /\ q < n }}
         s->rlits[b + 1 + q] = s->lt[q];
         q++;
     {{ PushInv (q + 1) }}                                               (push_inv_next)
       }
     {{ PushInv n: rlits holds u :: lower x as clause j }}              (reasons_in_add)
       the end;                                                    (push_end_correct)
     {{ PushPost }}

   The loop ends: n - q decreases. *)
Lemma push_stores_correct: forall (sh: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (u: Lit) (le: temp_env) (m: mem),
  RepL m sh N lss x -> (extract u < N)%nat -> (nr x < N)%nat ->
  (rtop x + length (u :: lower x) <= rcap x)%nat ->
  PushTemps sh x le -> le ! _u = Some (vint (key u)) ->
  Exec ge le m push_stores (Returns f_push_reason (PushPost m sh N lss x u)).
Proof.
  intros sh N lss x u le m HRep Hu Hnr Hroom [Hs Hj Hb Hn] Hu'.
  pose proof (r_n HRep) as HN.
  pose proof (r_nodup HRep) as Hnd.
  pose proof (r_rcap_small HRep) as Hrcap.
  pose proof (r_lt_le HRep) as Hltle.
  pose proof (r_rlits HRep) as Frl.
  pose proof (a_rlits HRep) as (trl & Arl & Htrl).
  assert (Hbr: (rtop x < rcap x)%nat) by (cbn [length] in Hroom; lia).
  unfold push_stores, f_push_reason. cbn [fn_body drop_stmts].
  (* s->rlits[b] = u; *)
  run. store Arl Hbr as m1 Hst1.
  pose proof (arr_store Arl Hbr Hst1) as Arl1. clear Arl.
  (* int q = 0; *)
  run. unfold Swhile.
  apply exec_loop with (R := ltof nat (fun (q: nat) => length (lower x) - q)%nat)
    (I := PushInv m sh x u) (a := 0%nat).
  - apply well_founded_ltof.
  - intros q le1 m2 HI.
    destruct HI as [HT Hq Hqle (t & Arl2 & HP) Hun].
    pose proof HT as [Hs1 Hj1 Hb1 Hn1]. pose proof HP as [Hold Hfirst Hlits].
    clear Arl1.
    apply exec_seq.
    (* if (q < n) ... else break; *)
    branch.
    + (* q < n: s->rlits[b + 1 + q] = s->lt[q]; q++; *)
      intros Hlt. assert (Hq_lt: (q < length (lower x))%nat) by lia.
      pose proof (r_lt HRep) as Flt.
      pose proof (a_lt HRep) as (tlt & Alt & Htlt).
      transfer Hun Hnd.
      assert (Hidx: Int.add (Int.add (Int.repr (Z.of_nat (rtop x))) (Int.repr 1))
                      (Int.repr (Z.of_nat q))
                    = Int.repr (Z.of_nat (rtop x + 1 + q))).
      { rewrite !add_repr. f_equal. lia. }
      assert (Hadd: Int.add (Int.repr (Z.of_nat q)) (Int.repr 1)
                    = Int.repr (Z.of_nat (S q))).
      { rewrite add_repr. f_equal. lia. }
      assert (Hk: (rtop x + 1 + q < rcap x)%nat)
        by (cbn [length] in Hroom; lia).
      apply exec_skip. normal. run.
      rewrite (Htlt q) by assumption.
      store Arl2 Hk as m3 Hst3.
      run. ints.
      apply loopk_next with (S q).
      * unfold ltof. lia.
      * apply (push_inv_next m m3 sh x u q _ t).
        -- assumption.
        -- assumption.
        -- apply (arr_store Arl2 Hk Hst3).
        -- frame.
        -- constructor; tmp.
        -- tmp.
    + (* q = n: break; and the end, with u :: lower x as clause j *)
      intros Hge.
      apply exec_break. abrupt. apply loopk_break. normal.
      apply (push_end_correct sh N lss x u t _ m m2).
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * cbn [add_reason rcl nr]. apply reasons_in_add.
        -- assumption.
        -- intros k Hk. destruct k as [|k].
           ++ rewrite Nat.add_0_r. assumption.
           ++ cbn [nth]. cbn [length] in Hk.
              replace (rtop x + S k)%nat
                with (rtop x + 1 + k)%nat by lia.
              apply Hlits. lia.
      * constructor; tmp.
  - (* The invariant holds at q = 0, with u at b. *)
    constructor.
    + constructor; tmp.
    + tmp.
    + lia.
    + eexists. split.
      * apply Arl1.
      * constructor.
        -- apply (reasons_in_ext trl).
           ++ assumption.
           ++ intros k Hk.
              replace (Nat.eqb (rtop x) k) with false
                by (symmetry; apply Nat.eqb_neq; lia).
              reflexivity.
        -- rewrite Nat.eqb_refl. reflexivity.
        -- intros k Hk. lia.
    + frame.
Qed.

(* Without room, push_reason keeps x and gives no reason, which C returns as 0. *)
Lemma push_none: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (u: Lit) (m: mem),
  RepL m sh N lss x -> push_reason x u = (x, no_reason) ->
  PushPost m sh N lss x u m (vint 0).
Proof.
  intros sh N lss x u m HRep Hpush. unfold PushPost. rewrite Hpush. splits.
  - cbn [ReasonBelow]. apply I.
  - reflexivity.
  - assumption.
  - frame.
Qed.

(* push_reason stores u :: lower x as a new reason clause, for the literal at the end of
   the trail, if there is room for one more clause (at most N) and its literals (at most
   rcap x), and gives that clause as the reason, or no reason:

     {{ RepL m sh N lss x /\ extract u < N }}
       int j = s->nr;
       int b = s->rtop;
       int n = s->ltlen;
       if (j >= s->nv) return 0;
       if (n >= s->rcap - b) return 0;
     {{ result = 0 = enc_reason no_reason, and push_reason x u = (x, no_reason)
     }}
     {{ RepL x /\ j = nr x < N /\ b + n + 1 <= rcap x }}
       the stores, and return -(j + 1);                           (push_stores_correct)
     {{ PushPost: push_reason x u = (add_reason x (u :: lower x), learnt j) }}
                                                                                       *)
Lemma push_reason_correct: forall (sh: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (u: Lit),
  {{ m | RepL m sh N lss x /\ (extract u < N)%nat }}
    f_push_reason(sptr sh, vint (key u))
  {{ m', v | PushPost m sh N lss x u m' v }}.
Proof.
  intros sh N lss x u m [HRep Hu].
  pose proof (r_n HRep) as HN.
  pose proof (r_nvars HRep) as Hnv.
  pose proof (r_nr_le HRep) as Hnrle.
  pose proof (r_rsize_le HRep) as Hsize.
  pose proof (r_rcap_small HRep) as Hrcap.
  pose proof (r_lt_le HRep) as Hltle.
  pose proof (r_nv HRep) as Fnv.
  pose proof (r_nr HRep) as Fnr.
  pose proof (r_rtop HRep) as Frtop.
  pose proof (r_ltlen HRep) as Fltlen.
  pose proof (r_rcap HRep) as Frcap.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_push_reason. cbn [fn_body fn_return].
    (* int j = s->nr; int b = s->rtop; int n = s->ltlen; *)
    run.
    (* if (j >= s->nv) return 0; *)
    branch.
    + (* no room for one more clause: return 0; *)
      intros Hfull. return_int.
      apply (push_none sh N lss x u m HRep).
      unfold push_reason. rewrite Hnv.
      replace (nr x <? N)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
      reflexivity.
    + (* room for one more clause *)
      intros Hnr_z. assert (Hnr: (nr x < N)%nat) by lia.
      apply exec_skip. normal.
      (* if (n >= s->rcap - b) return 0; *)
      run.
      eapply (exec_if_ge (Z.of_nat (length (lower x)))
                (Z.of_nat (rcap x) - Z.of_nat (rtop x))).
      * ev.
      * eapply eval_Ebinop.
        -- ev.
        -- ev.
        -- cbn -[Int.sub Int.repr]. unfold vint. rewrite <- sub_repr. reflexivity.
      * reflexivity.
      * lia.
      * (* no room for its literals: return 0; *)
        intros Hover_z.
        assert (Hover: (rcap x < rtop x + length (u :: lower x))%nat)
          by (cbn [length]; lia).
        return_int.
        apply (push_none sh N lss x u m HRep).
        unfold push_reason.
        replace (rtop x + S (length (lower x)) <=? rcap x)%nat
          with false by (symmetry; apply Nat.leb_gt; assumption).
        rewrite andb_false_r. reflexivity.
      * (* room for its literals: the stores *)
        intros Hroom_z.
        assert (Hroom: (rtop x + length (u :: lower x) <= rcap x)%nat)
          by (cbn [length]; lia).
        apply exec_skip. normal.
        apply (push_stores_correct sh N lss x u).
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- constructor; tmp.
        -- tmp.
Qed.

Lemma push_reason_fun: FunAt _push_reason f_push_reason.
Proof. apply find_fun. reflexivity. Qed.
