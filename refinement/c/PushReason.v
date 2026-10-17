(* push_reason stores a literal and the lower literals of the analysis as a new reason
   clause, if there is room (push_reason). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Propagate Analysis.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep RepReasons.
Import ListNotations.

(* Changing the literals of block rlits from the end of the first n reason clauses on
   keeps them. *)
Lemma reasons_in_ext: forall (t t': nat -> Z) (rc: Table (list Lit)) (n: nat),
  ReasonsIn t rc n -> (forall (k: nat), (k < reasons_size rc n)%nat -> t' k = t k) ->
  ReasonsIn t' rc n.
Proof.
  intros t t' rc n Hin Hext j k Hj Hk.
  assert (Hle: (reasons_size rc (Datatypes.S j) <= reasons_size rc n)%nat).
  { apply reasons_size_le. lia. }
  cbn [reasons_size] in Hle. rewrite Hext by lia. apply Hin.
  - assumption.
  - assumption.
Qed.

(* The literals of c after the first n reason clauses make c reason clause n. *)
Lemma reasons_in_add: forall (t: nat -> Z) (rc: Table (list Lit)) (n: nat)
  (c: list Lit), ReasonsIn t rc n ->
  (forall (k: nat), (k < length c)%nat ->
     t (reasons_size rc n + k)%nat = key (nth k c (Pos 0%nat))) ->
  ReasonsIn t (tset rc n c) (Datatypes.S n).
Proof.
  intros t rc n c Hin Hc j k Hj Hk. rewrite reasons_size_tset by lia.
  rewrite tget_tset in Hk |- *. destruct (Nat.eq_dec n j) as [<- | Hne].
  - apply Hc. assumption.
  - apply Hin.
    + lia.
    + assumption.
Qed.

(* What push_reason gives when there is room: the memory holds x with u :: lt as reason
   clause nr x, the result is that clause as a reason, and only the blocks of the reason
   clauses and the struct changed from the memory m of the call. *)
Definition PushPost (m: mem) (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (lt: list Lit) (u: Lit) (m': mem) (v: val): Prop :=
  RepL m' S N lss (add_reason x (u :: lt)) lims lt /\
  v = vint (enc_reason (learnt (nr x))) /\
  ReasonBelow (length lss) N (learnt (nr x)) /\
  Mem.unchanged_on (fun (b: block) (_: Z) =>
    b <> b_rlits S /\ b <> b_rbeg S /\ b <> b_rlen S /\ b <> b_rpos S /\
    b <> b_s S) m m'.


(* The statements of push_reason from the size of the reason clauses on: the two
   fields and the result. *)
Definition push_fields: statement := drop_stmts 11 (fn_body f_push_reason).

(* The end of push_reason, once the four arrays of the reason clauses hold
   add_reason x (u :: lt) in the memory m1, which is the memory m of the call but for
   them. Writing b for reasons_size (rcl x) (nr x), n for length lt and j for nr x:

     {{ RepL m x lt /\ the arrays of add_reason x (u :: lt) in m1 }}
       s->rtop = b + n + 1;
       s->nr = j + 1;                                                   (rep_store_push)
     {{ RepL (add_reason x (u :: lt)) lt }}
       return -(j + 1);
     {{ PushPost: result = enc_reason (learnt j) }}                                   *)
Lemma push_fields_correct {lt: list Lit}: forall (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (u: Lit) (trl tb tn tp: nat -> Z)
  (le: temp_env) (m m1: mem),
  RepL m S N lss x lims lt -> (nr x < N)%nat ->
  (reasons_size (rcl x) (nr x) + length (u :: lt) <= rcap x)%nat ->
  (forall (y: Lit), In y (u :: lt) -> (extract y < N)%nat) ->
  Mem.unchanged_on (fun (b: block) (_: Z) =>
    b <> b_rlits S /\ b <> b_rbeg S /\ b <> b_rlen S /\ b <> b_rpos S) m m1 ->
  Arr m1 (b_rlits S) (rcap x) trl ->
  ReasonsIn trl (rcl (add_reason x (u :: lt))) (nr (add_reason x (u :: lt))) ->
  Arr m1 (b_rbeg S) N tb ->
  (forall (j: nat), (j <= nr x)%nat -> tb j = Z.of_nat (reasons_size (rcl x) j)) ->
  Arr m1 (b_rlen S) N tn ->
  (forall (j: nat), (j <= nr x)%nat ->
     tn j = Z.of_nat (length (tget (rcl (add_reason x (u :: lt))) j))) ->
  Arr m1 (b_rpos S) N tp ->
  (forall (j: nat), (j <= nr x)%nat ->
     tp j = Z.of_nat (tget (rps (add_reason x (u :: lt))) j)) ->
  le ! _s = Some (sptr S) -> le ! _j = Some (vint (Z.of_nat (nr x))) ->
  le ! _b = Some (vint (Z.of_nat (reasons_size (rcl x) (nr x)))) ->
  le ! _n = Some (vint (Z.of_nat (length lt))) ->
  Exec ge le m1 push_fields (Returns f_push_reason (PushPost m S N lss x lims lt u)).
Proof.
  intros S N lss x lims u trl tb tn tp le m m1 HRep Hnr Hroom Hc Hun Arl Htrl Arb Htb
    Arn Htn Arp Htp Hs Hj Hb Hn.
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_rcap_small _ _ _ _ _ _ _ HRep) as Hrcap.
  pose proof (r_rtop _ _ _ _ _ _ _ HRep) as Frtop.
  pose proof (r_nr _ _ _ _ _ _ _ HRep) as Fnr.
  transfer Hun Hnd.
  (* The sums C computes, and its result. *)
  assert (Hsize: Int.add (Int.add (Int.repr (Z.of_nat (reasons_size (rcl x) (nr x))))
                                  (Int.repr (Z.of_nat (length lt)))) (Int.repr 1)
                 = Int.repr (Z.of_nat (reasons_size (rcl x) (nr x) + length (u :: lt)))).
  { rewrite !add_repr. f_equal. cbn [length]. lia. }
  assert (Hj1: Int.add (Int.repr (Z.of_nat (nr x))) (Int.repr 1)
               = Int.repr (Z.of_nat (Datatypes.S (nr x)))).
  { rewrite add_repr. f_equal. lia. }
  assert (Hneg: Int.neg (Int.repr (Z.of_nat (Datatypes.S (nr x))))
                = Int.repr (enc_reason (learnt (nr x)))).
  { rewrite Int.neg_repr. f_equal. cbn [enc_reason]. lia. }
  unfold push_fields, f_push_reason. cbn [fn_body drop_stmts].
  (* s->rtop = b + n + 1; *)
  run. eapply exec_store.
  - evl.
  - ev.
  - reflexivity.
  - reflexivity.
  - fofs. bound.
  - fofs. cbn [cast_int_int]. ints.
    destruct (fld_storable m1 (b_s S) 204 Mint32 _
                (vint (Z.of_nat (reasons_size (rcl x) (nr x) + length (u :: lt)))) Frtop)
      as [m2 Hst2].
    exists m2. split.
    + apply Hst2.
    + normal.
      assert (Fnr2: Fld m2 (b_s S) 232 Mint32 (vint (Z.of_nat (nr x)))).
      { apply (fld_store_other _ _ _ _ _ _ _ _ _ _ Fnr Hst2). right.
        unfold Mptr. cbv [Archi.ptr64]. cbn [size_chunk]. lia. }
      (* s->nr = j + 1; *)
      run. eapply exec_store.
      * evl.
      * ev.
      * reflexivity.
      * reflexivity.
      * fofs. bound.
      * fofs. cbn [cast_int_int]. ints.
        destruct (fld_storable m2 (b_s S) 232 Mint32 _
                    (vint (Z.of_nat (Datatypes.S (nr x)))) Fnr2) as [m3 Hst3].
        exists m3. split.
        -- apply Hst3.
        -- normal.
           (* return -(j + 1); *)
           eapply exec_return.
           ++ ev.
           ++ cbn [cast_int_int]. ints.
              exists (vint (enc_reason (learnt (nr x)))). split.
              ** apply result_int.
              ** unfold PushPost. split.
                 --- apply (rep_store_push m m1 m2 m3 S N lss x lims (u :: lt) trl tb tn
                              tp HRep Hnr Hroom Hc Hun Arl Htrl Arb Htb Arn Htn Arp Htp
                              Hst2 Hst3).
                 --- split.
                     +++ reflexivity.
                     +++ split.
                         *** cbn [ReasonBelow]. assumption.
                         *** (* only the reason clauses and the struct changed *)
                             apply (store_unchanged _ m m2 m3 Mint32 (b_s S) 232
                                      (vint (Z.of_nat (Datatypes.S (nr x))))).
                             ---- apply (store_unchanged _ m m1 m2 Mint32 (b_s S) 204
                                           (vint (Z.of_nat (reasons_size (rcl x) (nr x)
                                                            + length (u :: lt))))).
                                  ++++ apply (Mem.unchanged_on_implies _ _ m m1 Hun).
                                       intros b' ofs' Hb' _. repeat split; apply Hb'.
                                  ++++ assumption.
                                  ++++ intros i (_ & _ & _ & _ & Hi). now apply Hi.
                             ---- assumption.
                             ---- intros i (_ & _ & _ & _ & Hi). now apply Hi.
Qed.

(* The statements of push_reason after the loop: the start, length and trail position of
   the new clause, then the fields. *)
Definition push_end: statement := drop_stmts 8 (fn_body f_push_reason).

(* The end of push_reason, once the literals t of block rlits hold u :: lt as reason
   clause nr x after the others, in the memory m1, which is the memory m of the call but
   for rlits. Writing b for reasons_size (rcl x) (nr x), n for length lt and j for nr x:

     {{ RepL m x lt /\ Arr m1 rlits t /\ m1 is m but for rlits /\ j < N /\
        b + n + 1 <= rcap x }}
       s->rbeg[j] = b;
       s->rlen[j] = n + 1;
       s->rpos[j] = s->tlen;
     {{ the arrays of add_reason x (u :: lt), and only the reason clauses changed }}
       the fields, and the result;                                (push_fields_correct)
     {{ PushPost }}                                                                   *)
Lemma push_end_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (u: Lit) (t: nat -> Z) (le: temp_env) (m m1: mem),
  RepL m S N lss x lims lt -> (extract u < N)%nat -> (nr x < N)%nat ->
  (reasons_size (rcl x) (nr x) + length (u :: lt) <= rcap x)%nat ->
  Mem.unchanged_on (fun (b: block) (_: Z) => b <> b_rlits S) m m1 ->
  Arr m1 (b_rlits S) (rcap x) t ->
  ReasonsIn t (rcl (add_reason x (u :: lt))) (nr (add_reason x (u :: lt))) ->
  le ! _s = Some (sptr S) -> le ! _j = Some (vint (Z.of_nat (nr x))) ->
  le ! _b = Some (vint (Z.of_nat (reasons_size (rcl x) (nr x)))) ->
  le ! _n = Some (vint (Z.of_nat (length lt))) ->
  Exec ge le m1 push_end (Returns f_push_reason (PushPost m S N lss x lims lt u)).
Proof.
  intros S N lss x lims u t le m m1 HRep Hu Hnr Hroom Hun Arl Htrl Hs Hj Hb Hn.
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_rcap_small _ _ _ _ _ _ _ HRep) as Hrcap.
  pose proof (r_tlen_le _ _ _ _ _ _ _ HRep) as Htlen.
  pose proof (r_lt_atoms _ _ _ _ _ _ _ HRep) as Hatoms.
  pose proof (r_rbeg _ _ _ _ _ _ _ HRep) as Frbeg.
  pose proof (r_rlen _ _ _ _ _ _ _ HRep) as Frlen.
  pose proof (r_rpos _ _ _ _ _ _ _ HRep) as Frpos.
  pose proof (r_tlen _ _ _ _ _ _ _ HRep) as Ftlen.
  pose proof (a_rbeg _ _ _ _ _ _ _ HRep) as (tb & Arb & Htb).
  pose proof (a_rlen _ _ _ _ _ _ _ HRep) as (tn & Arn & Htn).
  pose proof (a_rpos _ _ _ _ _ _ _ HRep) as (tp & Arp & Htp).
  transfer Hun Hnd.
  assert (Hn1: Int.add (Int.repr (Z.of_nat (length lt))) (Int.repr 1)
               = Int.repr (Z.of_nat (length (u :: lt)))).
  { rewrite add_repr. f_equal. cbn [length]. lia. }
  unfold push_end, f_push_reason. cbn [fn_body drop_stmts].
  (* s->rbeg[j] = b; *)
  run. eapply exec_store.
  - evl.
  - ev.
  - reflexivity.
  - reflexivity.
  - ofs. bound.
  - ofs. cbn [cast_int_int].
    destruct (arr_storable m1 (b_rbeg S) N (nr x) tb
                (Z.of_nat (reasons_size (rcl x) (nr x))) Arb Hnr) as [m2 Hst2].
    exists m2. split.
    + apply Hst2.
    + normal. pose proof (arr_store _ _ _ _ _ _ _ Arb Hnr Hst2) as Arb2.
      clear Arb. carry Hst2 Hnd.
      (* s->rlen[j] = n + 1; *)
      run. eapply exec_store.
      * evl.
      * ev.
      * reflexivity.
      * reflexivity.
      * ofs. bound.
      * ofs. cbn [cast_int_int].
        destruct (arr_storable m2 (b_rlen S) N (nr x) tn
                    (Z.of_nat (length (u :: lt))) Arn Hnr) as [m3 Hst3].
        exists m3. split.
        -- apply Hst3.
        -- normal. pose proof (arr_store _ _ _ _ _ _ _ Arn Hnr Hst3) as Arn3.
           clear Arn. carry Hst3 Hnd.
           (* s->rpos[j] = s->tlen; *)
           run. eapply exec_store.
           ++ evl.
           ++ ev.
           ++ reflexivity.
           ++ reflexivity.
           ++ ofs. bound.
           ++ ofs. cbn [cast_int_int].
              destruct (arr_storable m3 (b_rpos S) N (nr x) tp (Z.of_nat (tlen x)) Arp
                          Hnr) as [m4 Hst4].
              exists m4. split.
              ** apply Hst4.
              ** normal. pose proof (arr_store _ _ _ _ _ _ _ Arp Hnr Hst4) as Arp4.
                 clear Arp. carry Hst4 Hnd.
                 (* Only the four blocks of the reason clauses changed since the call. *)
                 assert (Hun4: Mem.unchanged_on (fun (b: block) (_: Z) =>
                                 b <> b_rlits S /\ b <> b_rbeg S /\ b <> b_rlen S /\
                                 b <> b_rpos S) m m4).
                 { apply (store_unchanged _ m m3 m4 Mint32 (b_rpos S)
                            (4 * Z.of_nat (nr x)) (vint (Z.of_nat (tlen x)))).
                   - apply (store_unchanged _ m m2 m3 Mint32 (b_rlen S)
                              (4 * Z.of_nat (nr x))
                              (vint (Z.of_nat (length (u :: lt))))).
                     + apply (store_unchanged _ m m1 m2 Mint32 (b_rbeg S)
                                (4 * Z.of_nat (nr x))
                                (vint (Z.of_nat (reasons_size (rcl x) (nr x))))).
                       * apply (Mem.unchanged_on_implies _ _ m m1 Hun).
                         intros b' ofs' (Hb' & _) _. assumption.
                       * assumption.
                       * intros i (_ & Hi & _). now apply Hi.
                     + assumption.
                     + intros i (_ & _ & Hi & _). now apply Hi.
                   - assumption.
                   - intros i (_ & _ & _ & Hi). now apply Hi. }
                 (* the fields, and the result *)
                 eapply (push_fields_correct S N lss x lims u t _ _ _ _ m m4).
                 --- assumption.
                 --- assumption.
                 --- assumption.
                 --- (* the atoms of u :: lt are below N *)
                     intros y [<- | Hy].
                     +++ assumption.
                     +++ apply Hatoms. assumption.
                 --- assumption.
                 --- assumption.
                 --- assumption.
                 --- apply Arb2.
                 --- (* the starts: b for clause j *)
                     intros j Hj'. cbv beta.
                     destruct (Nat.eqb_spec (nr x) j) as [<- | Hne].
                     +++ reflexivity.
                     +++ apply Htb. lia.
                 --- apply Arn3.
                 --- (* the lengths: that of u :: lt for clause j *)
                     intros j Hj'. cbv beta. cbn [add_reason rcl].
                     destruct (Nat.eqb_spec (nr x) j) as [<- | Hne].
                     +++ rewrite tget_tset_same. reflexivity.
                     +++ rewrite tget_tset_other by assumption. apply Htn. lia.
                 --- apply Arp4.
                 --- (* the trail positions: the end of the trail for clause j *)
                     intros j Hj'. cbv beta. cbn [add_reason rps].
                     destruct (Nat.eqb_spec (nr x) j) as [<- | Hne].
                     +++ rewrite tget_tset_same. reflexivity.
                     +++ rewrite tget_tset_other by assumption. apply Htp. lia.
                 --- tmp.
                 --- tmp.
                 --- tmp.
                 --- tmp.
Qed.

(* The invariant of the loop of push_reason at q, for the memory m of the call: the
   temporaries hold s, j = nr x, b = reasons_size (rcl x) (nr x), n = length lt and q,
   the literals t of block rlits hold the reason clauses of x, then u at b and the first
   q literals of lt after it, and the memory m1 is m but for rlits. *)
Record PushInv (m: mem) (S: Shape) (x: Ctx) (lt: list Lit) (u: Lit) (q: nat)
  (le: temp_env) (m1: mem): Prop := {
  pu_s: le ! _s = Some (sptr S);
  pu_j: le ! _j = Some (vint (Z.of_nat (nr x)));
  pu_b: le ! _b = Some (vint (Z.of_nat (reasons_size (rcl x) (nr x))));
  pu_n: le ! _n = Some (vint (Z.of_nat (length lt)));
  pu_q: le ! _q = Some (vint (Z.of_nat q));
  pu_le: (q <= length lt)%nat;
  pu_rlits: exists (t: nat -> Z), Arr m1 (b_rlits S) (rcap x) t /\
    ReasonsIn t (rcl x) (nr x) /\ t (reasons_size (rcl x) (nr x)) = key u /\
    forall (k: nat), (k < q)%nat ->
      t (reasons_size (rcl x) (nr x) + 1 + k)%nat = key (nth k lt (Pos 0%nat));
  pu_frame: Mem.unchanged_on (fun (b: block) (_: Z) => b <> b_rlits S) m m1;
}.

(* After the literal at position q of lt is stored at b + 1 + q, for
   b = reasons_size (rcl x) (nr x), the invariant holds at q + 1. *)
Lemma push_inv_next: forall (m m1: mem) (S: Shape) (x: Ctx) (lt: list Lit) (u: Lit)
  (q: nat) (le: temp_env) (t: nat -> Z),
  (q < length lt)%nat ->
  Arr m1 (b_rlits S) (rcap x) (fun (i: nat) =>
    if Nat.eqb (reasons_size (rcl x) (nr x) + 1 + q) i
    then key (nth q lt (Pos 0%nat)) else t i) ->
  ReasonsIn t (rcl x) (nr x) -> t (reasons_size (rcl x) (nr x)) = key u ->
  (forall (k: nat), (k < q)%nat ->
     t (reasons_size (rcl x) (nr x) + 1 + k)%nat = key (nth k lt (Pos 0%nat))) ->
  Mem.unchanged_on (fun (b: block) (_: Z) => b <> b_rlits S) m m1 ->
  le ! _s = Some (sptr S) -> le ! _j = Some (vint (Z.of_nat (nr x))) ->
  le ! _b = Some (vint (Z.of_nat (reasons_size (rcl x) (nr x)))) ->
  le ! _n = Some (vint (Z.of_nat (length lt))) ->
  le ! _q = Some (vint (Z.of_nat (Datatypes.S q))) ->
  PushInv m S x lt u (Datatypes.S q) le m1.
Proof.
  intros m m1 S x lt u q le t Hq Arl Hold Hu Hlits Hun Hs Hj Hb Hn Hq'.
  constructor.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - lia.
  - eexists. split.
    + apply Arl.
    + split.
      * (* the reason clauses are before b *)
        apply (reasons_in_ext t).
        -- assumption.
        -- intros k Hk.
           replace (Nat.eqb (reasons_size (rcl x) (nr x) + 1 + q) k) with false
             by (symmetry; apply Nat.eqb_neq; lia).
           reflexivity.
      * split.
        -- (* u is at b *)
           replace (Nat.eqb (reasons_size (rcl x) (nr x) + 1 + q)
                      (reasons_size (rcl x) (nr x))) with false
             by (symmetry; apply Nat.eqb_neq; lia).
           assumption.
        -- (* the first q + 1 literals of lt after it *)
           intros k Hk.
           destruct (Nat.eqb_spec (reasons_size (rcl x) (nr x) + 1 + q)
                       (reasons_size (rcl x) (nr x) + 1 + k)) as [Heq | Hne].
           ++ replace k with q by lia. reflexivity.
           ++ apply Hlits. lia.
  - assumption.
Qed.

(* The statements of push_reason after its tests: the literals and the end. *)
Definition push_stores: statement := drop_stmts 5 (fn_body f_push_reason).

(* The stores of push_reason, when there is room. Writing b for
   reasons_size (rcl x) (nr x), n for length lt and j for nr x:

     {{ RepL m x lt /\ j < N /\ b + n + 1 <= rcap x }}
       s->rlits[b] = u;
       int q = 0;
     {{ PushInv 0 }}
       while (q < n) {
     {{ PushInv q /\ q < n }}
         s->rlits[b + 1 + q] = s->lt[q];
         q++;
     {{ PushInv (q + 1) }}                                               (push_inv_next)
       }
     {{ PushInv n: rlits holds u :: lt as clause j }}                   (reasons_in_add)
       the end;                                                    (push_end_correct)
     {{ PushPost }}

   The loop ends: n - q decreases. *)
Lemma push_stores_correct {lt: list Lit}: forall (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (u: Lit) (le: temp_env) (m: mem),
  RepL m S N lss x lims lt -> (extract u < N)%nat -> (nr x < N)%nat ->
  (reasons_size (rcl x) (nr x) + length (u :: lt) <= rcap x)%nat ->
  le ! _s = Some (sptr S) -> le ! _u = Some (vint (key u)) ->
  le ! _j = Some (vint (Z.of_nat (nr x))) ->
  le ! _b = Some (vint (Z.of_nat (reasons_size (rcl x) (nr x)))) ->
  le ! _n = Some (vint (Z.of_nat (length lt))) ->
  Exec ge le m push_stores (Returns f_push_reason (PushPost m S N lss x lims lt u)).
Proof.
  intros S N lss x lims u le m HRep Hu Hnr Hroom Hs Hu' Hj Hb Hn.
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_rcap_small _ _ _ _ _ _ _ HRep) as Hrcap.
  pose proof (r_lt_le _ _ _ _ _ _ _ HRep) as Hltle.
  pose proof (r_rlits _ _ _ _ _ _ _ HRep) as Frl.
  pose proof (a_rlits _ _ _ _ _ _ _ HRep) as (trl & Arl & Htrl).
  assert (Hbr: (reasons_size (rcl x) (nr x) < rcap x)%nat)
    by (cbn [length] in Hroom; lia).
  unfold push_stores, f_push_reason. cbn [fn_body drop_stmts].
  (* s->rlits[b] = u; *)
  run. eapply exec_store.
  - evl.
  - ev.
  - reflexivity.
  - reflexivity.
  - ofs. bound.
  - ofs. cbn [cast_int_int].
    destruct (arr_storable m (b_rlits S) (rcap x) (reasons_size (rcl x) (nr x)) trl
                (key u) Arl Hbr) as [m1 Hst1].
    exists m1. split.
    + apply Hst1.
    + normal. pose proof (arr_store _ _ _ _ _ _ _ Arl Hbr Hst1) as Arl1. clear Arl.
      (* int q = 0; *)
      run. unfold Swhile.
      apply exec_loop with (R := ltof nat (fun (q: nat) => length lt - q)%nat)
        (I := PushInv m S x lt u) (a := 0%nat).
      * apply well_founded_ltof.
      * intros q le1 m2 HI.
        destruct HI as [Hs1 Hj1 Hb1 Hn1 Hq Hqle (t & Arl2 & Hold & Hfirst & Hlits) Hun].
        clear Arl1.
        apply exec_seq.
        (* if (q < n) ... else break; *)
        eapply (exec_if_cmp _ _ _ Clt).
        -- ev.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- unfold Small. lia.
        -- unfold Small. lia.
        -- destruct (Nat.lt_ge_cases q (length lt)) as [Hlt | Hge].
           ++ (* q < n: s->rlits[b + 1 + q] = s->lt[q]; q++; *)
              replace (zcmp Clt (Z.of_nat q) (Z.of_nat (length lt))) with true
                by (symmetry; cbn [zcmp]; apply Z.ltb_lt; lia).
              pose proof (r_lt _ _ _ _ _ _ _ HRep) as Flt.
              pose proof (a_lt _ _ _ _ _ _ _ HRep) as (tlt & Alt & Htlt).
              transfer Hun Hnd.
              assert (Hidx: Int.add (Int.add
                              (Int.repr (Z.of_nat (reasons_size (rcl x) (nr x))))
                              (Int.repr 1)) (Int.repr (Z.of_nat q))
                            = Int.repr (Z.of_nat (reasons_size (rcl x) (nr x) + 1 + q))).
              { rewrite !add_repr. f_equal. lia. }
              assert (Hadd: Int.add (Int.repr (Z.of_nat q)) (Int.repr 1)
                            = Int.repr (Z.of_nat (Datatypes.S q))).
              { rewrite add_repr. f_equal. lia. }
              assert (Hk: (reasons_size (rcl x) (nr x) + 1 + q < rcap x)%nat)
                by (cbn [length] in Hroom; lia).
              cbv beta iota. apply exec_skip. normal. run.
              rewrite (Htlt q) by assumption.
              eapply exec_store.
              ** evl.
              ** ev.
              ** reflexivity.
              ** reflexivity.
              ** ofs. bound.
              ** ofs. cbn [cast_int_int].
                 destruct (arr_storable m2 (b_rlits S) (rcap x)
                             (reasons_size (rcl x) (nr x) + 1 + q) t
                             (key (nth q lt (Pos 0%nat))) Arl2 Hk) as [m3 Hst3].
                 exists m3. split.
                 --- apply Hst3.
                 --- normal. run. ints. apply loopk_next with (Datatypes.S q).
                     +++ unfold ltof. lia.
                     +++ apply (push_inv_next m m3 S x lt u q _ t).
                         *** assumption.
                         *** apply (arr_store _ _ _ _ _ _ _ Arl2 Hk Hst3).
                         *** assumption.
                         *** assumption.
                         *** assumption.
                         *** apply (store_unchanged _ m m2 m3 Mint32 (b_rlits S)
                                      (4 * Z.of_nat
                                             (reasons_size (rcl x) (nr x) + 1 + q))
                                      (vint (key (nth q lt (Pos 0%nat))))).
                             ---- assumption.
                             ---- assumption.
                             ---- intros i Hi. now apply Hi.
                         *** tmp.
                         *** tmp.
                         *** tmp.
                         *** tmp.
                         *** tmp.
           ++ (* q = n: break; and the end, with u :: lt as clause j *)
              replace (zcmp Clt (Z.of_nat q) (Z.of_nat (length lt))) with false
                by (symmetry; cbn [zcmp]; apply Z.ltb_ge; lia).
              cbv beta iota. apply exec_break. abrupt. apply loopk_break. normal.
              apply (push_end_correct S N lss x lims u t _ m m2).
              ** assumption.
              ** assumption.
              ** assumption.
              ** assumption.
              ** assumption.
              ** assumption.
              ** cbn [add_reason rcl nr]. apply reasons_in_add.
                 --- assumption.
                 --- intros k Hk. destruct k as [|k].
                     +++ rewrite Nat.add_0_r. assumption.
                     +++ cbn [nth]. cbn [length] in Hk.
                         replace (reasons_size (rcl x) (nr x) + Datatypes.S k)%nat
                           with (reasons_size (rcl x) (nr x) + 1 + k)%nat by lia.
                         apply Hlits. lia.
              ** tmp.
              ** tmp.
              ** tmp.
              ** tmp.
      * (* The invariant holds at q = 0, with u at b. *)
        constructor.
        -- tmp.
        -- tmp.
        -- tmp.
        -- tmp.
        -- tmp.
        -- lia.
        -- eexists. split.
           ++ apply Arl1.
           ++ split.
              ** apply (reasons_in_ext trl).
                 --- assumption.
                 --- intros k Hk.
                     replace (Nat.eqb (reasons_size (rcl x) (nr x)) k) with false
                       by (symmetry; apply Nat.eqb_neq; lia).
                     reflexivity.
              ** split.
                 --- rewrite Nat.eqb_refl. reflexivity.
                 --- intros k Hk. lia.
        -- apply (store_unchanged _ m m m1 Mint32 (b_rlits S)
                    (4 * Z.of_nat (reasons_size (rcl x) (nr x))) (vint (key u))).
           ++ apply Mem.unchanged_on_refl.
           ++ assumption.
           ++ intros i Hi. now apply Hi.
Qed.

(* Without room, push_reason keeps x and gives no reason, which C returns as 0. *)
Lemma push_none {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (u: Lit) (m: mem),
  RepL m S N lss x lims lt -> push_reason x u lt = (x, no_reason) ->
  RepL m S N lss (fst (push_reason x u lt)) lims lt /\
  vint 0 = vint (enc_reason (snd (push_reason x u lt))) /\
  ReasonBelow (length lss) N (snd (push_reason x u lt)) /\
  Mem.unchanged_on (fun (b: block) (_: Z) =>
    b <> b_rlits S /\ b <> b_rbeg S /\ b <> b_rlen S /\ b <> b_rpos S /\
    b <> b_s S) m m.
Proof.
  intros S N lss x lims u m HRep Hpush. rewrite Hpush. cbn [fst snd]. split.
  - assumption.
  - split.
    + reflexivity.
    + split.
      * cbn [ReasonBelow]. apply I.
      * apply Mem.unchanged_on_refl.
Qed.

(* push_reason stores u :: lt as a new reason clause, for the literal at the end of the
   trail, if there is room for one more clause (at most N) and its literals (at most
   rcap x), and gives that clause as the reason, or no reason:

     {{ RepL m S N lss x lims lt /\ extract u < N }}
       int j = s->nr;
       int b = s->rtop;
       int n = s->ltlen;
       if (j >= s->nv) return 0;
       if (n >= s->rcap - b) return 0;
     {{ result = 0 = enc_reason no_reason, and push_reason x u lt = (x, no_reason) }}
     {{ RepL x lt /\ j = nr x < N /\ b + n + 1 <= rcap x }}
       the stores, and return -(j + 1);                           (push_stores_correct)
     {{ PushPost: push_reason x u lt = (add_reason x (u :: lt), learnt j) }}        *)
Lemma push_reason_correct {lt: list Lit}: forall (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (u: Lit),
  {{ m | RepL m S N lss x lims lt /\ (extract u < N)%nat }}
    f_push_reason(sptr S, vint (key u))
  {{ m', v | RepL m' S N lss (fst (push_reason x u lt)) lims lt /\
             v = vint (enc_reason (snd (push_reason x u lt))) /\
             ReasonBelow (length lss) N (snd (push_reason x u lt)) /\
             Mem.unchanged_on (fun (b: block) (_: Z) =>
               b <> b_rlits S /\ b <> b_rbeg S /\ b <> b_rlen S /\ b <> b_rpos S /\
               b <> b_s S) m m' }}.
Proof.
  intros S N lss x lims u m [HRep Hu].
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_nvars _ _ _ _ _ _ _ HRep) as Hnv.
  pose proof (r_nr_le _ _ _ _ _ _ _ HRep) as Hnrle.
  pose proof (r_rsize_le _ _ _ _ _ _ _ HRep) as Hsize.
  pose proof (r_rcap_small _ _ _ _ _ _ _ HRep) as Hrcap.
  pose proof (r_lt_le _ _ _ _ _ _ _ HRep) as Hltle.
  pose proof (r_nv _ _ _ _ _ _ _ HRep) as Fnv.
  pose proof (r_nr _ _ _ _ _ _ _ HRep) as Fnr.
  pose proof (r_rtop _ _ _ _ _ _ _ HRep) as Frtop.
  pose proof (r_ltlen _ _ _ _ _ _ _ HRep) as Fltlen.
  pose proof (r_rcap _ _ _ _ _ _ _ HRep) as Frcap.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_push_reason. cbn [fn_body fn_return].
    (* int j = s->nr; int b = s->rtop; int n = s->ltlen; *)
    run.
    (* if (j >= s->nv) return 0; *)
    eapply (exec_if_cmp _ _ _ Cge).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + unfold Small. lia.
    + unfold Small. lia.
    + destruct (Nat.lt_ge_cases (nr x) N) as [Hnr | Hfull].
      * (* room for one more clause *)
        replace (zcmp Cge (Z.of_nat (nr x)) (Z.of_nat N)) with false
          by (symmetry; cbn [zcmp]; apply Z.leb_gt; lia).
        cbv beta iota. apply exec_skip. normal.
        (* if (n >= s->rcap - b) return 0; *)
        run.
        eapply (exec_if_cmp _ _ _ Cge _ _ (Z.of_nat (length lt))
                  (Z.of_nat (rcap x) - Z.of_nat (reasons_size (rcl x) (nr x)))).
        -- ev.
        -- eapply eval_Ebinop.
           ++ ev.
           ++ ev.
           ++ cbn -[Int.sub Int.repr]. unfold vint. rewrite <- sub_repr. reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- unfold Small. lia.
        -- unfold Small. lia.
        -- cbn [zcmp].
           destruct (Nat.leb_spec (reasons_size (rcl x) (nr x) + length (u :: lt))
                       (rcap x)) as [Hroom | Hover].
           ++ (* room for its literals: the stores *)
              replace (Z.of_nat (rcap x) - Z.of_nat (reasons_size (rcl x) (nr x))
                       <=? Z.of_nat (length lt)) with false
                by (symmetry; apply Z.leb_gt; cbn [length] in Hroom; lia).
              assert (Hpush: push_reason x u lt
                             = (add_reason x (u :: lt), learnt (nr x))).
              { unfold push_reason. rewrite Hnv.
                replace (nr x <? N)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
                replace (reasons_size (rcl x) (nr x) + Datatypes.S (length lt)
                         <=? rcap x)%nat with true
                  by (symmetry; apply Nat.leb_le; assumption).
                reflexivity. }
              rewrite Hpush. cbn [fst snd].
              cbv beta iota. apply exec_skip. normal.
              apply (push_stores_correct S N lss x lims u).
              ** assumption.
              ** assumption.
              ** assumption.
              ** assumption.
              ** tmp.
              ** tmp.
              ** tmp.
              ** tmp.
              ** tmp.
           ++ (* no room for its literals: return 0; *)
              replace (Z.of_nat (rcap x) - Z.of_nat (reasons_size (rcl x) (nr x))
                       <=? Z.of_nat (length lt)) with true
                by (symmetry; apply Z.leb_le; cbn [length] in Hover; lia).
              cbv beta iota. eapply exec_return.
              ** ev.
              ** ret. exists (vint 0). split.
                 --- apply result_int.
                 --- apply (push_none S N lss x lims u m HRep).
                     unfold push_reason.
                     replace (reasons_size (rcl x) (nr x) + Datatypes.S (length lt)
                              <=? rcap x)%nat
                       with false by (symmetry; apply Nat.leb_gt; assumption).
                     rewrite andb_false_r. reflexivity.
      * (* no room for one more clause: return 0; *)
        replace (zcmp Cge (Z.of_nat (nr x)) (Z.of_nat N)) with true
          by (symmetry; cbn [zcmp]; apply Z.leb_le; lia).
        cbv beta iota. eapply exec_return.
        -- ev.
        -- ret. exists (vint 0). split.
           ++ apply result_int.
           ++ apply (push_none S N lss x lims u m HRep).
              unfold push_reason. rewrite Hnv.
              replace (nr x <? N)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
              reflexivity.
Qed.

Lemma push_reason_fun: exists (b: block),
  Genv.find_symbol ge _push_reason = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_push_reason).
Proof. apply find_fun. reflexivity. Qed.
