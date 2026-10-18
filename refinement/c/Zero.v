(* zero sets the entries of an int array to zero; fill_none, which differs only in the
   value it stores, is proved with it (FillNone.v). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Ctypesdefs Cop Clight ClightBigstep.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep.
Import ListNotations.

(* The Clight of a function that stores the value of e into n ints from p on; zero and
   fill_none are this function for e = 0 and e = -1:
     static void fill(int *p, int n) { int q = 0; while (q < n) { p[q] = e; q++; } } *)
Definition fill_fun (e: expr): function := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tint)) :: (_n, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_q, tint) :: nil);
  fn_body :=
    Ssequence (Sset _q (Econst_int (Int.repr 0) tint))
      (Swhile (Ebinop Olt (Etempvar _q tint) (Etempvar _n tint) tint)
        (Ssequence
          (Sassign
            (Ederef (Ebinop Oadd (Etempvar _p (tptr tint)) (Etempvar _q tint)
                       (tptr tint)) tint) e)
          (Sset _q
            (Ebinop Oadd (Etempvar _q tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

(* The invariant of the loop of fill_fun e, at q, for an array b of n ints in the
   memory m before the call: the temporaries hold b, n and q, the entries below q are z,
   and the memory m1 is m but for b. *)
Record FillInv {m: mem} {b: block} {n: nat} {z: Z} {q: nat} {le: temp_env} {m1: mem}:
  Prop := {
  fi_p: le ! _p = Some (Vptr b Ptrofs.zero);
  fi_n: le ! _n = Some (vnat n);
  fi_q: le ! _q = Some (vnat q);
  fi_le: (q <= n)%nat;
  fi_arr: exists (t: nat -> Z), Arr m1 b n t /\ forall (k: nat), (k < q)%nat -> t k = z;
  fi_frame: Mem.unchanged_on (AllBut b) m m1;
}.
Arguments FillInv : clear implicits.

(* fill_fun e, for an int expression e of value z, stores z into every entry of the
   array, and nothing else:

     {{ Arr m b n t }}
       int q = 0;
     {{ FillInv m b n z 0 }}
       while (q < n) {
     {{ FillInv m b n z q /\ q < n }}
         p[q] = e;
         q++;
     {{ FillInv m b n z (q + 1) }}
       }
     {{ FillInv m b n z q /\ q >= n }} ->>
     {{ Arr m' b n (fun _ => z) /\ m' is m but for b }}

   The loop ends: n - q decreases. *)
Lemma fill_correct: forall (e: expr) (z: Z),
  typeof e = tint ->
  (forall (le: temp_env) (m: mem), eval_expr ge empty_env le m e (vint z)) ->
  forall (b: block) (n: nat) (t: nat -> Z),
  {{ m | Arr m b n t /\ Z.of_nat n < small_bound }}
    (fill_fun e)(Vptr b Ptrofs.zero, vnat n)
  {{ m', v | Arr m' b n (fun (_: nat) => z) /\ Mem.unchanged_on (AllBut b) m m' }}.
Proof.
  intros e z Hty He b n t m [A Hn]. eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold fill_fun. cbn [fn_body fn_return].
    (* int q = 0; *)
    run. unfold Swhile.
    apply exec_loop with (R := ltof nat (fun (q: nat) => n - q)%nat)
      (I := FillInv m b n z) (a := 0%nat).
    + apply well_founded_ltof.
    + intros q le1 m1 HI. destruct HI as [Hp Hn' Hq Hqn [t1 [A1 Hfilled]] Hframe].
      apply exec_seq.
      (* if (q < n) ... else break; *)
      eapply exec_if_lt.
      * ev.
      * ev.
      * reflexivity.
      * lia.
      * (* q < n: p[q] = e; q++; *)
        intros Hlt_z. assert (Hlt: (q < n)%nat) by lia.
        assert (Hadd: Int.add (Int.repr (Z.of_nat q)) (Int.repr 1)
                      = Int.repr (Z.of_nat (S q))).
        { rewrite add_repr by lia. f_equal. lia. }
        run. eapply (exec_store_arr A1 Hlt).
        -- evl.
        -- ofs.
        -- rewrite Hty. reflexivity.
        -- apply He.
        -- intros m2 Hst. normal. run. ints. apply loopk_next with (S q).
           ++ unfold ltof. lia.
           ++ constructor.
              ** tmp.
              ** tmp.
              ** tmp.
              ** lia.
              ** exists (fun (j: nat) => if Nat.eqb q j then z else t1 j). split.
                 --- apply (arr_store A1 Hlt Hst).
                 --- intros k Hk. destruct (Nat.eqb_spec q k) as [<- | Hne].
                     +++ reflexivity.
                     +++ apply Hfilled. lia.
              ** apply (store_unchanged _ m m1 m2 Mint32 b (4 * Z.of_nat q) (vint z)).
                 --- assumption.
                 --- assumption.
                 --- intros i Hi. now apply Hi.
      * (* q >= n: break; every entry is z *)
        intros Hge. apply exec_break. abrupt. apply loopk_break.
        exists Vundef. split.
        -- reflexivity.
        -- split.
           ++ apply (arr_ext m1 b n t1).
              ** assumption.
              ** intros k Hk. symmetry. apply Hfilled. lia.
           ++ assumption.
    + (* The invariant holds at q = 0. *)
      constructor.
      * tmp.
      * tmp.
      * tmp.
      * lia.
      * exists t. split.
        -- assumption.
        -- intros k Hk. lia.
      * apply Mem.unchanged_on_refl.
Qed.

(* zero stores 0 into every entry of the array, and nothing else. *)
Lemma zero_correct: forall (b: block) (n: nat) (t: nat -> Z),
  {{ m | Arr m b n t /\ Z.of_nat n < small_bound }}
    f_zero(Vptr b Ptrofs.zero, vnat n)
  {{ m', v | Arr m' b n (fun (_: nat) => 0) /\ Mem.unchanged_on (AllBut b) m m' }}.
Proof.
  apply (fill_correct (Econst_int (Int.repr 0) tint) 0).
  - reflexivity.
  - intros le m. ev.
Qed.

Lemma zero_fun: FunAt _zero f_zero.
Proof. apply find_fun. reflexivity. Qed.
