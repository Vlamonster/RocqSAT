(* zero sets the entries of an int array to zero. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep.
Import ListNotations.

(* The invariant of the loop of zero, at q, for an array b of n ints in the memory m
   before the call: the temporaries hold b, n and q, the entries below q are 0, and the
   memory m1 is m but for b. *)
Record ZeroInv (m: mem) (b: block) (n q: nat) (le: temp_env) (m1: mem): Prop := {
  zi_p: le ! _p = Some (Vptr b Ptrofs.zero);
  zi_n: le ! _n = Some (vint (Z.of_nat n));
  zi_q: le ! _q = Some (vint (Z.of_nat q));
  zi_le: (q <= n)%nat;
  zi_arr: exists (t: nat -> Z), Arr m1 b n t /\ forall (k: nat), (k < q)%nat -> t k = 0;
  zi_frame: Mem.unchanged_on (fun (b': block) (_: Z) => b' <> b) m m1;
}.

(* zero stores 0 into every entry of the array, and nothing else:

     {{ Arr m b n t }}
       int q = 0;
     {{ ZeroInv m b n 0 }}
       while (q < n) {
     {{ ZeroInv m b n q /\ q < n }}
         p[q] = 0;
         q++;
     {{ ZeroInv m b n (q + 1) }}
       }
     {{ ZeroInv m b n q /\ q >= n }} ->>
     {{ Arr m' b n (fun _ => 0) /\ m' is m but for b }}

   The loop ends: n - q decreases. *)
Lemma zero_correct: forall (b: block) (n: nat) (t: nat -> Z),
  {{ m | Arr m b n t /\ Z.of_nat n < 1073741824 }}
    f_zero(Vptr b Ptrofs.zero, vint (Z.of_nat n))
  {{ m', v | Arr m' b n (fun (_: nat) => 0) /\
             Mem.unchanged_on (fun (b': block) (_: Z) => b' <> b) m m' }}.
Proof.
  intros b n t m [A Hn]. eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_zero. cbn [fn_body fn_return].
    (* int q = 0; *)
    run. unfold Swhile.
    apply exec_loop with (R := ltof nat (fun (q: nat) => n - q)%nat) (I := ZeroInv m b n)
      (a := 0%nat).
    + apply well_founded_ltof.
    + intros q le1 m1 HI. destruct HI as [Hp Hn' Hq Hqn [t1 [A1 Hzero]] Hframe].
      apply exec_seq.
      (* if (q < n) ... else break; *)
      eapply (exec_if_cmp _ _ _ Clt).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * destruct (Nat.lt_ge_cases q n) as [Hlt | Hge].
        -- (* q < n: p[q] = 0; q++; *)
           replace (zcmp Clt (Z.of_nat q) (Z.of_nat n)) with true
             by (symmetry; cbn [zcmp]; apply Z.ltb_lt; lia).
           assert (Hadd: Int.add (Int.repr (Z.of_nat q)) (Int.repr 1)
                         = Int.repr (Z.of_nat (Datatypes.S q))).
           { rewrite add_repr by lia. f_equal. lia. }
           cbv beta iota. run. eapply exec_store.
           ++ evl.
           ++ ev.
           ++ reflexivity.
           ++ reflexivity.
           ++ ofs. bound.
           ++ ofs. cbn [cast_int_int].
              destruct (arr_storable m1 b n q t1 0 A1 Hlt) as [m2 Hst].
              exists m2. split.
              ** apply Hst.
              ** normal. run. ints. apply loopk_next with (Datatypes.S q).
                 --- unfold ltof. lia.
                 --- constructor.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
                     +++ lia.
                     +++ exists (fun (j: nat) => if Nat.eqb q j then 0 else t1 j). split.
                         *** apply (arr_store m1 m2 b n q t1 0 A1 Hlt Hst).
                         *** intros k Hk. destruct (Nat.eqb_spec q k) as [<- | Hne].
                             ---- reflexivity.
                             ---- apply Hzero. lia.
                     +++ apply (store_unchanged _ m m1 m2 Mint32 b (4 * Z.of_nat q)
                                  (vint 0)).
                         *** assumption.
                         *** assumption.
                         *** intros i Hi. now apply Hi.
        -- (* q >= n: break; every entry is 0 *)
           replace (zcmp Clt (Z.of_nat q) (Z.of_nat n)) with false
             by (symmetry; cbn [zcmp]; apply Z.ltb_ge; lia).
           cbv beta iota. apply exec_break. abrupt. apply loopk_break.
           exists Vundef. split.
           ++ reflexivity.
           ++ split.
              ** apply (arr_ext m1 b n t1).
                 --- assumption.
                 --- intros k Hk. symmetry. apply Hzero. lia.
              ** assumption.
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

Lemma zero_fun: exists (b: block),
  Genv.find_symbol ge _zero = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_zero).
Proof. apply find_fun. reflexivity. Qed.
