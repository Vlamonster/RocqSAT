(* set_value sets the value of an atom, for both its literals (the tset of the values in
   assign and jump). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Propagate.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep.
Import ListNotations.

(* set_value stores the value o of atom a at the entries of its two literals, 2a and
   2a + 1 (v = enc_value o). Only the values change:

     {{ RepL m sh N lss x /\ a < N }}
       s->vals[2 * a] = v;
       s->vals[2 * a + 1] = -v;                                         (rep_store_vals)
     {{ RepL (x <| vals := tset (vals x) a o |>) /\ only the values changed }}       *)
Lemma set_value_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (a: nat) (o: option bool),
  {{ m | RepL m sh N lss x /\ (a < N)%nat }}
    f_set_value(sptr sh, vnat a, vint (enc_value o))
  {{ m', v | RepL m' sh N lss (x <| vals := tset (vals x) a o |>) /\
             Mem.unchanged_on (AllBut (b_vals sh)) m m' }}.
Proof.
  intros sh N lss x a o m [HRep Ha].
  pose proof (r_n HRep) as HN.
  pose proof (r_vals HRep) as Fvals.
  pose proof (a_vals HRep) as Avals.
  (* The entries of the two literals of a, as C computes them. *)
  assert (Hpos: Int.mul (Int.repr 2) (Int.repr (Z.of_nat a))
                = Int.repr (Z.of_nat (2 * a))).
  { rewrite mul_repr. f_equal. lia. }
  assert (Hneg: Int.add (Int.repr (Z.of_nat (2 * a))) (Int.repr 1)
                = Int.repr (Z.of_nat (2 * a + 1))).
  { rewrite add_repr. f_equal. lia. }
  assert (Hv: Int.neg (Int.repr (enc_value o)) = Int.repr (- enc_value o)).
  { apply Int.neg_repr. }
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_set_value. cbn [fn_body fn_return].
    (* s->vals[2 * a] = v; *)
    assert (Hpos_lt: (2 * a < 2 * N)%nat) by lia.
    run. eapply (exec_store_arr Avals Hpos_lt).
    + evl.
    + ofs.
    + reflexivity.
    + ev.
    + intros m1 Hst1. normal.
      pose proof (arr_store Avals Hpos_lt Hst1) as Avals1.
      pose proof (r_nodup HRep) as Hnd.
      assert (Fvals1: PtrAt m1 sh o_vals (b_vals sh)).
      { apply (fld_store_other Fvals Hst1). left. neq Hnd. }
      clear Fvals Avals.
      (* s->vals[2 * a + 1] = -v; *)
      assert (Hneg_lt: (2 * a + 1 < 2 * N)%nat) by lia.
      run. eapply (exec_store_arr Avals1 Hneg_lt).
      * evl.
      * ofs.
      * reflexivity.
      * ev.
      * intros m2 Hst2. rewrite Hv in Hst2. exists Vundef. split.
        -- reflexivity.
        -- split.
           ++ apply (rep_store_vals m m1 m2 a o HRep Ha Hst1 Hst2).
           ++ (* only the values changed *)
              apply (store_unchanged _ m m1 m2 Mint32 (b_vals sh)
                       (4 * Z.of_nat (2 * a + 1)) (vint (- enc_value o))).
              ** apply (store_unchanged _ m m m1 Mint32 (b_vals sh)
                          (4 * Z.of_nat (2 * a)) (vint (enc_value o))).
                 --- apply Mem.unchanged_on_refl.
                 --- apply Hst1.
                 --- intros j Hb. now apply Hb.
              ** apply Hst2.
              ** intros j Hb. now apply Hb.
Qed.

Lemma set_value_fun: FunAt _set_value f_set_value.
Proof. apply find_fun. reflexivity. Qed.
