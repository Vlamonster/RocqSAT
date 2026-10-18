(* set_value sets the value of an atom, for both its literals (the tset of the values in
   assign and jump). *)
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
From RocqSAT.refinement Require Import Table.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement.c Require Import Arrays.
From RocqSAT.refinement.c Require Import Logic.
From RocqSAT.refinement.c Require Import Common.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Rep.

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
    run. store Avals Hpos_lt as m1 Hst1.
    pose proof (arr_store Avals Hpos_lt Hst1) as Avals1.
    pose proof (r_nodup HRep) as Hnd.
    assert (Fvals1: PtrAt m1 sh o_vals (b_vals sh)).
    { apply (fld_store_other Fvals Hst1). left. neq Hnd. }
    clear Fvals Avals.
    (* s->vals[2 * a + 1] = -v; *)
    assert (Hneg_lt: (2 * a + 1 < 2 * N)%nat) by lia.
    run. store Avals1 Hneg_lt as m2 Hst2.
    rewrite Hv in Hst2. return_none.
    split.
    + apply (rep_store_vals m m1 m2 a o HRep Ha Hst1 Hst2).
    + (* only the values changed *)
      frame.
Qed.

Lemma set_value_fun: FunAt _set_value f_set_value.
Proof. apply find_fun. reflexivity. Qed.
