(* fill_none sets the entries of an int array to -1, which encodes none (enc_pos,
   enc_lit); it is fill_fun of Zero.v for the value -1. *)
From compcert Require Import Coqlib Integers Values Memory AST Ctypes Ctypesdefs Cop
  Clight.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep Zero.

(* fill_none stores -1 into every entry of the array, and nothing else. *)
Lemma fill_none_correct: forall (b: block) (n: nat) (t: nat -> Z),
  {{ m | Arr m b n t /\ Z.of_nat n < small_bound }}
    f_fill_none(Vptr b Ptrofs.zero, vnat n)
  {{ m', v | Arr m' b n (fun (_: nat) => -1) /\ Mem.unchanged_on (AllBut b) m m' }}.
Proof.
  apply (fill_correct (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) (-1)).
  - reflexivity.
  - intros le m. ev.
Qed.

Lemma fill_none_fun: FunAt _fill_none f_fill_none.
Proof. apply find_fun. reflexivity. Qed.
