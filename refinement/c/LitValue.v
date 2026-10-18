(* lit_value computes the value of a literal: lookup on the values of the context. *)
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

(* lit_value reads the value of l, kept per literal (key_value_lookup). It stores
   nothing, so the memory stays m. It needs RepL only, so it also runs during an
   analysis:

     {{ RepL m sh N lss x /\ extract l < N }}
       return s->vals[l];
     {{ result = key_value (vals x) (lit_key l) = enc_value (lookup (vals x) l) }}    *)
Lemma lit_value_correct: forall (sh: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (l: Lit),
  {{ m | RepL m sh N lss x /\ (extract l < N)%nat }}
    f_lit_value(sptr sh, vint (key l))
  {{ m', v | m' = m /\ v = vint (enc_value (lookup (vals x) l)) }}.
Proof.
  intros sh N lss x l m [HRep Hl].
  pose proof (key_small l N Hl (r_n HRep)) as Hkey.
  pose proof (lit_key_lt l N Hl) as Hlt.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_lit_value. cbn [fn_body fn_return]. destruct HRep. unfold key in *.
    (* return s->vals[l]; *)
    run. return_int.
    split.
    + reflexivity.
    + now rewrite key_value_lookup.
Qed.

Lemma lit_value_fun: FunAt _lit_value f_lit_value.
Proof. apply find_fun. reflexivity. Qed.
