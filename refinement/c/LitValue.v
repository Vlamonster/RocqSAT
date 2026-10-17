(* lit_value computes the value of a literal: lookup on the values of the context. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Propagate.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep.
Import ListNotations.

(* lit_value reads the value of l, kept per literal (key_value_lookup). It stores
   nothing, so the memory stays m; it runs also during an analysis (any lower literals
   lt):

     {{ RepL m S N lss x lims lt /\ extract l < N }}
       return s->vals[l];
     {{ result = key_value (vals x) (lit_key l) = enc_value (lookup (vals x) l) }}    *)
Lemma lit_value_correct {lt: list Lit}: forall (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (l: Lit),
  {{ m | RepL m S N lss x lims lt /\ (extract l < N)%nat }}
    f_lit_value(sptr S, vint (key l))
  {{ m', v | m' = m /\ v = vint (enc_value (lookup (vals x) l)) }}.
Proof.
  intros S N lss x lims l m [HRep Hl].
  pose proof (key_small l N Hl (r_n _ _ _ _ _ _ _ HRep)) as Hkey.
  pose proof (lit_key_lt l N Hl) as Hlt.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_lit_value. cbn [fn_body fn_return]. destruct HRep. unfold key in *.
    (* return s->vals[l]; *)
    run. eapply exec_return.
    + ev.
    + exists (vint (key_value (vals x) (lit_key l))). split.
      * apply result_int.
      * split.
        -- reflexivity.
        -- now rewrite key_value_lookup.
Qed.

Lemma lit_value_fun: exists (b: block),
  Genv.find_symbol ge _lit_value = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_lit_value).
Proof. apply find_fun. reflexivity. Qed.
