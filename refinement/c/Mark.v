(* mark marks a literal for the analysis and bumps its atom (the marking of add_lits). *)
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
From RocqSAT.refinement Require Import Heur.
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement Require Import Analysis.
From RocqSAT.refinement Require Import Step.
From RocqSAT.refinement.c Require Import Arrays.
From RocqSAT.refinement.c Require Import Logic.
From RocqSAT.refinement.c Require Import Common.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Rep.
From RocqSAT.refinement.c Require Import RepReasons.
From RocqSAT.refinement.c Require Import RepHeur.
From RocqSAT.refinement.c Require Import Bump.

(* Every block but those mark writes: the marks and those of the heuristic. *)
Definition MarkFrame (sh: Shape): block -> Z -> Prop :=
  fun (b: block) (ofs: Z) => b <> b_mrk sh /\ HeurFrame sh b ofs.

(* mark sets the mark of y and bumps the activity of its atom:

     {{ RepL x /\ extract y < N }}
       s->mrk[y] = 1;                                                     (rep_store_mrk)
     {{ RepL (x <| mrk := tset (mrk x) (lit_key y) true |>) }}
       bump(s, y >> 1);                                                     (bump_correct)
     {{ RepL (mark x y) /\ only the marks and the heuristic changed }}               *)
Lemma mark_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (y: Lit),
  {{ m | RepL m sh N lss x /\ (extract y < N)%nat }}
    f_mark(sptr sh, vint (key y))
  {{ m', v | RepL m' sh N lss (mark x y) /\ Mem.unchanged_on (MarkFrame sh) m m' }}.
Proof.
  intros sh N lss x y m [HRep Hy].
  pose proof (r_n HRep) as HN.
  pose proof (r_nodup HRep) as Hnd.
  pose proof (r_mrk HRep) as Fmrk.
  pose proof (a_mrk HRep) as Amrk.
  pose proof (key_small y N Hy HN) as Hky.
  assert (Hkey: (lit_key y < 2 * N)%nat) by (apply lit_key_lt; assumption).
  assert (Hshr: Int.shr (Int.repr (key y)) (Int.repr 1) =
                Int.repr (Z.of_nat (extract y))).
  { apply shr_key. lia. }
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_mark. cbn [fn_body fn_return].
    (* s->mrk[y] = 1; *)
    run. store Amrk Hkey as m1 Hst1.
    pose proof (rep_store_mrk m m1 (lit_key y) true HRep Hkey Hst1)
      as HRep1.
    (* bump(s, y >> 1); *)
    eapply (exec_call_triple_none bump_fun
              (bump_correct sh N lss (x <| mrk := tset (mrk x) (lit_key y) true |>)
                 (extract y))).
    + reflexivity.
    + unfold vint. rewrite <- Hshr. evs.
    + split.
      * apply HRep1.
      * assumption.
    + intros m2 v [HRep2 Hun2]. return_none.
      split.
      * unfold mark. rewrite (r_nvars HRep). apply HRep2.
      * (* only the marks and the heuristic changed *)
        frame.
Qed.

Lemma mark_fun: FunAt _mark f_mark.
Proof. apply find_fun. reflexivity. Qed.
