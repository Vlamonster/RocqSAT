(* mark marks a literal for the analysis and bumps its atom (the marking of add_lits). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Heur Propagate Analysis Step.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep RepReasons RepHeur Bump.
Import ListNotations.

(* The blocks mark writes: the marks and those of the heuristic. *)
Definition MarkFrame (S: Shape): block -> Z -> Prop :=
  fun (b: block) (ofs: Z) => b <> b_mrk S /\ HeurFrame S b ofs.

(* mark sets the mark of y and bumps the activity of its atom:

     {{ RepL x lt /\ extract y < N }}
       s->mrk[y] = 1;                                                     (rep_store_mrk)
     {{ RepL (set_mrk x (tset (mrk x) (lit_key y) true)) lt }}
       bump(s, y >> 1);                                                     (bump_correct)
     {{ RepL with the mark of y and the bumped heuristic /\ only those changed }}      *)
Lemma mark_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (y: Lit),
  {{ m | RepL m S N lss x lims lt /\ (extract y < N)%nat }}
    f_mark(sptr S, vint (key y))
  {{ m', v | RepL m' S N lss (with_heur (set_mrk x (tset (mrk x) (lit_key y) true))
                                (bump (hr x) N (extract y))) lims lt /\
             Mem.unchanged_on (MarkFrame S) m m' }}.
Proof.
  intros S N lss x lims y m [HRep Hy].
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_mrk _ _ _ _ _ _ _ HRep) as Fmrk.
  pose proof (a_mrk _ _ _ _ _ _ _ HRep) as Amrk.
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
    run. eapply exec_store.
    + evl.
    + ev.
    + reflexivity.
    + reflexivity.
    + ofs. bound.
    + ofs. cbn [cast_int_int].
      destruct (arr_storable m (b_mrk S) (2 * N) (lit_key y) _ (enc_mark true) Amrk Hkey)
        as [m1 Hst1].
      exists m1. split.
      * apply Hst1.
      * normal.
        pose proof (rep_store_mrk m m1 S N lss x lims (lit_key y) true HRep Hkey Hst1)
          as HRep1.
        (* bump(s, y >> 1); *)
        call bump_fun. cbn [cast_int_int]. rewrite Hshr. eapply call_weaken.
        -- apply (bump_correct (lt := lt) S N lss
                    (set_mrk x (tset (mrk x) (lit_key y) true)) lims (extract y)).
           split.
           ++ assumption.
           ++ assumption.
        -- intros m2 v [HRep2 Hun2]. exists Vundef. split.
           ++ reflexivity.
           ++ split.
              ** apply HRep2.
              ** (* only the marks and the heuristic changed *)
                 apply (Mem.unchanged_on_trans _ m m1 m2).
                 --- apply (store_unchanged _ m m m1 Mint32 (b_mrk S) _ _
                              (Mem.unchanged_on_refl _ m) Hst1).
                     intros i [Hb _]. apply Hb. reflexivity.
                 --- apply (Mem.unchanged_on_implies _ _ _ _ Hun2).
                     intros b0 ofs [_ Hb] _. assumption.
Qed.

Lemma mark_fun: exists (b: block),
  Genv.find_symbol ge _mark = Some b /\ Genv.find_funct_ptr ge b = Some (Internal f_mark).
Proof. apply find_fun. reflexivity. Qed.
