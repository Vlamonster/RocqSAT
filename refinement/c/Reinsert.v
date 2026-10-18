(* reinsert puts the atoms of a range of the trail back in the heap (reinsert). *)
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
From RocqSAT.refinement.c Require Import RepHeur.
From RocqSAT.refinement.c Require Import HeapInsert.

(* The invariant of the loop of reinsert at q: the memory represents x with a heuristic
   h that reinserting from q on turns into res, and m1 is m on HeurFrame. *)
Record ReinsertInv {m: mem} {sh: Shape} {N: nat} {lss: list (list Lit)}
  {x: Ctx} {j: nat} {res: Heur} {q: nat} {le: temp_env} {m1: mem}:
  Prop := {
  ri_s: le ! _s = Some (sptr sh);
  ri_j: le ! _j = Some (vnat j);
  ri_q: le ! _q = Some (vnat q);
  ri_range: (j <= q <= tlen x)%nat;
  ri_heur: exists (h: Heur), reinsert h (tr x) N j q (q - j) = res /\
    RepL m1 sh N lss (x <| hr := h |>);
  ri_frame: Mem.unchanged_on (HeurFrame sh) m m1;
}.
Arguments ReinsertInv : clear implicits.

(* reinsert inserts the atoms of the trail from position q - 1 down to j into the heap.
   Writing res for reinsert (hr x) (tr x) N j q0 (q0 - j), for the q0 of the call:

     {{ RepL m sh N lss x /\ j <= q0 <= tlen x }}
       (q = q0)
     {{ ReinsertInv res q0 }}
       while (q > j) {
     {{ ReinsertInv res q /\ q > j }}
         heap_insert(s, s->tr[q - 1] >> 1);                         (heap_insert_correct)
         q--;
     {{ ReinsertInv res (q - 1) }}                                     (reinsert_last)
       }
     {{ ReinsertInv res j: the heuristic is res }}

   The loop ends: q decreases. *)
Lemma reinsert_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (j q: nat),
  {{ m | RepL m sh N lss x /\ (j <= q <= tlen x)%nat }}
    f_reinsert(sptr sh, vnat j, vnat q)
  {{ m', v | HeurPost sh N lss x m (reinsert (hr x) (tr x) N j q (q - j)) m' }}.
Proof.
  intros sh N lss x j q0 m [HRep Hq0].
  pose proof (r_n HRep) as HN.
  pose proof (r_tlen_le HRep) as Ht.
  set (res := reinsert (hr x) (tr x) N j q0 (q0 - j)).
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_reinsert. cbn [fn_body fn_return]. unfold Swhile.
    apply exec_loop with (R := Peano.lt)
      (I := @ReinsertInv m sh N lss x j res) (a := q0).
    + apply lt_wf.
    + intros q le1 m1 HI. destruct HI as [Hs Hj Hq Hjq (h & Hres & HRep1) Hframe].
      pose proof (r_nodup HRep1) as Hnd.
      pose proof (r_tr_atoms HRep1) as Hatoms.
      pose proof (r_tr HRep1) as Ftr.
      pose proof (a_tr HRep1) as Atr.
      cbn [set_hr tr tlen] in Hatoms, Atr.
      apply exec_seq.
      (* if (q > j) ... else break; *)
      branch.
      * (* q > j: insert the atom at q - 1 *)
        intros Hgt.
        assert (Hsub: Int.sub (Int.repr (Z.of_nat q)) (Int.repr 1)
                      = Int.repr (Z.of_nat (q - 1))).
        { rewrite sub_repr. f_equal. lia. }
        assert (Hl: (extract (tget (tr x) (q - 1)) < N)%nat).
        { apply Hatoms. lia. }
        pose proof (key_small _ N Hl HN) as Hkey.
        assert (Hshr: Int.shr (Int.repr (key (tget (tr x) (q - 1)))) (Int.repr 1)
                      = Int.repr (Z.of_nat (extract (tget (tr x) (q - 1))))).
        { apply shr_key. lia. }
        (* heap_insert(s, s->tr[q - 1] >> 1); *)
        run.
        eapply (exec_call_triple_none heap_insert_fun
                  (heap_insert_correct sh N lss (x <| hr := h |>)
                     (extract (tget (tr x) (q - 1))))).
        -- reflexivity.
        -- unfold vint. rewrite <- Hshr. evs.
        -- split; assumption.
        -- intros m2 v2 [HRep2 Hun2]. normal. keep_mem m2.
           (* q--; and the loop goes on *)
           run. ints. apply loopk_next with (q - 1)%nat.
           ++ lia.
           ++ constructor.
              ** tmp.
              ** tmp.
              ** tmp.
              ** lia.
              ** exists (heap_insert h N (extract (tget (tr x) (q - 1)))). split.
                 --- rewrite reinsert_last by lia. assumption.
                 --- apply HRep2.
              ** frame.
      * (* q <= j, so q = j: break; the heuristic is res *)
        intros Hle. apply exec_break. abrupt. apply loopk_break. return_none.
        replace (q - j)%nat with 0%nat in Hres by lia. cbn [reinsert] in Hres.
        rewrite <- Hres. split.
        -- apply HRep1.
        -- assumption.
    + (* The invariant holds at q0. *)
      constructor.
      * tmp.
      * tmp.
      * tmp.
      * lia.
      * exists (hr x). split.
        -- reflexivity.
        -- destruct x. apply HRep.
      * frame.
Qed.

Lemma reinsert_fun: FunAt _reinsert f_reinsert.
Proof. apply find_fun. reflexivity. Qed.
