(* unmark_range unmarks the negations of the trail literals in a range of positions
   (unmark_range). *)
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
From RocqSAT.refinement Require Import Tactics.
From RocqSAT.refinement Require Import Table.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement Require Import Analysis.
From RocqSAT.refinement.c Require Import Arrays.
From RocqSAT.refinement.c Require Import Logic.
From RocqSAT.refinement.c Require Import Common.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Rep.
From RocqSAT.refinement.c Require Import RepReasons.

(* One step of the model: unmarking from idx > lo down to lo unmarks the negation of
   the literal at idx - 1 first. *)
Lemma unmark_range_step: forall (y: Ctx) (idx lo: nat), (lo < idx)%nat ->
  unmark_range y idx lo
  = unmark_range (y <| mrk := tset (mrk y) (lit_key (¬tget (tr y) (idx - 1))) false |>)
      (idx - 1) lo.
Proof.
  intros y idx lo Hlt. unfold unmark_range.
  replace (idx - lo)%nat with (S (idx - 1 - lo)) by lia. reflexivity.
Qed.

(* The invariant of the loop of unmark_range at idx: the memory holds a context y that,
   unmarked from idx down to lo, gives res, and only the marks changed since m. *)
Record UnmarkRangeInv {sh: Shape} {N: nat} {lss: list (list Lit)}
  {lo: nat} {res: Ctx} {m: mem} {idx: nat} {le: temp_env}
  {m1: mem}: Prop := {
  um_s: le ! _s = Some (sptr sh);
  um_idx: le ! _idx = Some (vnat idx);
  um_lo: le ! _lo = Some (vnat lo);
  um_ctx: exists (y: Ctx),
    (idx <= tlen y)%nat /\ unmark_range y idx lo = res /\ RepL m1 sh N lss y;
  um_unchanged: Mem.unchanged_on (AllBut (b_mrk sh)) m m1;
}.
Arguments UnmarkRangeInv : clear implicits.

(* unmark_range moves idx down to lo and unmarks the negation of each literal it passes.
   Writing res for the model, unmark_range x idx lo, and l for the literal at idx - 1
   of the current context y:

     {{ RepL m sh N lss x /\ idx <= tlen x /\ lo <= N }}
     {{ UnmarkRangeInv res idx }}
       while (idx > lo) {
     {{ UnmarkRangeInv res idx /\ idx > lo: the context is y }}
         s->mrk[s->tr[idx - 1] ^ 1] = 0;                                  (rep_store_mrk)
     {{ the context is y <| mrk := tset (mrk y) (lit_key (¬l)) false |> }}
         idx--;
     {{ UnmarkRangeInv res (idx - 1) }}
       }
     {{ UnmarkRangeInv res idx /\ idx <= lo: the context is res }}

   The loop ends: idx decreases. *)
Lemma unmark_range_correct: forall (sh: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (idx lo: nat),
  {{ m | RepL m sh N lss x /\ (idx <= tlen x)%nat /\ (lo <= N)%nat }}
    f_unmark_range(sptr sh, vnat idx, vnat lo)
  {{ m', v | Changes sh N lss (AllBut (b_mrk sh)) (unmark_range x idx lo) m m' }}.
Proof.
  intros sh N lss x idx lo m (HRep & Hidx & Hlo).
  pose proof (r_n HRep) as HN.
  remember (unmark_range x idx lo) as res eqn:Hres.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_unmark_range. cbn [fn_body fn_return]. unfold Swhile.
    apply exec_loop with (R := Peano.lt) (I := UnmarkRangeInv sh N lss lo res m)
      (a := idx).
    + apply lt_wf.
    + intros i le1 m1 HI.
      destruct HI as [Hs Hi Hlo' (y & Hile & Hy & HRep1) Hun1].
      pose proof (r_nodup HRep1) as Hnd.
      pose proof (r_tlen_le HRep1) as Htle.
      apply exec_seq.
      (* if (idx > lo) ... else break; *)
      branch.
      * (* idx > lo: unmark the negation of the literal l at idx - 1 *)
        intros Hgt.
        rewrite unmark_range_step in Hy by lia.
        assert (Hsub: Int.sub (Int.repr (Z.of_nat i)) (Int.repr 1)
                      = Int.repr (Z.of_nat (i - 1))).
        { rewrite sub_repr. f_equal. lia. }
        assert (Hl: (extract (tget (tr y) (i - 1)) < N)%nat).
        { apply (r_tr_atoms HRep1). lia. }
        pose proof (key_small _ N Hl HN) as Hkl.
        assert (Hxor: Int.xor (Int.repr (key (tget (tr y) (i - 1)))) (Int.repr 1)
                      = Int.repr (key (¬tget (tr y) (i - 1)))).
        { apply xor_key. lia. }
        assert (Hnegl: (lit_key (¬tget (tr y) (i - 1)) < 2 * N)%nat).
        { apply lit_key_lt. now destruct (tget (tr y) (i - 1)). }
        pose proof (r_mrk HRep1) as Fmrk.
        pose proof (r_tr HRep1) as Ftr.
        pose proof (a_tr HRep1) as Atr.
        pose proof (a_mrk HRep1) as Amrk.
        (* s->mrk[s->tr[idx - 1] ^ 1] = 0; *)
        apply exec_skip. normal. run.
        cbv beta. set (l := tget (tr y) (i - 1)) in *.
        store Amrk Hnegl as m2 Hst2.
        pose proof (rep_store_mrk m1 m2
                      (lit_key (¬l)) false HRep1 Hnegl Hst2) as HRep2.
        (* idx--; and the loop goes on *)
        run. ints. apply loopk_next with (i - 1)%nat.
        -- lia.
        -- constructor.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ exists (y <| mrk := tset (mrk y) (lit_key (¬l)) false |>). splits.
              ** cbn [set_mrk tlen]. lia.
              ** assumption.
              ** apply HRep2.
           ++ frame.
      * (* idx <= lo: break; the context is res *)
        intros Hle. apply exec_break. abrupt. apply loopk_break.
        return_none.
        split.
        -- (* nothing is left to unmark: y is res *)
           assert (Hyres: unmark_range y i lo = y).
           { unfold unmark_range. replace (i - lo)%nat with 0%nat by lia.
             destruct y. reflexivity. }
           rewrite <- Hy, Hyres. apply HRep1.
        -- assumption.
    + (* The invariant holds at idx, with the context x. *)
      constructor.
      * tmp.
      * tmp.
      * tmp.
      * exists x. splits.
        -- assumption.
        -- symmetry. assumption.
        -- apply HRep.
      * frame.
Qed.

Lemma unmark_range_fun: FunAt _unmark_range f_unmark_range.
Proof. apply find_fun. reflexivity. Qed.
