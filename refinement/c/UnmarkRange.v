(* unmark_range unmarks the negations of the trail literals in a range of positions
   (unmark_range). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Propagate Analysis.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep.
Import ListNotations.

(* The invariant of the loop of unmark_range at idx, for the memory m of the call: the
   temporaries hold s, idx and lo, idx is within the trail, the memory represents x with
   marks mk that, unmarked from idx down to lo, give the marks res of the model, and only
   the marks have changed since m. *)
Record UnmarkInv (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx) (lims: list nat)
  (lt: list Lit) (lo: nat) (res: Table bool) (m: mem) (idx: nat) (le: temp_env)
  (m1: mem): Prop := {
  um_s: le ! _s = Some (sptr S);
  um_idx: le ! _idx = Some (vint (Z.of_nat idx));
  um_lo: le ! _lo = Some (vint (Z.of_nat lo));
  um_le: (idx <= tlen x)%nat;
  um_mrk: exists (mk: Table bool),
    unmark_range (tr x) mk idx (idx - lo) = res /\
    RepL m1 S N lss (set_mrk x mk) lims lt;
  um_unchanged: Mem.unchanged_on (fun (b: block) (_: Z) => b <> b_mrk S) m m1;
}.

(* unmark_range moves idx down to lo and unmarks the negation of each literal it passes.
   Writing res for the model, unmark_range (tr x) (mrk x) idx (idx - lo), and l for the
   literal at idx - 1:

     {{ RepL m S N lss x lims lt /\ idx <= tlen x /\ lo <= N }}
     {{ UnmarkInv res idx }}
       while (idx > lo) {
     {{ UnmarkInv res idx /\ idx > lo: the marks are mk }}
         s->mrk[s->tr[idx - 1] ^ 1] = 0;                                  (rep_store_mrk)
     {{ the marks are tset mk (lit_key (¬l)) false }}
         idx--;
     {{ UnmarkInv res (idx - 1) }}
       }
     {{ UnmarkInv res idx /\ idx <= lo: the marks are res }}

   The loop ends: idx decreases. *)
Lemma unmark_range_correct {lt: list Lit}: forall (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (idx lo: nat),
  {{ m | RepL m S N lss x lims lt /\ (idx <= tlen x)%nat /\ (lo <= N)%nat }}
    f_unmark_range(sptr S, vint (Z.of_nat idx), vint (Z.of_nat lo))
  {{ m', v | RepL m' S N lss (set_mrk x (unmark_range (tr x) (mrk x) idx (idx - lo)))
               lims lt /\
             Mem.unchanged_on (fun (b: block) (_: Z) => b <> b_mrk S) m m' }}.
Proof.
  intros S N lss x lims idx lo m (HRep & Hidx & Hlo).
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_tlen_le _ _ _ _ _ _ _ HRep) as Htle.
  remember (unmark_range (tr x) (mrk x) idx (idx - lo)) as res eqn:Hres.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_unmark_range. cbn [fn_body fn_return]. unfold Swhile.
    apply exec_loop with (R := Peano.lt) (I := UnmarkInv S N lss x lims lt lo res m)
      (a := idx).
    + apply lt_wf.
    + intros i le1 m1 HI.
      destruct HI as [Hs Hi Hlo' Hile (mk & Hmk & HRep1) Hun1].
      pose proof (r_nodup _ _ _ _ _ _ _ HRep1) as Hnd.
      apply exec_seq.
      (* if (idx > lo) ... else break; *)
      eapply (exec_if_cmp _ _ _ Cgt).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * destruct (Nat.le_gt_cases i lo) as [Hle | Hgt].
        -- (* idx <= lo: break; the marks are res *)
           replace (zcmp Cgt (Z.of_nat i) (Z.of_nat lo)) with false
             by (simpl; symmetry; apply Z.ltb_ge; lia).
           cbv beta iota. apply exec_break. abrupt. apply loopk_break.
           exists Vundef. split.
           ++ reflexivity.
           ++ split.
              ** replace (i - lo)%nat with 0%nat in Hmk by lia.
                 cbn [unmark_range] in Hmk.
                 rewrite <- Hmk. apply HRep1.
              ** assumption.
        -- (* idx > lo: unmark the negation of the literal l at idx - 1 *)
           replace (zcmp Cgt (Z.of_nat i) (Z.of_nat lo)) with true
             by (simpl; symmetry; apply Z.ltb_lt; lia).
           replace (i - lo)%nat with (Datatypes.S (i - 1 - lo)) in Hmk by lia.
           cbn [unmark_range] in Hmk.
           assert (Hsub: Int.sub (Int.repr (Z.of_nat i)) (Int.repr 1)
                         = Int.repr (Z.of_nat (i - 1))).
           { rewrite sub_repr. f_equal. lia. }
           assert (Hl: (extract (tget (tr x) (i - 1)) < N)%nat).
           { apply (r_tr_atoms _ _ _ _ _ _ _ HRep1). cbn [set_mrk tlen]. lia. }
           pose proof (key_small _ N Hl HN) as Hkl.
           assert (Hxor: Int.xor (Int.repr (key (tget (tr x) (i - 1)))) (Int.repr 1)
                         = Int.repr (key (¬tget (tr x) (i - 1)))).
           { apply xor_key. lia. }
           assert (Hnegl: (lit_key (¬tget (tr x) (i - 1)) < 2 * N)%nat).
           { apply lit_key_lt. now destruct (tget (tr x) (i - 1)). }
           pose proof (r_mrk _ _ _ _ _ _ _ HRep1) as Fmrk.
           pose proof (r_tr _ _ _ _ _ _ _ HRep1) as Ftr.
           pose proof (a_tr _ _ _ _ _ _ _ HRep1) as Atr. cbn [set_mrk tr] in Atr.
           pose proof (a_mrk _ _ _ _ _ _ _ HRep1) as Amrk.
           (* s->mrk[s->tr[idx - 1] ^ 1] = 0; *)
           cbv beta iota. apply exec_skip. normal. run.
           cbv beta. set (l := tget (tr x) (i - 1)) in *.
           eapply exec_store.
           ++ evl.
           ++ ev.
           ++ reflexivity.
           ++ reflexivity.
           ++ ofs. bound.
           ++ ofs. cbn [cast_int_int].
              destruct (arr_storable m1 (b_mrk S) (2 * N) (lit_key (¬l)) _
                          (enc_mark false) Amrk Hnegl) as [m2 Hst2].
              exists m2. split.
              ** apply Hst2.
              ** normal.
                 pose proof (rep_store_mrk m1 m2 S N lss (set_mrk x mk) lims
                               (lit_key (¬l)) false HRep1 Hnegl Hst2) as HRep2.
                 (* idx--; and the loop goes on *)
                 run. ints. apply loopk_next with (i - 1)%nat.
                 --- lia.
                 --- constructor.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
                     +++ lia.
                     +++ exists (tset mk (lit_key (¬l)) false). split.
                         *** assumption.
                         *** apply HRep2.
                     +++ apply (store_unchanged _ _ _ _ _ _ _ _ Hun1 Hst2).
                         intros ofs Hne. apply Hne. reflexivity.
    + (* The invariant holds at idx, with the marks of x. *)
      constructor.
      * tmp.
      * tmp.
      * tmp.
      * assumption.
      * exists (mrk x). split.
        -- symmetry. assumption.
        -- destruct x. apply HRep.
      * apply Mem.unchanged_on_refl.
Qed.

Lemma unmark_range_fun: exists (b: block),
  Genv.find_symbol ge _unmark_range = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_unmark_range).
Proof. apply find_fun. reflexivity. Qed.
