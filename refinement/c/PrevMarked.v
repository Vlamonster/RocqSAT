(* prev_marked finds the position after the newest trail position below idx, from lo on,
   whose literal has its negation marked (prev_marked). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Propagate Analysis.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep.
Import ListNotations.

(* The position after the newest trail position below idx, from lo on, whose literal has
   its negation marked, or lo if there is none. *)
Abbreviation newest_marked x lo idx := (prev_marked (tr x) (mrk x) lo idx (idx - lo)).

(* The invariant of the loop of prev_marked at idx: the memory is still m, and the model
   from idx on gives res. *)
Record PrevInv {m: mem} {sh: Shape} {x: Ctx} {lo res idx: nat} {le: temp_env} {m1: mem}:
  Prop := {
  pv_s: le ! _s = Some (sptr sh);
  pv_idx: le ! _idx = Some (vnat idx);
  pv_lo: le ! _lo = Some (vnat lo);
  pv_mem: m1 = m;
  pv_le: (idx <= tlen x)%nat;
  pv_res: res = newest_marked x lo idx;
}.
Arguments PrevInv : clear implicits.

(* prev_marked moves idx down to lo, and stops early after the first position whose
   literal has its negation marked. It stores nothing. Writing res for
   newest_marked x lo idx and l for the literal at idx - 1:

     {{ RepL m sh N lss x /\ idx <= tlen x /\ lo <= N }}
     {{ PrevInv m sh x lo res idx }}
       while (idx > lo) {
     {{ PrevInv m sh x lo res idx /\ idx > lo }}
         if (s->mrk[s->tr[idx - 1] ^ 1]) return idx;
     {{ result = idx = res, as ¬l is marked }}
     {{ PrevInv m sh x lo res idx /\ ¬l is not marked }}
         idx--;
     {{ PrevInv m sh x lo res (idx - 1) }}
       }
     {{ PrevInv m sh x lo res idx /\ idx <= lo }}
       return idx;
     {{ result = idx = res, as there is nothing left to look at }}

   The loop ends: idx decreases. *)
Lemma prev_marked_correct: forall (sh: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (idx lo: nat),
  {{ m | RepL m sh N lss x /\ (idx <= tlen x)%nat /\ (lo <= N)%nat }}
    f_prev_marked(sptr sh, vnat idx, vnat lo)
  {{ m', v | m' = m /\ v = vnat (newest_marked x lo idx) }}.
Proof.
  intros sh N lss x idx lo m (HRep & Hidx & Hlo).
  pose proof (r_n HRep) as HN.
  pose proof (r_tlen_le HRep) as Htle.
  remember (newest_marked x lo idx) as res eqn:Hres.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_prev_marked. cbn [fn_body fn_return].
    pose proof HRep as HRep'. destruct HRep'. unpack.
    run. unfold Swhile.
    apply exec_loop with (R := Peano.lt) (I := PrevInv m sh x lo res) (a := idx).
    + apply lt_wf.
    + intros i le1 m1 HI. destruct HI as [Hs Hi Hlo' -> Hile Hprev]. apply exec_seq.
      (* if (idx > lo) ... else break; *)
      eapply exec_if_gt.
      * ev.
      * ev.
      * reflexivity.
      * lia.
      * (* idx > lo: the model looks at the literal l at idx - 1 *)
        intros Hgt.
        replace (i - lo)%nat with (S (i - 1 - lo)) in Hprev by lia.
        cbn [prev_marked] in Hprev.
        assert (Hsub: Int.sub (Int.repr (Z.of_nat i)) (Int.repr 1)
                      = Int.repr (Z.of_nat (i - 1))).
        { rewrite sub_repr. f_equal. lia. }
        assert (Hl: (extract (tget (tr x) (i - 1)) < N)%nat).
        { apply r_tr_atoms. lia. }
        pose proof (key_small _ N Hl HN) as Hkl.
        assert (Hxor: Int.xor (Int.repr (key (tget (tr x) (i - 1)))) (Int.repr 1)
                      = Int.repr (key (¬tget (tr x) (i - 1)))).
        { apply xor_key. lia. }
        assert (Hnegl: (lit_key (¬tget (tr x) (i - 1)) < 2 * N)%nat).
        { apply lit_key_lt. now destruct (tget (tr x) (i - 1)). }
        (* s->mrk[s->tr[idx - 1] ^ 1] *)
        apply exec_skip. normal. run.
        cbv beta. set (l := tget (tr x) (i - 1)) in *.
        eapply (exec_if_nonzero (enc_mark (tget (mrk x) (lit_key (¬l))))).
        -- ev.
        -- reflexivity.
        -- unfold enc_mark. destruct (tget (mrk x) (lit_key (¬l))); lia.
        -- (* ¬l is marked: return idx, which is res *)
           intros Hmarked. unfold enc_mark in Hmarked.
           destruct (tget (mrk x) (lit_key (¬l))).
           ++ eapply exec_return.
              ** ev.
              ** ret. exists (vnat i). split.
                 --- apply result_int.
                 --- split.
                     +++ reflexivity.
                     +++ now rewrite Hprev.
           ++ lia.
        -- (* ¬l is not marked: idx--; and the loop goes on *)
           intros Hunmarked. unfold enc_mark in Hunmarked.
           destruct (tget (mrk x) (lit_key (¬l))).
           ++ lia.
           ++ apply exec_skip. normal. run. ints. apply loopk_next with (i - 1)%nat.
              ** lia.
              ** constructor.
                 --- tmp.
                 --- tmp.
                 --- tmp.
                 --- reflexivity.
                 --- lia.
                 --- assumption.
      * (* idx <= lo: break; return idx, which is res *)
        intros Hle. apply exec_break. abrupt. apply loopk_break. normal.
        eapply exec_return.
        -- ev.
        -- exists (vnat i). split.
           ++ apply result_int.
           ++ split.
              ** reflexivity.
              ** replace (i - lo)%nat with 0%nat in Hprev by lia.
                 now rewrite Hprev.
    + (* The invariant holds at idx. *)
      constructor.
      * tmp.
      * tmp.
      * tmp.
      * reflexivity.
      * assumption.
      * assumption.
Qed.

Lemma prev_marked_fun: FunAt _prev_marked f_prev_marked.
Proof. apply find_fun. reflexivity. Qed.
