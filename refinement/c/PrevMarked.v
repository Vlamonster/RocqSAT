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

(* The invariant of the loop of prev_marked at idx, for the memory m of the call: the
   temporaries hold s, idx and lo, idx is within the trail, the memory is still m, and
   the result res of the model is what prev_marked gives from idx down to lo (the loop
   follows the recursion of the model). *)
Record PrevInv (m: mem) (S: Shape) (x: Ctx) (lo res idx: nat) (le: temp_env) (m1: mem):
  Prop := {
  pv_s: le ! _s = Some (sptr S);
  pv_idx: le ! _idx = Some (vint (Z.of_nat idx));
  pv_lo: le ! _lo = Some (vint (Z.of_nat lo));
  pv_mem: m1 = m;
  pv_le: (idx <= tlen x)%nat;
  pv_res: res = prev_marked (tr x) (mrk x) lo idx (idx - lo);
}.

(* prev_marked moves idx down to lo, and stops early after the first position whose
   literal has its negation marked. It stores nothing. Writing res for the model,
   prev_marked (tr x) (mrk x) lo idx (idx - lo), and l for the literal at idx - 1:

     {{ RepL m S N lss x lims lt /\ idx <= tlen x /\ lo <= N }}
     {{ PrevInv m S x lo res idx }}
       while (idx > lo) {
     {{ PrevInv m S x lo res idx /\ idx > lo }}
         if (s->mrk[s->tr[idx - 1] ^ 1]) return idx;
     {{ result = idx = res, as ¬l is marked }}
     {{ PrevInv m S x lo res idx /\ ¬l is not marked }}
         idx--;
     {{ PrevInv m S x lo res (idx - 1) }}
       }
     {{ PrevInv m S x lo res idx /\ idx <= lo }}
       return idx;
     {{ result = idx = res, as there is nothing left to look at }}

   The loop ends: idx decreases. *)
Lemma prev_marked_correct {lt: list Lit}: forall (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (idx lo: nat),
  {{ m | RepL m S N lss x lims lt /\ (idx <= tlen x)%nat /\ (lo <= N)%nat }}
    f_prev_marked(sptr S, vint (Z.of_nat idx), vint (Z.of_nat lo))
  {{ m', v | m' = m /\
             v = vint (Z.of_nat (prev_marked (tr x) (mrk x) lo idx (idx - lo))) }}.
Proof.
  intros S N lss x lims idx lo m (HRep & Hidx & Hlo).
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_tlen_le _ _ _ _ _ _ _ HRep) as Htle.
  remember (prev_marked (tr x) (mrk x) lo idx (idx - lo)) as res eqn:Hres.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_prev_marked. cbn [fn_body fn_return].
    pose proof HRep as HRep'. destruct HRep'. unpack.
    run. unfold Swhile.
    apply exec_loop with (R := Peano.lt) (I := PrevInv m S x lo res) (a := idx).
    + apply lt_wf.
    + intros i le1 m1 HI. destruct HI as [Hs Hi Hlo' -> Hile Hprev]. apply exec_seq.
      (* if (idx > lo) ... else break; *)
      eapply (exec_if_cmp _ _ _ Cgt).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * destruct (Nat.le_gt_cases i lo) as [Hle | Hgt].
        -- (* idx <= lo: break; return idx, which is res *)
           replace (zcmp Cgt (Z.of_nat i) (Z.of_nat lo)) with false
             by (simpl; symmetry; apply Z.ltb_ge; lia).
           cbv beta iota. apply exec_break. abrupt. apply loopk_break. normal.
           eapply exec_return.
           ++ ev.
           ++ exists (vint (Z.of_nat i)). split.
              ** apply result_int.
              ** split.
                 --- reflexivity.
                 --- replace (i - lo)%nat with 0%nat in Hprev by lia.
                     now rewrite Hprev.
        -- (* idx > lo: the model looks at the literal l at idx - 1 *)
           replace (zcmp Cgt (Z.of_nat i) (Z.of_nat lo)) with true
             by (simpl; symmetry; apply Z.ltb_lt; lia).
           replace (i - lo)%nat with (Datatypes.S (i - 1 - lo)) in Hprev by lia.
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
           cbv beta iota. apply exec_skip. normal. run.
           cbv beta. set (l := tget (tr x) (i - 1)) in *.
           eapply (exec_if_int _ _ _ _ (enc_mark (tget (mrk x) (lit_key (¬l))))).
           ++ ev.
           ++ reflexivity.
           ++ unfold Small, enc_mark. destruct (tget (mrk x) (lit_key (¬l))); lia.
           ++ unfold enc_mark.
              destruct (tget (mrk x) (lit_key (¬l))); cbn [Z.eqb negb].
              ** (* ¬l is marked: return idx, which is res *)
                 eapply exec_return.
                 --- ev.
                 --- ret. exists (vint (Z.of_nat i)). split.
                     +++ apply result_int.
                     +++ split.
                         *** reflexivity.
                         *** now rewrite Hprev.
              ** (* ¬l is not marked: idx--; and the loop goes on *)
                 apply exec_skip. normal. run. ints. apply loopk_next with (i - 1)%nat.
                 --- lia.
                 --- constructor.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
                     +++ reflexivity.
                     +++ lia.
                     +++ assumption.
    + (* The invariant holds at idx. *)
      constructor.
      * tmp.
      * tmp.
      * tmp.
      * reflexivity.
      * assumption.
      * assumption.
Qed.

Lemma prev_marked_fun: exists (b: block),
  Genv.find_symbol ge _prev_marked = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_prev_marked).
Proof. apply find_fun. reflexivity. Qed.
