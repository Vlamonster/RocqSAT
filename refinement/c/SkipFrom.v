(* skip_from finds the first position from the cursor on whose literal is unassigned
   (skip_from). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Propagate Step.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep LitValue.
Import ListNotations.

(* The invariant of the loop of skip_from at position c, for the memory m of the call:
   the temporaries hold s, c and n = nlits x, c is between the cursor and n, the memory
   is still m, and the result res of the model is what skip_from gives from c on (the
   loop follows the recursion of the model). *)
Record SkipInv (m: mem) (S: Shape) (x: Ctx) (res c: nat) (le: temp_env) (m1: mem):
  Prop := {
  si_s: le ! _s = Some (sptr S);
  si_c: le ! _c = Some (vint (Z.of_nat c));
  si_n: le ! _n = Some (vint (Z.of_nat (nlits x)));
  si_mem: m1 = m;
  si_range: (cur x <= c <= nlits x)%nat;
  si_res: res = skip_from (vals x) (alls x) (nlits x) (nlits x - c) c;
}.

(* skip_from moves c from the cursor to the first unassigned literal of alls, or to its
   end. It stores nothing. Writing res for the model,
   skip_from (vals x) (alls x) (nlits x) (nlits x - cur x) (cur x):

     {{ RepB m S N lss x lims }}
       int c = s->cur;
       int n = s->nlits;
     {{ SkipInv m S x res (cur x) }}
       while (c < n) {
     {{ SkipInv m S x res c /\ c < n }}
         if (lit_value(s, s->alls[c]) == 0) return c;
     {{ result = c = res, as the literal at c is unassigned }}
     {{ SkipInv m S x res c /\ the literal at c is assigned }}
         c++;
     {{ SkipInv m S x res (c + 1) }}
       }
     {{ SkipInv m S x res c /\ c >= n }}
       return c;
     {{ result = c = res, as c = n }}

   The loop ends: nlits x - c decreases. *)
Lemma skip_from_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat),
  {{ m | RepB m S N lss x lims }}
    f_skip_from(sptr S)
  {{ m', v | m' = m /\
             v = vint (Z.of_nat (skip_from (vals x) (alls x) (nlits x) (nlits x - cur x)
                                           (cur x))) }}.
Proof.
  intros S N lss x lims m HRep. pose proof (r_n _ _ _ _ _ _ HRep) as HN.
  remember (skip_from (vals x) (alls x) (nlits x) (nlits x - cur x) (cur x))
    as res eqn:Hres.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_skip_from. cbn [fn_body fn_return].
    pose proof HRep as HRep'. destruct HRep'.
    destruct a_alls as (ta & Aalls & Hta). unpack.
    (* int c = s->cur; int n = s->nlits; *)
    run. unfold Swhile.
    apply exec_loop with (R := ltof nat (fun (c: nat) => nlits x - c)%nat)
      (I := SkipInv m S x res) (a := cur x).
    + apply well_founded_ltof.
    + intros c le1 m1 HI. destruct HI as [Hs Hc Hn -> Hcrange Hskip]. apply exec_seq.
      (* if (c < n) ... else break; *)
      eapply (exec_if_cmp _ _ _ Clt).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * destruct (Nat.lt_ge_cases c (nlits x)) as [Hlt | Hge].
        -- (* c < n: the model looks at the literal at c *)
           replace (zcmp Clt (Z.of_nat c) (Z.of_nat (nlits x))) with true
             by (simpl; symmetry; apply Z.ltb_lt; lia).
           assert (Hl: (extract (tget (alls x) c) < N)%nat).
           { apply r_alls_atoms. lia. }
           pose proof (key_small _ N Hl HN) as Hkl.
           assert (Hadd: Int.add (Int.repr (Z.of_nat c)) (Int.repr 1)
                         = Int.repr (Z.of_nat (Datatypes.S c))).
           { rewrite add_repr by lia. f_equal. lia. }
           replace (nlits x - c)%nat with (Datatypes.S (nlits x - Datatypes.S c))
             in Hskip by lia.
           cbn [skip_from] in Hskip.
           replace (c <? nlits x)%nat with true in Hskip
             by (symmetry; now apply Nat.ltb_lt).
           (* lit_value(s, s->alls[c]) *)
           cbv beta iota. run. rewrite (Hta c) by lia. call lit_value_fun.
           eapply call_weaken.
           { apply (lit_value_correct S N lss x lims (tget (alls x) c) m).
             split; assumption. }
           intros m' v [-> ->]. normal.
           (* if (... == 0) return c; *)
           eapply (exec_if_cmp _ _ _ Ceq _ _ _ 0).
           ++ ev.
           ++ ev.
           ++ reflexivity.
           ++ reflexivity.
           ++ apply enc_small.
           ++ unfold Small. lia.
           ++ cbn [zcmp]. rewrite enc_undef.
              destruct (lookup_undef (vals x) (tget (alls x) c)) eqn:Hu;
                cbn [negb andb] in Hskip.
              ** (* unassigned: return c, which is res *)
                 cbv beta iota. eapply exec_return.
                 --- ev.
                 --- ret. exists (vint (Z.of_nat c)). split.
                     +++ apply result_int.
                     +++ split.
                         *** reflexivity.
                         *** now rewrite Hskip.
              ** (* assigned: c++; and the loop goes on *)
                 cbv beta iota. run. ints. apply loopk_next with (Datatypes.S c).
                 --- unfold ltof. lia.
                 --- constructor.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
                     +++ reflexivity.
                     +++ lia.
                     +++ assumption.
        -- (* c >= n: break; return c, which is res *)
           replace (zcmp Clt (Z.of_nat c) (Z.of_nat (nlits x))) with false
             by (simpl; symmetry; apply Z.ltb_ge; lia).
           cbv beta iota. apply exec_break. abrupt. apply loopk_break. normal.
           eapply exec_return.
           ++ ev.
           ++ exists (vint (Z.of_nat c)). split.
              ** apply result_int.
              ** split.
                 --- reflexivity.
                 --- replace (nlits x - c)%nat with 0%nat in Hskip by lia.
                     now rewrite Hskip.
    + (* The invariant holds at the cursor. *)
      constructor.
      * tmp.
      * tmp.
      * tmp.
      * reflexivity.
      * lia.
      * assumption.
Qed.

Lemma skip_from_fun: exists (b: block),
  Genv.find_symbol ge _skip_from = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_skip_from).
Proof. apply find_fun. reflexivity. Qed.
