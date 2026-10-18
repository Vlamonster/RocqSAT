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
Record SkipInv {m: mem} {sh: Shape} {x: Ctx} {res c: nat} {le: temp_env} {m1: mem}:
  Prop := {
  si_s: le ! _s = Some (sptr sh);
  si_c: le ! _c = Some (vnat c);
  si_n: le ! _n = Some (vnat (nlits x));
  si_mem: m1 = m;
  si_range: (cur x <= c <= nlits x)%nat;
  si_res: res = skip_from (vals x) (alls x) (nlits x) (nlits x - c) c;
}.
Arguments SkipInv : clear implicits.

(* skip_from moves c from the cursor to the first unassigned literal of alls, or to its
   end. It stores nothing. Writing res for the model,
   skip_from (vals x) (alls x) (nlits x) (nlits x - cur x) (cur x):

     {{ RepL m sh N lss x }}
       int c = s->cur;
       int n = s->nlits;
     {{ SkipInv m sh x res (cur x) }}
       while (c < n) {
     {{ SkipInv m sh x res c /\ c < n }}
         if (lit_value(s, s->alls[c]) == 0) return c;
     {{ result = c = res, as the literal at c is unassigned }}
     {{ SkipInv m sh x res c /\ the literal at c is assigned }}
         c++;
     {{ SkipInv m sh x res (c + 1) }}
       }
     {{ SkipInv m sh x res c /\ c >= n }}
       return c;
     {{ result = c = res, as c = n }}

   The loop ends: nlits x - c decreases. *)
Lemma skip_from_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx),
  {{ m | RepL m sh N lss x }}
    f_skip_from(sptr sh)
  {{ m', v | m' = m /\
             v = vnat (next_undef x) }}.
Proof.
  intros sh N lss x m HRep. pose proof (r_n HRep) as HN.
  unfold next_undef.
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
      (I := SkipInv m sh x res) (a := cur x).
    + apply well_founded_ltof.
    + intros c le1 m1 HI. destruct HI as [Hs Hc Hn -> Hcrange Hskip]. apply exec_seq.
      (* if (c < n) ... else break; *)
      eapply exec_if_lt.
      * ev.
      * ev.
      * reflexivity.
      * lia.
      * (* c < n: the model looks at the literal at c *)
        intros Hlt.
        assert (Hl: (extract (tget (alls x) c) < N)%nat).
        { apply r_alls_atoms. lia. }
        pose proof (key_small _ N Hl HN) as Hkl.
        assert (Hadd: Int.add (Int.repr (Z.of_nat c)) (Int.repr 1)
                      = Int.repr (Z.of_nat (S c))).
        { rewrite add_repr by lia. f_equal. lia. }
        replace (nlits x - c)%nat with (S (nlits x - S c))
          in Hskip by lia.
        cbn [skip_from] in Hskip.
        replace (c <? nlits x)%nat with true in Hskip
          by (symmetry; apply Nat.ltb_lt; lia).
        (* lit_value(s, s->alls[c]) *)
        run. rewrite (Hta c) by lia.
        eapply (exec_call_triple lit_value_fun
                  (lit_value_correct sh N lss x (tget (alls x) c))).
        -- reflexivity.
        -- evs.
        -- split.
           ++ assumption.
           ++ assumption.
        -- intros m' v [-> ->]. normal.
           (* if (... == 0) return c; *)
           eapply (exec_if_eq _ 0).
           ++ ev.
           ++ ev.
           ++ reflexivity.
           ++ pose proof (enc_small (lookup (vals x) (tget (alls x) c))). lia.
           ++ (* unassigned: return c, which is res *)
              intros Hzero.
              assert (Hu: lookup_undef (vals x) (tget (alls x) c) = true).
              { rewrite <- enc_undef. now apply Z.eqb_eq. }
              rewrite Hu in Hskip. cbn [negb andb] in Hskip.
              eapply exec_return.
              ** ev.
              ** ret. exists (vnat c). split.
                 --- apply result_int.
                 --- split.
                     +++ reflexivity.
                     +++ now rewrite Hskip.
           ++ (* assigned: c++; and the loop goes on *)
              intros Hnonzero.
              assert (Hu: lookup_undef (vals x) (tget (alls x) c) = false).
              { rewrite <- enc_undef. now apply Z.eqb_neq. }
              rewrite Hu in Hskip. cbn [negb andb] in Hskip.
              run. ints. apply loopk_next with (S c).
              ** unfold ltof. lia.
              ** constructor.
                 --- tmp.
                 --- tmp.
                 --- tmp.
                 --- reflexivity.
                 --- lia.
                 --- assumption.
      * (* c >= n: break; return c, which is res *)
        intros Hge. apply exec_break. abrupt. apply loopk_break. normal.
        eapply exec_return.
        -- ev.
        -- exists (vnat c). split.
           ++ apply result_int.
           ++ split.
              ** reflexivity.
              ** replace (nlits x - c)%nat with 0%nat in Hskip by lia.
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

Lemma skip_from_fun: FunAt _skip_from f_skip_from.
Proof. apply find_fun. reflexivity. Qed.
