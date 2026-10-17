(* pop_reasons finds the number of reason clauses of the literals below a trail position
   (pop_reasons). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Propagate Analysis.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep.
Import ListNotations.

(* The invariant of the loop of pop_reasons at n, for the memory m of the call: the
   temporaries hold s, j and n, n is at most the number of reason clauses, the memory is
   still m, and the result res of the model is what pop_reasons gives for the first n
   (the loop follows the recursion of the model). *)
Record PopInv (m: mem) (S: Shape) (x: Ctx) (j res n: nat) (le: temp_env) (m1: mem):
  Prop := {
  pi_s: le ! _s = Some (sptr S);
  pi_j: le ! _j = Some (vint (Z.of_nat j));
  pi_n: le ! _n = Some (vint (Z.of_nat n));
  pi_mem: m1 = m;
  pi_le: (n <= nr x)%nat;
  pi_res: res = pop_reasons (rps x) j n;
}.

(* pop_reasons moves n down from the number of reason clauses to the first one whose
   newest clause asserted a literal below position j. It stores nothing. Writing res for
   the model, pop_reasons (rps x) j (nr x):

     {{ RepL m S N lss x lims lt /\ j <= N }}
       int n = s->nr;
     {{ PopInv m S x j res (nr x) }}
       while (n > 0) {
     {{ PopInv m S x j res n /\ n > 0 }}
         if (s->rpos[n - 1] < j) return n;
     {{ result = n = res, as clause n - 1 is below j }}
     {{ PopInv m S x j res n /\ clause n - 1 is not below j }}
         n--;
     {{ PopInv m S x j res (n - 1) }}
       }
     {{ PopInv m S x j res 0 }}
       return n;
     {{ result = 0 = res }}

   The loop ends: n decreases. *)
Lemma pop_reasons_correct {lt: list Lit}: forall (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (j: nat),
  {{ m | RepL m S N lss x lims lt /\ (j <= N)%nat }}
    f_pop_reasons(sptr S, vint (Z.of_nat j))
  {{ m', v | m' = m /\ v = vint (Z.of_nat (pop_reasons (rps x) j (nr x))) }}.
Proof.
  intros S N lss x lims j m [HRep Hj]. pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  remember (pop_reasons (rps x) j (nr x)) as res eqn:Hres.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_pop_reasons. cbn [fn_body fn_return].
    pose proof HRep as HRep'. destruct HRep'.
    destruct a_rpos as (tp & Arpos & Htp). unpack.
    (* int n = s->nr; *)
    run. unfold Swhile.
    apply exec_loop with (R := Peano.lt) (I := PopInv m S x j res) (a := nr x).
    + apply lt_wf.
    + intros n le1 m1 HI. destruct HI as [Hs Hj' Hn -> Hnle Hpop]. apply exec_seq.
      (* if (n > 0) ... else break; *)
      eapply (exec_if_cmp _ _ _ Cgt).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * destruct n as [|n].
        -- (* n = 0: break; return n, which is res *)
           replace (zcmp Cgt (Z.of_nat 0) 0) with false by reflexivity.
           cbv beta iota. apply exec_break. abrupt. apply loopk_break. normal.
           eapply exec_return.
           ++ ev.
           ++ exists (vint (Z.of_nat 0)). split.
              ** apply result_int.
              ** split.
                 --- reflexivity.
                 --- now rewrite Hpop.
        -- (* n > 0: the model looks at clause n - 1 *)
           replace (zcmp Cgt (Z.of_nat (Datatypes.S n)) 0) with true
             by (simpl; symmetry; apply Z.ltb_lt; lia).
           assert (Hsub: Int.sub (Int.repr (Z.of_nat (Datatypes.S n))) (Int.repr 1)
                         = Int.repr (Z.of_nat n)).
           { rewrite sub_repr. f_equal. lia. }
           assert (Hrps: (tget (rps x) n <= N)%nat) by (apply r_rps_le; lia).
           cbn [pop_reasons] in Hpop.
           (* s->rpos[n - 1] < j *)
           cbv beta iota. apply exec_skip. normal. run. rewrite (Htp n) by lia.
           eapply (exec_if_cmp _ _ _ Clt).
           ++ ev.
           ++ ev.
           ++ reflexivity.
           ++ reflexivity.
           ++ unfold Small. lia.
           ++ unfold Small. lia.
           ++ cbn [zcmp]. destruct (Nat.ltb_spec (tget (rps x) n) j) as [Hlt | Hge].
              ** (* below j: return n, which is res *)
                 replace (Z.of_nat (tget (rps x) n) <? Z.of_nat j) with true
                   by (symmetry; apply Z.ltb_lt; lia).
                 cbv beta iota. eapply exec_return.
                 --- ev.
                 --- ret. exists (vint (Z.of_nat (Datatypes.S n))). split.
                     +++ apply result_int.
                     +++ split.
                         *** reflexivity.
                         *** now rewrite Hpop.
              ** (* not below j: n--; and the loop goes on *)
                 replace (Z.of_nat (tget (rps x) n) <? Z.of_nat j) with false
                   by (symmetry; apply Z.ltb_ge; lia).
                 cbv beta iota. apply exec_skip. normal. run. ints.
                 apply loopk_next with n.
                 --- lia.
                 --- constructor.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
                     +++ reflexivity.
                     +++ lia.
                     +++ assumption.
    + (* The invariant holds at the number of reason clauses. *)
      constructor.
      * tmp.
      * tmp.
      * tmp.
      * reflexivity.
      * lia.
      * assumption.
Qed.

Lemma pop_reasons_fun: exists (b: block),
  Genv.find_symbol ge _pop_reasons = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_pop_reasons).
Proof. apply find_fun. reflexivity. Qed.
