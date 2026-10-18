(* pop_reasons finds the number of reason clauses of the literals below a trail position
   (pop_reasons). *)
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
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement Require Import Analysis.
From RocqSAT.refinement.c Require Import Arrays.
From RocqSAT.refinement.c Require Import Logic.
From RocqSAT.refinement.c Require Import Common.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Rep.

(* The invariant of the loop of pop_reasons at n: the memory is still m, and the model
   for the first n clauses gives res. *)
Record PopInv {m: mem} {sh: Shape} {x: Ctx} {j res n: nat} {le: temp_env} {m1: mem}:
  Prop := {
  pi_s: le ! _s = Some (sptr sh);
  pi_j: le ! _j = Some (vnat j);
  pi_n: le ! _n = Some (vnat n);
  pi_mem: m1 = m;
  pi_le: (n <= nr x)%nat;
  pi_res: res = pop_reasons (rps x) j n;
}.
Arguments PopInv : clear implicits.

(* pop_reasons moves n down from the number of reason clauses to the first one whose
   newest clause asserted a literal below position j. It stores nothing. Writing res for
   the model, pop_reasons (rps x) j (nr x):

     {{ RepL m sh N lss x /\ j <= N }}
       int n = s->nr;
     {{ PopInv m sh x j res (nr x) }}
       while (n > 0) {
     {{ PopInv m sh x j res n /\ n > 0 }}
         if (s->rpos[n - 1] < j) return n;
     {{ result = n = res, as clause n - 1 is below j }}
     {{ PopInv m sh x j res n /\ clause n - 1 is not below j }}
         n--;
     {{ PopInv m sh x j res (n - 1) }}
       }
     {{ PopInv m sh x j res 0 }}
       return n;
     {{ result = 0 = res }}

   The loop ends: n decreases. *)
Lemma pop_reasons_correct: forall (sh: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (j: nat),
  {{ m | RepL m sh N lss x /\ (j <= N)%nat }}
    f_pop_reasons(sptr sh, vnat j)
  {{ m', v | m' = m /\ v = vnat (pop_reasons (rps x) j (nr x)) }}.
Proof.
  intros sh N lss x j m [HRep Hj]. pose proof (r_n HRep) as HN.
  remember (pop_reasons (rps x) j (nr x)) as res eqn:Hres.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_pop_reasons. cbn [fn_body fn_return].
    pose proof HRep as HRep'. destruct HRep'.
    destruct a_rpos as (tp & Arpos & Htp). unpack.
    (* int n = s->nr; *)
    run. unfold Swhile.
    apply exec_loop with (R := Peano.lt) (I := PopInv m sh x j res) (a := nr x).
    + apply lt_wf.
    + intros n le1 m1 HI. destruct HI as [Hs Hj' Hn -> Hnle Hpop]. apply exec_seq.
      (* if (n > 0) ... else break; *)
      branch.
      * (* n > 0: the model looks at clause n - 1 *)
        intros Hpos. destruct n as [|n].
        -- (* 0 is not positive *)
           lia.
        -- assert (Hsub: Int.sub (Int.repr (Z.of_nat (S n))) (Int.repr 1)
                         = Int.repr (Z.of_nat n)).
           { rewrite sub_repr. f_equal. lia. }
           assert (Hrps: (tget (rps x) n <= N)%nat) by (apply r_rps_le; lia).
           cbn [pop_reasons] in Hpop.
           (* s->rpos[n - 1] < j *)
           run. rewrite (Htp n) by lia.
           branch.
           ++ (* below j: return n, which is res *)
              intros Hlt.
              assert (Hbelow: (tget (rps x) n <? j)%nat = true)
                by (apply Nat.ltb_lt; lia).
              rewrite Hbelow in Hpop. return_int.
              split.
              ** reflexivity.
              ** now rewrite Hpop.
           ++ (* not below j: n--; and the loop goes on *)
              intros Hge.
              assert (Hbelow: (tget (rps x) n <? j)%nat = false)
                by (apply Nat.ltb_ge; lia).
              rewrite Hbelow in Hpop. apply exec_skip. normal. run. ints.
              apply loopk_next with n.
              ** lia.
              ** constructor.
                 --- tmp.
                 --- tmp.
                 --- tmp.
                 --- reflexivity.
                 --- lia.
                 --- assumption.
      * (* n = 0: break; return n, which is res *)
        intros Hzero. assert (Hn0: n = 0%nat) by lia. subst n.
        apply exec_break. abrupt. apply loopk_break. normal.
        return_int.
        split.
        -- reflexivity.
        -- now rewrite Hpop.
    + (* The invariant holds at the number of reason clauses. *)
      constructor.
      * tmp.
      * tmp.
      * tmp.
      * reflexivity.
      * lia.
      * assumption.
Qed.

Lemma pop_reasons_fun: FunAt _pop_reasons f_pop_reasons.
Proof. apply find_fun. reflexivity. Qed.
