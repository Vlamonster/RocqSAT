(* find_watch finds the first literal of a clause, from a position on, that is not false
   (the search of swap_watch). *)
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
From RocqSAT.refinement.c Require Import Arrays.
From RocqSAT.refinement.c Require Import Logic.
From RocqSAT.refinement.c Require Import Common.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Rep.
From RocqSAT.refinement.c Require Import LitValue.

(* Literal d of cls is false in v. *)
Abbreviation LitFalse v cls d := (lookup v (nth d cls (Pos 0%nat)) = Some false).

(* What find_watch returns for the literals cls of a clause at positions a on, searched
   from literal d0 on: the position of the first that is not false, or -1 if all are. *)
Definition FoundWatch (v: Values) (cls: list Lit) (d0 a: nat) (r: val): Prop :=
  (r = vint (-1) /\ forall (d: nat), (d0 <= d < length cls)%nat -> LitFalse v cls d) \/
  (exists (d: nat), (d0 <= d < length cls)%nat /\ r = vnat (a + d) /\
     ~ LitFalse v cls d /\ forall (d': nat), (d0 <= d' < d)%nat -> LitFalse v cls d').

(* find_watch returns position a + d when literal d is the first from d0 on that is not
   false. *)
Lemma found_watch_at: forall (v: Values) (cls: list Lit) (d0 a d: nat),
  (d0 <= d < length cls)%nat -> ~ LitFalse v cls d ->
  (forall (d': nat), (d0 <= d' < d)%nat -> LitFalse v cls d') ->
  FoundWatch v cls d0 a (vnat (a + d)).
Proof.
  intros v cls d0 a d Hd Hnf Hbefore. right. exists d. split.
  - assumption.
  - split.
    + reflexivity.
    + split; assumption.
Qed.

(* The invariant of the loop of find_watch at literal d of clause i with literals cls,
   for the memory m of the call: the temporaries hold s, the position q of literal d and
   the end e of the clause, the memory is still m, and the literals d0 .. d - 1 are
   false. *)
Record FindInv {m: mem} {sh: Shape} {v: Values} {i: nat} {cls: list Lit} {d0 d: nat}
  {le: temp_env} {m1: mem}: Prop := {
  fi_s: le ! _s = Some (sptr sh);
  fi_q: le ! _q = Some (vnat (starts sh i + d));
  fi_e: le ! _e = Some (vnat (starts sh (S i)));
  fi_mem: m1 = m;
  fi_range: (d0 <= d <= length cls)%nat;
  fi_before: forall (d': nat), (d0 <= d' < d)%nat -> LitFalse v cls d'
}.
Arguments FindInv : clear implicits.

(* find_watch scans the literals of clause i from literal d0 on for one that is not
   false. It stores nothing. Writing cls for the literals of clause i:

     {{ RepL m sh N lss x /\ i < length lss /\ cmap x i = cls /\ d0 <= length cls }}
     {{ FindInv d0 }}
       while (q < e) {
     {{ FindInv d /\ d < length cls }}
         if (lit_value(s, s->clits[q]) != -1) return q;
     {{ result = q, the position of literal d: not false, those before are }}
     {{ FindInv d /\ literal d is false }}
         q++;
     {{ FindInv (d + 1) }}
       }
     {{ FindInv d /\ d = length cls }}
       return -1;
     {{ result = -1, all literals from d0 on are false }}

   The loop ends: length cls - d decreases. *)
Lemma find_watch_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (i d0: nat) (cls: list Lit),
  {{ m | RepL m sh N lss x /\ (i < length lss)%nat /\ tget (cmap x) i = Some cls /\
         (d0 <= length cls)%nat }}
    f_find_watch(sptr sh, vnat (starts sh i + d0),
                 vnat (starts sh (S i)))
  {{ m', v | m' = m /\ FoundWatch (vals x) cls d0 (starts sh i) v }}.
Proof.
  intros sh N lss x i d0 cls m (HRep & Hi & Hcls & Hd0).
  pose proof (r_n HRep) as HN.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_find_watch. cbn [fn_body fn_return].
    pose proof (a_lits HRep) as (t & Alits & Hclauses).
    destruct (r_starts HRep i Hi) as [Hsi Hsn].
    pose proof HRep as HRep'. destruct HRep'.
    pose proof (clause_length sh N lss x t i cls Hclauses Hi Hcls) as Hlen.
    apply exec_seq. unfold Swhile.
    apply exec_loop
      with (R := ltof nat (fun (d: nat) => length cls - d)%nat)
      (I := FindInv m sh (vals x) i cls d0) (a := d0).
    + apply well_founded_ltof.
    + intros d le1 m1 HI. destruct HI as [Hs Hq He -> Hdrange Hbefore].
      apply exec_seq.
      (* if (q < e) ... else break; *)
      branch.
      * (* q < e: if (lit_value(s, s->clits[q]) != -1) return q; *)
        intros Hlt. assert (Hdlt: (d < length cls)%nat) by lia.
        destruct (clause_lit m sh N lss x t i d cls HRep Hclauses Hi Hcls Hdlt)
          as (Hpos & Ht & Hatom).
        set (y := nth d cls (Pos 0%nat)) in *.
        pose proof (key_small y N Hatom HN) as Hky.
        assert (Haddq: Int.add (Int.repr (Z.of_nat (starts sh i + d))) (Int.repr 1)
                       = Int.repr (Z.of_nat (starts sh i + S d))).
        { rewrite add_repr. f_equal. lia. }
        run. rewrite Ht.
        call lit_value_fun (lit_value_correct sh N lss x y).
        -- split; assumption.
        -- intros m' v [-> ->]. normal.
           eapply (exec_if_ne _ (-1)).
           ++ ev.
           ++ ev.
           ++ reflexivity.
           ++ pose proof (enc_small (lookup (vals x) y)). lia.
           ++ (* y is not false: return q; *)
              intros Hnot_false.
              assert (Hnf: not_false (vals x) y = true).
              { rewrite <- enc_not_false. apply negb_true_iff. now apply Z.eqb_neq. }
              return_int.
              split.
              ** reflexivity.
              ** apply found_watch_at.
                 --- lia.
                 --- unfold not_false in Hnf. fold y.
                     destruct (lookup (vals x) y) as [[|]|]; easy.
                 --- assumption.
           ++ (* y is false: q++; *)
              intros Hfalse.
              assert (Hnf: not_false (vals x) y = false).
              { rewrite <- enc_not_false, Hfalse. reflexivity. }
              run. normal. run. ints. apply loopk_next with (S d).
              ** unfold ltof. lia.
              ** constructor.
                 --- tmp.
                 --- tmp.
                 --- tmp.
                 --- reflexivity.
                 --- lia.
                 --- intros d' Hd'. destruct (Nat.eq_dec d' d) as [-> | Hne].
                     +++ unfold not_false in Hnf. fold y.
                         destruct (lookup (vals x) y) as [[|]|]; easy.
                     +++ apply Hbefore. lia.
      * (* q >= e: break; return -1; every literal from d0 on is false *)
        intros Hge. apply exec_break. abrupt. apply loopk_break. normal.
        return_int.
        split.
        -- reflexivity.
        -- left. split.
           ++ reflexivity.
           ++ intros d' Hd'. apply Hbefore. lia.
    + (* The invariant holds at literal d0. *)
      constructor.
      * tmp.
      * tmp.
      * tmp.
      * reflexivity.
      * lia.
      * intros d' Hd'. lia.
Qed.

Lemma find_watch_fun: FunAt _find_watch f_find_watch.
Proof. apply find_fun. reflexivity. Qed.
