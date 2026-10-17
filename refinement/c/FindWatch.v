(* find_watch finds the first literal of a clause, from a position on, that is not false
   (the search of swap_watch). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Propagate.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep LitValue.
Import ListNotations.

(* What find_watch returns for the literals cls of a clause at positions a on, searched
   from literal d0 on: the position of the first that is not false, or -1 if all are. *)
Definition FoundWatch (v: Values) (cls: list Lit) (d0 a: nat) (r: val): Prop :=
  (r = vint (-1) /\
   forall (d: nat), (d0 <= d < length cls)%nat ->
     lookup v (nth d cls (Pos 0%nat)) = Some false) \/
  (exists (d: nat), (d0 <= d < length cls)%nat /\ r = vint (Z.of_nat (a + d)) /\
     lookup v (nth d cls (Pos 0%nat)) <> Some false /\
     forall (d': nat), (d0 <= d' < d)%nat ->
       lookup v (nth d' cls (Pos 0%nat)) = Some false).

(* The invariant of the loop of find_watch at literal d of clause i with literals cls,
   for the memory m of the call: the temporaries hold s, the position q of literal d and
   the end e of the clause, the memory is still m, and the literals from d0 to d are
   false. *)
Record FindInv (m: mem) (S: Shape) (v: Values) (i: nat) (cls: list Lit) (d0 d: nat)
  (le: temp_env) (m1: mem): Prop := {
  fi_s: le ! _s = Some (sptr S);
  fi_q: le ! _q = Some (vint (Z.of_nat (starts S i + d)));
  fi_e: le ! _e = Some (vint (Z.of_nat (starts S (Datatypes.S i))));
  fi_mem: m1 = m;
  fi_range: (d0 <= d <= length cls)%nat;
  fi_before: forall (d': nat), (d0 <= d' < d)%nat ->
    lookup v (nth d' cls (Pos 0%nat)) = Some false
}.

(* find_watch scans the literals of clause i from literal d0 on for one that is not
   false. It stores nothing. Writing cls for the literals of clause i:

     {{ RepB m S N lss x lims /\ i < length lss /\ cmap x i = cls /\ d0 <= length cls }}
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
Lemma find_watch_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (i d0: nat) (cls: list Lit),
  {{ m | RepB m S N lss x lims /\ (i < length lss)%nat /\ tget (cmap x) i = Some cls /\
         (d0 <= length cls)%nat }}
    f_find_watch(sptr S, vint (Z.of_nat (starts S i + d0)),
                 vint (Z.of_nat (starts S (Datatypes.S i))))
  {{ m', v | m' = m /\ FoundWatch (vals x) cls d0 (starts S i) v }}.
Proof.
  intros S N lss x lims i d0 cls m (HRep & Hi & Hcls & Hd0).
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_find_watch. cbn [fn_body fn_return].
    pose proof (a_lits _ _ _ _ _ _ _ HRep) as (t & Alits & Hclauses).
    destruct (r_starts _ _ _ _ _ _ _ HRep i Hi) as [Hsi Hsn].
    pose proof HRep as HRep'. destruct HRep'.
    pose proof (clause_length m S N lss x lims t i cls Hclauses Hi Hcls) as Hlen.
    apply exec_seq. unfold Swhile.
    apply exec_loop
      with (R := ltof nat (fun (d: nat) => length cls - d)%nat)
      (I := FindInv m S (vals x) i cls d0) (a := d0).
    + apply well_founded_ltof.
    + intros d le1 m1 HI. destruct HI as [Hs Hq He -> Hdrange Hbefore].
      apply exec_seq.
      (* if (q < e) ... else break; *)
      eapply (exec_if_cmp _ _ _ Clt).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * destruct (Nat.lt_ge_cases d (length cls)) as [Hdlt | Hdge].
        -- (* q < e: if (lit_value(s, s->clits[q]) != -1) return q; *)
           replace (zcmp Clt (Z.of_nat (starts S i + d))
             (Z.of_nat (starts S (Datatypes.S i))))
             with true
             by (simpl; symmetry; apply Z.ltb_lt; lia).
           destruct (clause_lit m S N lss x lims t i d cls HRep Hclauses Hi Hcls Hdlt)
             as (Hpos & Ht & Hatom).
           set (y := nth d cls (Pos 0%nat)) in *.
           pose proof (key_small y N Hatom HN) as Hky.
           assert (Haddq: Int.add (Int.repr (Z.of_nat (starts S i + d))) (Int.repr 1)
                          = Int.repr (Z.of_nat (starts S i + Datatypes.S d))).
           { rewrite add_repr. f_equal. lia. }
           cbv beta iota. run. rewrite Ht.
           call lit_value_fun. eapply call_weaken.
           { apply (lit_value_correct S N lss x lims y m). split; assumption. }
           intros m' v [-> ->]. normal.
           eapply (exec_if_cmp _ _ _ Cne _ _ _ (-1)).
           ++ ev.
           ++ ev.
           ++ reflexivity.
           ++ reflexivity.
           ++ apply enc_small.
           ++ unfold Small. lia.
           ++ cbn [zcmp]. rewrite enc_not_false.
              destruct (not_false (vals x) y) eqn:Hnf; cbn [negb].
              ** (* y is not false: return q; *)
                 eapply exec_return.
                 --- ev.
                 --- ret. exists (vint (Z.of_nat (starts S i + d))). split.
                     +++ apply result_int.
                     +++ split.
                         *** reflexivity.
                         *** right. exists d. split.
                             ---- lia.
                             ---- split.
                                  ++++ reflexivity.
                                  ++++ split.
                                       **** unfold not_false in Hnf.
                                            fold y. destruct (lookup (vals x) y) as
                                              [[|]|]; easy.
                                       **** assumption.
              ** (* y is false: q++; *)
                 run. normal. run. ints. apply loopk_next with (Datatypes.S d).
                 --- unfold ltof. lia.
                 --- constructor.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
                     +++ reflexivity.
                     +++ lia.
                     +++ intros d' Hd'. destruct (Nat.eq_dec d' d) as [-> | Hne].
                         *** unfold not_false in Hnf. fold y.
                             destruct (lookup (vals x) y) as [[|]|]; easy.
                         *** apply Hbefore. lia.
        -- (* q >= e: break; return -1; every literal from d0 on is false *)
           replace (zcmp Clt (Z.of_nat (starts S i + d))
             (Z.of_nat (starts S (Datatypes.S i))))
             with false
             by (simpl; symmetry; apply Z.ltb_ge; lia).
           cbv beta iota. apply exec_break. abrupt. apply loopk_break. normal.
           eapply exec_return.
           ++ ev.
           ++ exists (vint (-1)). split.
              ** apply result_int.
              ** split.
                 --- reflexivity.
                 --- left. split.
                     +++ reflexivity.
                     +++ intros d' Hd'. apply Hbefore. lia.
    + (* The invariant holds at literal d0. *)
      constructor.
      * tmp.
      * tmp.
      * tmp.
      * reflexivity.
      * lia.
      * intros d' Hd'. lia.
Qed.

Lemma find_watch_fun: exists (b: block),
  Genv.find_symbol ge _find_watch = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_find_watch).
Proof. apply find_fun. reflexivity. Qed.
