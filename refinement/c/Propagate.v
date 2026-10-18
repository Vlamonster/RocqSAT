(* propagate visits the watchers of the queued literals until a conflict (propagate),
   or gives up. *)
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
From RocqSAT.refinement.c Require Import Visit.

(* The parts of propagate proved in lemmas of their own: its loop, and the body of the
   loop after its test. *)
Definition prop_loop: statement := first_stmt (drop_stmts 1 (fn_body f_propagate)).
Definition prop_body: statement := drop_stmts 1 (loop_body prop_loop).

(* The invariant of the loop of propagate with fuel f, for the result res of the model:
   the temporaries hold s and f, and the memory represents a context xc from which
   propagate with fuel f gives res. *)
Record FuelInv {sh: Shape} {N: nat} {lss: list (list Lit)}
  {res: Ctx * option nat} {xc: Ctx} {f: nat} {le: temp_env} {m1: mem}: Prop := {
  fu_s: le ! _s = Some (sptr sh);
  fu_fuel: le ! _fuel = Some (vnat f);
  fu_le: (f <= S N)%nat;
  fu_rep: Rep m1 sh N lss xc;
  fu_res: res = propagate f xc;
}.
Arguments FuelInv : clear implicits.

(* The invariant of the loop at fuel f: FuelInv for some context xc. *)
Definition fuel_inv (sh: Shape) (N: nat) (lss: list (list Lit))
  (res: Ctx * option nat) (f: nat) (le: temp_env) (m1: mem): Prop :=
  exists (xc: Ctx), FuelInv sh N lss res xc f le m1.

(* The loop ends: the fuel decreases. *)
Definition fuel_variant: nat -> nat -> Prop := ltof nat (fun (f: nat) => f).

(* One pass of the loop, with fuel f + 1, as propagate (f + 1):

     {{ FuelInv xc (f + 1) }}
       if (s->qhead >= s->tlen) return 0;
     {{ result = 0: the queue is empty, res = (xc, None) }}
       int c = visit(s, s->tr[s->qhead] ^ 1);                         (visit_correct)
       if (c != 0) return c;
     {{ result = c: a conflict on clause i (i + 1) or out of room (-1) }}
     {{ Rep x1, after the visit without conflict }}
       s->qhead = s->qhead + 1;                                       (rep_store_qhead)
       fuel--;
     {{ FuelInv (advance x1) f }}                                                *)
Lemma prop_body_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (res: Ctx * option nat) (xc: Ctx) (f: nat) (le: temp_env) (m1: mem),
  FuelInv sh N lss res xc (S f) le m1 ->
  Exec ge le m1 prop_body
    (LoopK fuel_variant (fuel_inv sh N lss res) (LoopOut sh N lss res) (S f)).
Proof.
  intros sh N lss res xc f le m1 HI.
  destruct HI as [Hs Hf Hfle [HRepc [Hlower [tp [Apool Hpool]]]] Hprop].
  pose proof (r_n HRepc) as HN.
  pose proof HRepc as HRepc'. destruct HRepc'. unpack.
  unfold prop_body, prop_loop, f_propagate.
  cbn [fn_body drop_stmts first_stmt loop_body Swhile].
  cbn [propagate] in Hprop.
  (* if (s->qhead >= s->tlen) return 0; *)
  run. eapply exec_if_ge.
  - ev.
  - ev.
  - reflexivity.
  - lia.
  - (* the queue is empty: return 0; *)
    intros Hge. replace (qhead xc <? tlen xc)%nat with false in Hprop
      by (symmetry; apply Nat.ltb_ge; lia).
    eapply exec_return.
    + ev.
    + ret. right. exists 0. split.
      * reflexivity.
      * right. rewrite Hprop. cbn [fst snd enc_conf]. split.
        -- reflexivity.
        -- split.
           ++ split.
              ** assumption.
              ** split.
                 --- assumption.
                 --- exists tp. split; assumption.
           ++ intros i Heq. discriminate.
  - (* a literal to visit: int c = visit(s, s->tr[s->qhead] ^ 1); *)
    intros Hlt. assert (Hq: (qhead xc < tlen xc)%nat) by lia.
    replace (qhead xc <? tlen xc)%nat with true in Hprop
      by (symmetry; now apply Nat.ltb_lt).
    pose proof (r_tr_atoms (qhead xc) Hq) as Hl.
    pose proof (key_small _ N Hl HN) as Hkl.
    set (p := ¬(tget (tr xc) (qhead xc))) in *.
    assert (Hxor: Int.xor (Int.repr (key (tget (tr xc) (qhead xc)))) (Int.repr 1)
                  = Int.repr (key p)).
    { apply xor_key. lia. }
    assert (Hp: (extract p < N)%nat).
    { unfold p. now destruct (tget (tr xc) (qhead xc)). }
    run.
    eapply (exec_call_triple visit_fun (visit_correct sh N lss xc p)).
    + reflexivity.
    + unfold vint. rewrite <- Hxor. evs.
    + split.
      * split.
        -- assumption.
        -- split.
           ++ assumption.
           ++ exists tp. split; assumption.
      * assumption.
    + intros m2 v Hv. normal. forget_mem m1.
      destruct Hv as [-> | (-> & HRep2 & Hcls)].
      * (* out of room: if (c != 0) return c; with c = -1 *)
        run. eapply exec_if_ne with (z1 := -1) (z2 := 0).
        -- ev.
        -- ev.
        -- reflexivity.
        -- lia.
        -- intros Hne. eapply exec_return.
           ++ ev.
           ++ ret. right. exists (-1). split.
              ** reflexivity.
              ** now left.
        -- (* -1 is not 0 *)
           intros Heq. lia.
      * unfold watching in *.
        destruct (visit p (tget (wls xc) (lit_key p)) [] xc) as [x1 [i|]]
          eqn:Hvisit; cbn [fst snd enc_conf] in HRep2 |- *.
        -- (* a conflict on clause i: if (c != 0) return c; with c = i + 1 *)
           pose proof (Hcls i eq_refl) as Hi_lt.
           run. eapply exec_if_ne with (z1 := Z.of_nat i + 1) (z2 := 0).
           ++ ev.
           ++ ev.
           ++ reflexivity.
           ++ lia.
           ++ intros Hne. eapply exec_return.
              ** ev.
              ** ret. right. exists (Z.of_nat i + 1). split.
                 --- reflexivity.
                 --- right. rewrite Hprop. cbn [fst snd enc_conf]. split.
                     +++ reflexivity.
                     +++ split.
                         *** assumption.
                         *** assumption.
           ++ (* i + 1 is not 0 *)
              intros Heq. lia.
        -- (* no conflict: s->qhead = s->qhead + 1; fuel--; *)
           run. eapply exec_if_ne with (z1 := 0) (z2 := 0).
           ++ ev.
           ++ ev.
           ++ reflexivity.
           ++ lia.
           ++ (* 0 is 0 *)
              intros Hne. lia.
           ++ intros Heq.
              destruct HRep2 as [HRep2 [Hlower2 [tq [Apool2 Hpool2]]]].
              destruct (visit_qhead Hvisit) as [Hqv Htv].
              pose proof (Rep.r_qhead HRep2) as Fqh2.
              pose proof (Rep.r_tlen HRep2) as Ftlen2.
              pose proof (Rep.r_nodup HRep2) as Hnd2.
              pose proof (Rep.r_qhead_le HRep2) as Hqle2.
              assert (Hq1': Int.add (Int.repr (Z.of_nat (qhead x1))) (Int.repr 1)
                            = Int.repr (Z.of_nat (S (qhead x1)))).
              { rewrite add_repr by lia. f_equal. lia. }
              assert (Hf1: Int.sub (Int.repr (Z.of_nat (S f))) (Int.repr 1)
                           = Int.repr (Z.of_nat f)).
              { rewrite sub_repr. f_equal. lia. }
              run. eapply (exec_store_fld Fqh2).
              ** evl.
              ** reflexivity.
              ** ev.
              ** intros m3 Hst3. normal.
                 cbn [cast_int_int] in Hst3. rewrite Hq1' in Hst3.
                 assert (Hn: (S (qhead x1) <= tlen x1)%nat) by lia.
                 pose proof (rep_store_qhead m2 m3 _ HRep2 Hn Hst3)
                   as HRep3.
                 run. ints. apply loopk_next with f.
                 --- unfold fuel_variant, ltof. lia.
                 --- exists (advance x1). constructor.
                     +++ tmp.
                     +++ tmp.
                     +++ lia.
                     +++ split.
                         *** apply HRep3.
                         *** split.
                             ---- (* advance keeps the lower literals *)
                                  apply Hlower2.
                             ---- exists tq. split.
                                  ++++ apply (arr_store_other Apool2 Hst3).
                                       neq Hnd2.
                                  ++++ assumption.
                     +++ rewrite Hprop. reflexivity.
Qed.

(* The loop of propagate, from fuel N + 1:

     {{ FuelInv x (N + 1) }}
       while (fuel > 0) { ... }                                   (prop_body_correct)
     {{ FuelInv xc 0 }} ->>
     {{ res = (xc, None): no conflict }}

   The loop ends: the fuel decreases. *)
Lemma prop_loop_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (res: Ctx * option nat) (le: temp_env) (m: mem),
  fuel_inv sh N lss res (S N) le m ->
  Exec ge le m prop_loop (LoopOut sh N lss res).
Proof.
  intros sh N lss res le m HI0.
  unfold prop_loop, f_propagate. cbn [fn_body drop_stmts first_stmt]. unfold Swhile.
  apply exec_loop with (R := fuel_variant) (I := fuel_inv sh N lss res)
    (a := S N).
  - apply well_founded_ltof.
  - intros f le1 m1 [xc HI]. pose proof HI as HI'.
    destruct HI' as [Hs Hf Hfle HRepc Hprop]. apply exec_seq.
    (* if (fuel > 0) ... else break; *)
    eapply exec_if_gt with (z2 := 0).
    + ev.
    + ev.
    + reflexivity.
    + pose proof (r_n (proj1 HRepc)). lia.
    + (* fuel > 0: the body *)
      intros Hpos. destruct f as [|f].
      * (* fuel 0 is not positive *)
        lia.
      * apply exec_skip. normal.
        apply (prop_body_correct sh N lss res xc f le1 m1). assumption.
    + (* out of fuel: break; with no conflict *)
      intros Hle. assert (Hf0: f = 0%nat) by lia. subst f.
      apply exec_break. abrupt. apply loopk_break. left. split.
      * reflexivity.
      * rewrite Hprop. cbn [propagate fst snd]. split.
        -- reflexivity.
        -- assumption.
  - assumption.
Qed.

(* propagate visits the queued literals with fuel N + 1, at most one per literal of the
   trail:

     {{ Rep m sh N lss x }}
       int fuel = s->nv + 1;
       while (fuel > 0) { ... }                                   (prop_loop_correct)
       return 0;
     {{ ConfOut (propagate (N + 1) x) }}                                         *)
Lemma propagate_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx),
  {{ m | Rep m sh N lss x }}
    f_propagate(sptr sh)
  {{ m', v | ConfOut sh N lss (propagate (S N) x) m' v }}.
Proof.
  intros sh N lss x m HRep. pose proof (r_n (proj1 HRep)) as HN.
  remember (propagate (S N) x) as res eqn:Hres.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_propagate. cbn [fn_body fn_return].
    assert (Hfuel: Int.add (Int.repr (Z.of_nat N)) (Int.repr 1)
                   = Int.repr (Z.of_nat (S N))).
    { rewrite add_repr by lia. f_equal. lia. }
    pose proof (r_nv (proj1 HRep)) as Fnv.
    (* int fuel = s->nv + 1; *)
    run. ints. clear Fnv.
    apply exec_weaken with (Q := LoopOut sh N lss res).
    + apply (prop_loop_correct sh N lss res). exists x. constructor.
      * tmp.
      * tmp.
      * lia.
      * assumption.
      * assumption.
    + intros le' m' out [(-> & Hnone & HRep') | (z & -> & Hz)].
      * (* out of fuel: return 0; *)
        normal. eapply exec_return.
        -- ev.
        -- exists (vint 0). split.
           ++ apply result_int.
           ++ right. split.
              ** rewrite Hnone. reflexivity.
              ** split.
                 --- assumption.
                 --- rewrite Hnone. intros i Heq. discriminate.
      * (* a return: the outcome of res, or -1 when out of room *)
        abrupt. exists (vint z). split.
        -- apply result_int.
        -- assumption.
Qed.

Lemma propagate_fun: FunAt _propagate f_propagate.
Proof. apply find_fun. reflexivity. Qed.
