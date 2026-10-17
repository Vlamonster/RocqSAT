(* propagate visits the watchers of the queued literals until a conflict (propagate_t),
   or gives up. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Propagate CStep.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep Visit.
Import ListNotations.

(* A visit keeps the queue, and only extends the trail. *)
Lemma visit_t_qhead: forall (p: Lit) (ws kept: list Watcher) (x x': Ctx) (r: option nat),
  visit_t p ws kept x = (x', r) -> qhead x' = qhead x /\ (tlen x <= tlen x')%nat.
Proof.
  intros p ws. induction ws as [|[i b] ws IH]; intros kept x x' r Hv; simpl in Hv.
  - injection Hv as <- <-. cbn [set_watching qhead tlen]. split.
    + reflexivity.
    + lia.
  - destruct (lookup_true (vals x) b).
    + now apply IH in Hv.
    + destruct (tget (cmap x) i) as [[|c0 [|c1 ls]]|].
      * now apply IH in Hv.
      * destruct (c0 =? p).
        -- injection Hv as <- <-. cbn [set_watching qhead tlen]. split.
           ++ reflexivity.
           ++ lia.
        -- now apply IH in Hv.
      * destruct ((c0 =? p) || (c1 =? p)).
        -- destruct (lookup_true _ (if c0 =? p then c1 else c0)).
           ++ apply IH in Hv as [Hq Ht]. cbn [set_clause qhead tlen] in Hq, Ht. split.
              ** assumption.
              ** lia.
           ++ destruct (swap_watch _ p ls) as [[r' ls']|].
              ** apply IH in Hv as [Hq Ht].
                 cbn [move_watch set_clause qhead tlen] in Hq, Ht.
                 split.
                 --- assumption.
                 --- lia.
              ** destruct (lookup_undef _ (if c0 =? p then c1 else c0)).
                 --- apply IH in Hv as [Hq Ht].
                     cbn [assign set_clause qhead tlen] in Hq, Ht.
                     split.
                     +++ assumption.
                     +++ lia.
                 --- injection Hv as <- <-. cbn [set_watching set_clause qhead tlen].
                     split.
                     +++ reflexivity.
                     +++ lia.
        -- now apply IH in Hv.
      * now apply IH in Hv.
Qed.

(* The parts of propagate proved in lemmas of their own: its loop, and the body of the
   loop after its test. *)
Definition prop_loop: statement := first_stmt (drop_stmts 1 (fn_body f_propagate)).
Definition prop_body: statement := drop_stmts 1 (loop_body prop_loop).

(* The invariant of the loop of propagate with fuel f, for the result res of the model:
   the temporaries hold s and f, and the memory represents a context xc from which
   propagate_t with fuel f gives res. *)
Record FuelInv (S: Shape) (N: nat) (lss: list (list Lit)) (lims: list nat)
  (res: Ctx * option nat) (xc: Ctx) (f: nat) (le: temp_env) (m1: mem): Prop := {
  fu_s: le ! _s = Some (sptr S);
  fu_fuel: le ! _fuel = Some (vint (Z.of_nat f));
  fu_le: (f <= Datatypes.S N)%nat;
  fu_rep: Rep m1 S N lss xc lims;
  fu_res: res = propagate_t f xc;
}.

Definition fuel_inv (S: Shape) (N: nat) (lss: list (list Lit)) (lims: list nat)
  (res: Ctx * option nat) (f: nat) (le: temp_env) (m1: mem): Prop :=
  exists (xc: Ctx), FuelInv S N lss lims res xc f le m1.

Definition fuel_variant: nat -> nat -> Prop := ltof nat (fun (f: nat) => f).

(* What the loop of propagate ends in: out of fuel, which is res with no conflict; a
   return of the outcome of res, a conflict on one of the clauses lss or none; or out of
   room (return -1). *)
Definition PropPost (S: Shape) (N: nat) (lss: list (list Lit)) (lims: list nat)
  (res: Ctx * option nat) (le: temp_env) (m: mem) (out: outcome): Prop :=
  (out = Out_normal /\ snd res = None /\ Rep m S N lss (fst res) lims) \/
  (out = Out_return (Some (vint (enc_conf (snd res)), Ctypesdefs.tint)) /\
   Rep m S N lss (fst res) lims /\
   (forall (i: nat), snd res = Some i -> (i < length lss)%nat)) \/
  out = Out_return (Some (vint (-1), Ctypesdefs.tint)).

(* One pass of the loop, with fuel f + 1, as propagate_t (f + 1):

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
Lemma prop_body_correct: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (lims: list nat) (res: Ctx * option nat) (xc: Ctx) (f: nat) (le: temp_env) (m1: mem),
  FuelInv S N lss lims res xc (Datatypes.S f) le m1 ->
  Exec ge le m1 prop_body
    (LoopK fuel_variant (fuel_inv S N lss lims res) (PropPost S N lss lims res)
       (Datatypes.S f)).
Proof.
  intros S N lss lims res xc f le m1 HI.
  destruct HI as [Hs Hf Hfle [HRepc [tp [Apool Hpool]]] Hprop].
  pose proof (r_n _ _ _ _ _ _ _ HRepc) as HN.
  pose proof HRepc as HRepc'. destruct HRepc'. unpack.
  unfold prop_body, prop_loop, f_propagate.
  cbn [fn_body drop_stmts first_stmt loop_body Swhile].
  cbn [propagate_t] in Hprop.
  (* if (s->qhead >= s->tlen) return 0; *)
  run. eapply (exec_if_cmp _ _ _ Cge).
  - ev.
  - ev.
  - reflexivity.
  - reflexivity.
  - unfold Small. lia.
  - unfold Small. lia.
  - destruct (Nat.lt_ge_cases (qhead xc) (tlen xc)) as [Hq | Hq].
    + (* a literal to visit: int c = visit(s, s->tr[s->qhead] ^ 1); *)
      replace (zcmp Cge (Z.of_nat (qhead xc)) (Z.of_nat (tlen xc))) with false
        by (symmetry; cbn [zcmp]; apply Z.leb_gt; lia).
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
      cbv beta iota. run. call visit_fun. cbn [cast_int_int]. ints. eapply call_weaken.
      * apply (visit_correct S N lss xc lims p m1). split.
        -- split.
           ++ assumption.
           ++ exists tp. split; assumption.
        -- assumption.
      * intros m2 v Hv. normal. forget_mem m1.
        destruct Hv as [-> | (-> & HRep2 & Hcls)].
        -- (* out of room: if (c != 0) return c; with c = -1 *)
           run. eapply (exec_if_cmp _ _ _ Cne _ _ (-1) 0).
           ++ ev.
           ++ ev.
           ++ reflexivity.
           ++ reflexivity.
           ++ unfold Small. lia.
           ++ unfold Small. lia.
           ++ change (zcmp Cne (-1) 0) with true. cbv beta iota. eapply exec_return.
              ** ev.
              ** ret. right. right. reflexivity.
        -- unfold watching in *.
           destruct (visit_t p (tget (wls xc) (lit_key p)) [] xc) as [x1 [i|]]
             eqn:Hvisit; cbn [fst snd enc_conf] in HRep2 |- *.
           ++ (* a conflict on clause i: if (c != 0) return c; with c = i + 1 *)
              pose proof (Hcls i eq_refl) as Hi_lt.
              run. eapply (exec_if_cmp _ _ _ Cne _ _ (Z.of_nat i + 1) 0).
              ** ev.
              ** ev.
              ** reflexivity.
              ** reflexivity.
              ** unfold Small. lia.
              ** unfold Small. lia.
              ** replace (zcmp Cne (Z.of_nat i + 1) 0) with true
                   by (symmetry; cbn [zcmp]; apply negb_true_iff, Z.eqb_neq; lia).
                 cbv beta iota. eapply exec_return.
                 --- ev.
                 --- ret. right. left. rewrite Hprop. cbn [fst snd enc_conf]. split.
                     +++ reflexivity.
                     +++ split.
                         *** assumption.
                         *** assumption.
           ++ (* no conflict: s->qhead = s->qhead + 1; fuel--; *)
              run. eapply (exec_if_cmp _ _ _ Cne _ _ 0 0).
              ** ev.
              ** ev.
              ** reflexivity.
              ** reflexivity.
              ** unfold Small. lia.
              ** unfold Small. lia.
              ** change (zcmp Cne 0 0) with false. cbv beta iota.
                 destruct HRep2 as [HRep2 [tq [Apool2 Hpool2]]].
                 destruct (visit_t_qhead _ _ _ _ _ _ Hvisit) as [Hqv Htv].
                 pose proof (Rep.r_qhead _ _ _ _ _ _ _ HRep2) as Fqh2.
                 pose proof (Rep.r_tlen _ _ _ _ _ _ _ HRep2) as Ftlen2.
                 pose proof (Rep.r_nodup _ _ _ _ _ _ _ HRep2) as Hnd2.
                 pose proof (Rep.r_qhead_le _ _ _ _ _ _ _ HRep2) as Hqle2.
                 assert (Hq1': Int.add (Int.repr (Z.of_nat (qhead x1))) (Int.repr 1)
                               = Int.repr (Z.of_nat (Datatypes.S (qhead x1)))).
                 { rewrite add_repr by lia. f_equal. lia. }
                 assert (Hf1: Int.sub (Int.repr (Z.of_nat (Datatypes.S f))) (Int.repr 1)
                              = Int.repr (Z.of_nat f)).
                 { rewrite sub_repr. f_equal. lia. }
                 run. eapply exec_store.
                 --- evl.
                 --- ev.
                 --- reflexivity.
                 --- reflexivity.
                 --- fofs. bound.
                 --- fofs. cbn [cast_int_int]. ints.
                     destruct (fld_storable m2 (b_s S) 84 Mint32 _
                                 (vint (Z.of_nat (Datatypes.S (qhead x1)))) Fqh2)
                       as [m3 Hst3].
                     exists m3. split.
                     +++ apply Hst3.
                     +++ normal.
                         assert (Hn: (Datatypes.S (qhead x1) <= tlen x1)%nat) by lia.
                         pose proof (rep_store_qhead m2 m3 S N lss x1 lims _ HRep2 Hn
                                       Hst3) as HRep3.
                         run. ints. apply loopk_next with f.
                         *** unfold fuel_variant, ltof. lia.
                         *** exists (advance x1). constructor.
                             ---- tmp.
                             ---- tmp.
                             ---- lia.
                             ---- split.
                                  ++++ apply HRep3.
                                  ++++ exists tq. split.
                                       **** apply (arr_store_other _ _ _ _ _ _ _ _ _
                                                     Apool2 Hst3).
                                            neq Hnd2.
                                       **** assumption.
                             ---- rewrite Hprop. reflexivity.
    + (* the queue is empty: return 0; *)
      replace (zcmp Cge (Z.of_nat (qhead xc)) (Z.of_nat (tlen xc))) with true
        by (symmetry; cbn [zcmp]; apply Z.leb_le; lia).
      replace (qhead xc <? tlen xc)%nat with false in Hprop
        by (symmetry; now apply Nat.ltb_ge).
      cbv beta iota. eapply exec_return.
      * ev.
      * ret. right. left. rewrite Hprop. cbn [fst snd enc_conf]. split.
        -- reflexivity.
        -- split.
           ++ split.
              ** assumption.
              ** exists tp. split; assumption.
           ++ intros i Heq. discriminate.
Qed.

(* The loop of propagate, from fuel N + 1:

     {{ FuelInv x (N + 1) }}
       while (fuel > 0) { ... }                                   (prop_body_correct)
     {{ FuelInv xc 0 }} ->>
     {{ res = (xc, None): no conflict }}

   The loop ends: the fuel decreases. *)
Lemma prop_loop_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (res: Ctx * option nat) (le: temp_env) (m: mem),
  fuel_inv S N lss lims res (Datatypes.S N) le m ->
  Exec ge le m prop_loop (PropPost S N lss lims res).
Proof.
  intros S N lss x lims res le m HI0.
  unfold prop_loop, f_propagate. cbn [fn_body drop_stmts first_stmt]. unfold Swhile.
  apply exec_loop with (R := fuel_variant) (I := fuel_inv S N lss lims res)
    (a := Datatypes.S N).
  - apply well_founded_ltof.
  - intros f le1 m1 [xc HI]. pose proof HI as HI'.
    destruct HI' as [Hs Hf Hfle HRepc Hprop]. apply exec_seq.
    (* if (fuel > 0) ... else break; *)
    eapply (exec_if_cmp _ _ _ Cgt _ _ _ 0).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + pose proof (r_n _ _ _ _ _ _ _ (proj1 HRepc)). unfold Small. lia.
    + unfold Small. lia.
    + destruct f as [|f].
      * (* out of fuel: break; with no conflict *)
        change (zcmp Cgt (Z.of_nat 0) 0) with false. cbv beta iota.
        apply exec_break. abrupt. apply loopk_break. left. split.
        -- reflexivity.
        -- rewrite Hprop. cbn [propagate_t fst snd]. split.
           ++ reflexivity.
           ++ assumption.
      * (* fuel > 0: the body *)
        replace (zcmp Cgt (Z.of_nat (Datatypes.S f)) 0) with true
          by (symmetry; cbn [zcmp]; apply Z.ltb_lt; lia).
        cbv beta iota. apply exec_skip. normal.
        apply (prop_body_correct S N lss lims res xc f le1 m1). assumption.
  - assumption.
Qed.

(* propagate visits the queued literals with fuel N + 1, at most one per literal of the
   trail:

     {{ Rep m S N lss x lims }}
       int fuel = s->nv + 1;
       while (fuel > 0) { ... }                                   (prop_loop_correct)
       return 0;
     {{ result = -1, or the outcome of propagate_t (N + 1) x /\ Rep of its
        context /\ a conflict is on one of the clauses lss }}                      *)
Lemma propagate_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat),
  {{ m | Rep m S N lss x lims }}
    f_propagate(sptr S)
  {{ m', v | v = vint (-1) \/
             (v = vint (enc_conf (snd (propagate_t (Datatypes.S N) x))) /\
              Rep m' S N lss (fst (propagate_t (Datatypes.S N) x)) lims /\
              forall (i: nat), snd (propagate_t (Datatypes.S N) x) = Some i ->
                (i < length lss)%nat) }}.
Proof.
  intros S N lss x lims m HRep. pose proof (r_n _ _ _ _ _ _ _ (proj1 HRep)) as HN.
  remember (propagate_t (Datatypes.S N) x) as res eqn:Hres.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_propagate. cbn [fn_body fn_return].
    assert (Hfuel: Int.add (Int.repr (Z.of_nat N)) (Int.repr 1)
                   = Int.repr (Z.of_nat (Datatypes.S N))).
    { rewrite add_repr by lia. f_equal. lia. }
    pose proof (r_nv _ _ _ _ _ _ _ (proj1 HRep)) as Fnv.
    (* int fuel = s->nv + 1; *)
    run. ints. clear Fnv.
    apply exec_weaken with (Q := PropPost S N lss lims res).
    + apply (prop_loop_correct S N lss x lims res). exists x. constructor.
      * tmp.
      * tmp.
      * lia.
      * assumption.
      * assumption.
    + intros le' m' out [(-> & Hnone & HRep') | [(-> & HRep' & Hcls) | ->]].
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
      * (* a return of the outcome *)
        abrupt. exists (vint (enc_conf (snd res))). split.
        -- apply result_int.
        -- right. split.
           ++ reflexivity.
           ++ split.
              ** assumption.
              ** assumption.
      * (* out of room *)
        abrupt. exists (vint (-1)). split.
        -- apply result_int.
        -- now left.
Qed.

Lemma propagate_fun: exists (b: block),
  Genv.find_symbol ge _propagate = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_propagate).
Proof. apply find_fun. reflexivity. Qed.
