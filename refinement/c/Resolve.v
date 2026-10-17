(* resolve fails without decisions, and flips the last decision otherwise (resolve_t),
   or gives up. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Propagate Step CStep
  SolverStep.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep Assign Cut.
Import ListNotations.

(* What C returns and leaves for an outcome of a step on the context: 0 to stop with P of
   the memory, 1 to fail, and 2 with the next context in memory. *)
Definition COutcome (S: Shape) (N: nat) (lss: list (list Lit)) (P: mem -> Prop)
  (cr: CResult) (m: mem) (v: val): Prop :=
match cr with
| CStop          => v = vint 0 /\ P m
| CFail          => v = vint 1
| CNext x' lims' => v = vint 2 /\ Rep m S N lss x' lims'
end.

(* The statements of resolve after its test: flipping the last decision. *)
Definition resolve_flip: statement := drop_stmts 1 (fn_body f_resolve).

(* Flipping the last decision, at trail position j0, with the cursor c0 saved for it:

     {{ Rep x (j0 :: lims0) /\ saved x = c0 :: st }}
       int j0 = s->lims[s->dl - 1];
       int l = s->tr[j0];
       cut(s, j0);                                                       (cut_correct)
     {{ RepB (jump x v1 j0 (cur x) (saved x) (dl x) (mrk x)) (j0 :: lims0) }}
       s->cur = s->saved[s->dl - 1];
       s->dl = s->dl - 1;                                                (rep_store_pop)
     {{ RepB (jump x v1 j0 c0 st (dl x - 1) (mrk x)) lims0 }}            (rep_set_hints)
       if (!assign(s, l ^ 1)) return -1;                               (assign_correct)
     {{ result = -1 (out of room) }}
       return 2;
     {{ result = 2 /\ Rep (assign (jump ...) (¬l) 0) lims0 }}

   where v1 = unset_range (vals x) (tr x) j0 (tlen x - j0) and l = tget (tr x) j0. *)
Lemma resolve_flip_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims0: list nat) (j0 c0: nat) (st: list nat) (P: mem -> Prop) (tp: nat -> Z)
  (le: temp_env) (m: mem),
  RepB m S N lss x (j0 :: lims0) -> Arr m (b_wpool S) (2 * npool S) tp ->
  PoolOf S N tp (wls x) (fun (_ _: nat) => False) -> (j0 < tlen x)%nat ->
  saved x = c0 :: st -> le ! _s = Some (sptr S) ->
  Exec ge le m resolve_flip (Returns f_resolve (fun (m': mem) (v: val) =>
    v = vint (-1) \/ COutcome S N lss P (resolve_t x (j0 :: lims0)) m' v)).
Proof.
  intros S N lss x lims0 j0 c0 st P tp le m HRep Apool Hpool Hj0 Hsv Hs.
  pose proof (r_n _ _ _ _ _ _ HRep) as HN.
  pose proof HRep as HRep'. destruct HRep'.
  destruct a_lims as (tl & Alims & Htl). destruct a_saved as (tsv & Asaved & Htsv).
  unpack.
  cbn [length] in r_dl, r_dl_le, Htl.
  unfold resolve_flip, f_resolve. cbn [fn_body drop_stmts].
  assert (Hsub: Int.sub (Int.repr (Z.of_nat (Datatypes.S (length lims0)))) (Int.repr 1)
                = Int.repr (Z.of_nat (length lims0))).
  { rewrite sub_repr. f_equal. lia. }
  assert (Hl: (extract (tget (tr x) j0) < N)%nat) by (now apply r_tr_atoms).
  pose proof (key_small _ N Hl HN) as Hkl.
  assert (Htj0: tl (length lims0) = Z.of_nat j0).
  { rewrite Htl by lia. cbn [rev]. rewrite <- length_rev, nth_middle. reflexivity. }
  (* int j0 = s->lims[s->dl - 1]; int l = s->tr[j0]; cut(s, j0); *)
  run. rewrite Htj0. run. call cut_fun. eapply call_weaken.
  { apply (cut_correct S N lss x (j0 :: lims0) j0 tp m). split.
    - assumption.
    - split.
      + lia.
      + assumption. }
  intros m1 v [HRep1 Apool1]. normal. forget_mem m.
  set (v1 := unset_range (vals x) (tr x) j0 (tlen x - j0)) in HRep1.
  set (x1 := jump x v1 j0 (cur x) (saved x) (dl x) (mrk x)) in HRep1.
  pose proof r_nodup as Hnd.
  pose proof (r_cur _ _ _ _ _ _ HRep1) as Fcur1.
  pose proof (r_dl _ _ _ _ _ _ HRep1) as Fdl1.
  pose proof (r_saved _ _ _ _ _ _ HRep1) as Fsaved1.
  pose proof (r_lims _ _ _ _ _ _ HRep1) as Flims1.
  pose proof (a_saved _ _ _ _ _ _ HRep1) as (tsv1 & Asaved1 & Htsv1).
  cbn [x1 jump saved length] in Htsv1, Fdl1. rewrite Hsv in Htsv1. cbn [length] in Htsv1.
  pose proof r_saved_len as Hslen. rewrite Hsv in Hslen.
  cbn [length] in Hslen.
  assert (Hst: length st = length lims0) by lia.
  assert (Htc0: tsv1 (length lims0) = Z.of_nat c0).
  { rewrite Htsv1 by lia. cbn [rev]. rewrite <- Hst, <- length_rev, nth_middle.
    reflexivity. }
  assert (Hxor: Int.xor (Int.repr (key (tget (tr x) j0))) (Int.repr 1)
                = Int.repr (key (¬(tget (tr x) j0)))).
  { apply xor_key. lia. }
  assert (Hnl: (extract (¬(tget (tr x) j0)) < N)%nat) by (now destruct (tget (tr x) j0)).
  (* s->cur = s->saved[s->dl - 1]; *)
  run. rewrite Htc0.
  eapply exec_store.
  - evl.
  - ev.
  - reflexivity.
  - reflexivity.
  - fofs. bound.
  - fofs. cbn [cast_int_int].
    destruct (fld_storable m1 (b_s S) 116 Mint32 _ (vint (Z.of_nat c0)) Fcur1)
      as [m2 Hst2].
    exists m2. split.
    + apply Hst2.
    + normal.
      assert (Fdl2: Fld m2 (b_s S) 136 Mint32 (vint (Z.of_nat (length (j0 :: lims0))))).
      { apply (fld_store_other _ _ _ _ _ _ _ _ _ _ Fdl1 Hst2). right.
        cbn [size_chunk]. lia. }
      (* s->dl = s->dl - 1; *)
      run. eapply exec_store.
      * evl.
      * ev.
      * reflexivity.
      * reflexivity.
      * fofs. bound.
      * fofs. cbn [cast_int_int length]. ints.
        destruct (fld_storable m2 (b_s S) 136 Mint32 _ (vint (Z.of_nat (length lims0)))
                    Fdl2) as [m3 Hst3].
        exists m3. split.
        -- apply Hst3.
        -- normal.
           pose proof (rep_store_pop m1 m2 m3 S N lss x1 lims0 j0 c0 st HRep1 Hsv Hst2
                         Hst3) as HRep3.
           apply rep_set_hints
             with (r := rsn x) (lv := lvl x) (d := (dl x - 1)%nat) (mk := mrk x)
             in HRep3.
           assert (Apool2: Arr m2 (b_wpool S) (2 * npool S) tp).
           { apply (arr_store_other _ _ _ _ _ _ _ _ _ Apool1 Hst2). neq Hnd. }
           assert (Apool3: Arr m3 (b_wpool S) (2 * npool S) tp).
           { apply (arr_store_other _ _ _ _ _ _ _ _ _ Apool2 Hst3). neq Hnd. }
           keep_mem m3.
           (* if (!assign(s, l ^ 1)) return -1; *)
           run. call assign_fun. cbn [cast_int_int]. ints. eapply call_weaken.
           ++ apply (assign_correct S N lss (jump x v1 j0 c0 st (dl x - 1) (mrk x)) lims0
                       (¬(tget (tr x) j0)) 0 tp m3).
              split.
              ** apply HRep3.
              ** split; assumption.
           ++ intros m4 w Hw. normal. destruct Hw as [-> | (-> & HRep4 & Apool4)].
              ** (* out of room: return -1; *)
                 eapply (exec_if_int _ _ _ _ 1).
                 --- ev.
                 --- reflexivity.
                 --- unfold Small. lia.
                 --- change (negb (Z.eqb 1 0)) with true. cbv beta iota.
                     eapply exec_return.
                     +++ ev.
                     +++ ret. exists (vint (-1)). split.
                         *** apply result_int.
                         *** now left.
              ** (* return 2; with the flipped decision *)
                 eapply (exec_if_int _ _ _ _ 0).
                 --- ev.
                 --- reflexivity.
                 --- unfold Small. lia.
                 --- change (negb (Z.eqb 0 0)) with false. cbv beta iota. run.
                     eapply exec_return.
                     +++ ev.
                     +++ exists (vint 2). split.
                         *** apply result_int.
                         *** right. unfold resolve_t. rewrite Hsv. split.
                             ---- reflexivity.
                             ---- split.
                                  ++++ assumption.
                                  ++++ exists tp. split; assumption.
Qed.

(* resolve fails at decision level 0, and flips the last decision otherwise:

     {{ Rep x lims /\ the decision positions are on the trail }}
       if (s->dl == 0) return 1;
     {{ result = 1: no decision, fail }}
       ...                                                         (resolve_flip_correct)
     {{ result = 2 with the flipped decision, or -1 }}                          *)
Lemma resolve_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (P: mem -> Prop),
  {{ m | Rep m S N lss x lims /\ (forall (j: nat), In j lims -> (j < tlen x)%nat) }}
    f_resolve(sptr S)
  {{ m', v | v = vint (-1) \/ COutcome S N lss P (resolve_t x lims) m' v }}.
Proof.
  intros S N lss x lims P m [[HRep [tp [Apool Hpool]]] Hlims].
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_resolve. cbn [fn_body fn_return].
    pose proof (r_dl _ _ _ _ _ _ HRep) as Fdl.
    pose proof (r_dl_le _ _ _ _ _ _ HRep) as Hdl.
    pose proof (r_n _ _ _ _ _ _ HRep) as HN.
    (* if (s->dl == 0) return 1; *)
    run. eapply (exec_if_cmp _ _ _ Ceq).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + unfold Small. lia.
    + unfold Small. lia.
    + destruct lims as [|j0 lims0].
      * (* no decision: return 1; *)
        change (zcmp Ceq (Z.of_nat (length (@nil nat))) 0) with true. cbv beta iota.
        eapply exec_return.
        -- ev.
        -- ret. exists (vint 1). split.
           ++ apply result_int.
           ++ now right.
      * (* the last decision is at j0: flip it *)
        replace (zcmp Ceq (Z.of_nat (length (j0 :: lims0))) 0) with false
          by (symmetry; cbn [zcmp]; apply Z.eqb_neq; simpl; lia).
        pose proof (r_saved_len _ _ _ _ _ _ HRep) as Hslen.
        destruct (saved x) as [|c0 st] eqn:Hsv.
        -- discriminate Hslen.
        -- cbv beta iota. apply exec_skip. normal. clear Fdl.
           apply (resolve_flip_correct S N lss x lims0 j0 c0 st P tp).
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ apply Hlims. now left.
           ++ assumption.
           ++ tmp.
Qed.

Lemma resolve_fun: exists (b: block),
  Genv.find_symbol ge _resolve = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_resolve).
Proof. apply find_fun. reflexivity. Qed.
