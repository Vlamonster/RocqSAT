(* cut unassigns the trail from a position on, with an empty queue (the values, length
   and queue of jump). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Propagate Step CStep.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep SetValue.
Import ListNotations.

(* Unassigning the last literal of a range first. *)
Lemma unset_range_last: forall (v: Values) (tr: Table Lit) (j q: nat), (j < q)%nat ->
  unset_range (unset_value v (tget tr (q - 1))) tr j (q - 1 - j)
  = unset_range v tr j (q - j).
Proof.
  intros v tr j q Hjq. replace (q - j)%nat with (Datatypes.S (q - 1 - j)) by lia. simpl.
  now replace (j + (q - 1 - j))%nat with (q - 1)%nat by lia.
Qed.

(* The invariant of the loop of cut at q, for the memory m of the call with pool t: the
   temporaries hold s, j and q, q is between j and the end of the trail, and the memory
   represents x with values v that, unassigned from j up to q, give the values of the
   model. *)
Record CutInv (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx) (lims: list nat)
  (j: nat) (t: nat -> Z) (q: nat) (le: temp_env) (m1: mem): Prop := {
  cu_s: le ! _s = Some (sptr S);
  cu_j: le ! _j = Some (vint (Z.of_nat j));
  cu_q: le ! _q = Some (vint (Z.of_nat q));
  cu_range: (j <= q <= tlen x)%nat;
  cu_vals: exists (v: Values),
    unset_range v (tr x) j (q - j) = unset_range (vals x) (tr x) j (tlen x - j) /\
    RepB m1 S N lss (set_vals x v) lims;
  cu_pool: Arr m1 (b_wpool S) (2 * npool S) t;
}.

(* cut unassigns the literals of the trail from its end down to position j, and then cuts
   the trail at j with an empty queue:

     {{ RepB m S N lss x lims /\ j <= tlen x /\ Arr m pool t }}
       int q = s->tlen;
     {{ CutInv (tlen x) }}
       while (q > j) {
     {{ CutInv q /\ q > j }}
         set_value(s, s->tr[q - 1] >> 1, 0);                          (set_value_correct)
         q--;
     {{ CutInv (q - 1) }}                                             (unset_range_last)
       }
     {{ CutInv j: the values are unset_range (vals x) (tr x) j (tlen x - j) }}
       s->tlen = j;
       s->qhead = j;                                                      (rep_store_cut)
     {{ RepB (jump x (unset_range ...) j (cur x) (saved x) (dl x) (mrk x)) /\
        Arr pool t }}

   The loop ends: q decreases. *)
Lemma cut_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (j: nat) (t: nat -> Z),
  {{ m | RepB m S N lss x lims /\ (j <= tlen x)%nat /\
    Arr m (b_wpool S) (2 * npool S) t }}
    f_cut(sptr S, vint (Z.of_nat j))
  {{ m', v | RepB m' S N lss
               (jump x (unset_range (vals x) (tr x) j (tlen x - j)) j (cur x) (saved x)
                  (dl x) (mrk x)) lims /\
             Arr m' (b_wpool S) (2 * npool S) t }}.
Proof.
  intros S N lss x lims j t m (HRep & Hj & Apool0).
  pose proof (r_n _ _ _ _ _ _ HRep) as HN.
  pose proof (r_tlen_le _ _ _ _ _ _ HRep) as Ht.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_cut. cbn [fn_body fn_return].
    pose proof (r_tlen _ _ _ _ _ _ HRep) as Ftlen.
    (* int q = s->tlen; *)
    run. clear Ftlen. unfold Swhile.
    apply exec_loop with (R := lt) (I := CutInv S N lss x lims j t) (a := tlen x).
    + apply lt_wf.
    + intros q le1 m1 HI. destruct HI as [Hs Hj' Hq Hjq (v & Hv & HRepq) Apool].
      pose proof (r_nodup _ _ _ _ _ _ HRepq) as Hnd.
      pose proof HRepq as HRepq'. destruct HRepq'. unpack.
      cbn [set_vals vals tr tlen qhead cmap wls shorts alls nlits cur saved phs
           nvars] in *.
      apply exec_seq.
      (* if (q > j) ... else break; *)
      eapply (exec_if_cmp _ _ _ Cgt).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * destruct (Nat.eq_dec q j) as [-> | Hne].
        -- (* q = j: break; s->tlen = j; s->qhead = j; *)
           replace (zcmp Cgt (Z.of_nat j) (Z.of_nat j)) with false
             by (simpl; symmetry; apply Z.ltb_irrefl).
           apply exec_break. abrupt. apply loopk_break. normal. run.
           eapply exec_store.
           ++ evl.
           ++ ev.
           ++ reflexivity.
           ++ reflexivity.
           ++ fofs. bound.
           ++ fofs. cbn [cast_int_int].
              destruct (fld_storable m1 (b_s S) 80 Mint32 _ (vint (Z.of_nat j)) r_tlen)
                as [m2 Hst2].
              exists m2. split.
              ** apply Hst2.
              ** normal.
                 assert (Fqh2: Fld m2 (b_s S) 84 Mint32 (vint (Z.of_nat (qhead x)))).
                 { apply (fld_store_other _ _ _ _ _ _ _ _ _ _ r_qhead Hst2). right.
                   unfold Mptr. cbv [Archi.ptr64]. cbn [size_chunk]. lia. }
                 eapply exec_store.
                 --- evl.
                 --- ev.
                 --- reflexivity.
                 --- reflexivity.
                 --- fofs. bound.
                 --- fofs. cbn [cast_int_int].
                     destruct (fld_storable m2 (b_s S) 84 Mint32 _ (vint (Z.of_nat j))
                                 Fqh2) as [m3 Hst3].
                     exists m3. split.
                     +++ apply Hst3.
                     +++ (* the end of cut: the values are those of the model *)
                         exists Vundef. split.
                         *** reflexivity.
                         *** rewrite Nat.sub_diag in Hv. simpl in Hv. rewrite <- Hv.
                             split.
                             ---- apply (rep_store_cut m1 m2 m3 S N lss (set_vals x v)
                                           lims j HRepq).
                                  ++++ cbn [set_vals tlen]. assumption.
                                  ++++ assumption.
                                  ++++ assumption.
                             ---- assert (Apool2: Arr m2 (b_wpool S) (2 * npool S) t).
                                  { apply (arr_store_other _ _ _ _ _ _ _ _ _ Apool Hst2).
                                    neq Hnd. }
                                  apply (arr_store_other _ _ _ _ _ _ _ _ _ Apool2 Hst3).
                                  neq Hnd.
        -- (* q > j: unassign the literal at q - 1 *)
           replace (zcmp Cgt (Z.of_nat q) (Z.of_nat j)) with true
             by (simpl; symmetry; apply Z.ltb_lt; lia).
           assert (Hsub: Int.sub (Int.repr (Z.of_nat q)) (Int.repr 1)
                         = Int.repr (Z.of_nat (q - 1))).
           { rewrite sub_repr. f_equal. lia. }
           assert (Hl: (extract (tget (tr x) (q - 1)) < N)%nat).
           { apply r_tr_atoms. lia. }
           pose proof (key_small _ N Hl r_n) as Hkey.
           assert (Hshr: Int.shr (Int.repr (key (tget (tr x) (q - 1)))) (Int.repr 1)
                         = Int.repr (Z.of_nat (extract (tget (tr x) (q - 1))))).
           { apply shr_key. lia. }
           (* set_value(s, s->tr[q - 1] >> 1, 0); *)
           cbv beta iota. run. call set_value_fun. cbn [cast_int_int]. rewrite Hshr.
           eapply call_weaken.
           { apply (set_value_correct S N lss (set_vals x v) lims _ None).
             split; assumption. }
           intros m2 v2 [HRep2 Hun2]. normal. transfer Hun2 Hnd. keep_mem m2.
           (* q--; and the loop goes on *)
           run. ints. apply loopk_next with (q - 1)%nat.
           ++ lia.
           ++ constructor.
              ** tmp.
              ** tmp.
              ** tmp.
              ** lia.
              ** exists (unset_value v (tget (tr x) (q - 1))). split.
                 --- rewrite unset_range_last by lia. assumption.
                 --- apply HRep2.
              ** assumption.
    + (* The invariant holds at the end of the trail. *)
      constructor.
      * tmp.
      * tmp.
      * tmp.
      * lia.
      * exists (vals x). split.
        -- reflexivity.
        -- destruct x. apply HRep.
      * assumption.
Qed.

Lemma cut_fun: exists (b: block),
  Genv.find_symbol ge _cut = Some b /\ Genv.find_funct_ptr ge b = Some (Internal f_cut).
Proof. apply find_fun. reflexivity. Qed.
