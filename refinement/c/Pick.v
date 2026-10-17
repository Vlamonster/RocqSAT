(* pick takes atoms out of the heap until the literal to decide on of one is unassigned
   (pick). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Heur Propagate Analysis Step.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep RepHeur HeapPop
  LitValue.
Import ListNotations.

(* The atom heap_pop takes out is the one at the top. *)
Lemma heap_pop_snd: forall (h: Heur), snd (heap_pop h) = tget (heap h) 0.
Proof.
  intros h. unfold heap_pop. destruct (0 <? hsize h - 1)%nat.
  - reflexivity.
  - reflexivity.
Qed.

(* The invariant of the loop of pick at fuel f, for the memory m of the call and the
   result res of the model: the temporaries hold s and f, f is at most N, the memory
   represents x with a heuristic h for which pick with fuel f gives res, and only the
   heuristic is written. *)
Record PickInv {lt: list Lit} (m: mem) (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (res: Heur * option Lit) (f: nat) (le: temp_env)
  (m1: mem): Prop := {
  pi_s: le ! _s = Some (sptr S);
  pi_fuel: le ! _fuel = Some (vint (Z.of_nat f));
  pi_le: (f <= N)%nat;
  pi_heur: exists (h: Heur), pick (vals x) h f = res /\
    RepL m1 S N lss (with_heur x h) lims lt;
  pi_frame: Mem.unchanged_on (HeurFrame S) m m1;
}.

(* The last statement of the loop of pick: fuel--. *)
Definition pick_dec: statement :=
  drop_stmts 5 (loop_body (first_stmt (drop_stmts 1 (fn_body f_pick)))).

(* fuel--, once the atom taken out did not give a literal: the loop goes on with fuel f
   for the heuristic h, from which pick with fuel f gives res. Q is what the loop
   promises when it ends. *)
Lemma pick_dec_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (res: Heur * option Lit) (h: Heur) (f: nat)
  (Q: temp_env -> mem -> outcome -> Prop) (le: temp_env) (m m1: mem),
  le ! _s = Some (sptr S) -> le ! _fuel = Some (vint (Z.of_nat (Datatypes.S f))) ->
  (Datatypes.S f <= N)%nat -> pick (vals x) h f = res ->
  RepL m1 S N lss (with_heur x h) lims lt -> Mem.unchanged_on (HeurFrame S) m m1 ->
  Exec ge le m1 pick_dec
    (LoopK Peano.lt (@PickInv lt m S N lss x lims res) Q (Datatypes.S f)).
Proof.
  intros S N lss x lims res h f Q le m m1 Hs Hfuel Hf Hres HRep1 Hframe.
  pose proof (r_n _ _ _ _ _ _ _ HRep1) as HN.
  assert (Hsub: Int.sub (Int.repr (Z.of_nat (Datatypes.S f))) (Int.repr 1)
                = Int.repr (Z.of_nat f)).
  { rewrite sub_repr. f_equal. lia. }
  unfold pick_dec, f_pick. cbn [fn_body drop_stmts first_stmt loop_body Swhile].
  (* fuel--; and the loop goes on *)
  run. ints. apply loopk_next with f.
  - lia.
  - constructor.
    + tmp.
    + tmp.
    + lia.
    + exists h. split.
      * assumption.
      * assumption.
    + assumption.
Qed.

(* What pick promises for the result res of the model, in the memory m' with the result
   v, from the memory m of the call (its postcondition). *)
Definition PickPost {lt: list Lit} (m: mem) (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (res: Heur * option Lit) (m': mem) (v: val): Prop :=
  match res with
  | (h, ol) => RepL m' S N lss (with_heur x h) lims lt /\ v = vint (enc_lit ol) /\
               Mem.unchanged_on (HeurFrame S) m m'
  end.

(* The statement after the loop of pick, return -1, and what follows the loop: it and
   the end of pick with PickPost. *)
Definition pick_ret: statement := drop_stmts 2 (fn_body f_pick).

Definition PickExit {lt: list Lit} (m: mem) (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (res: Heur * option Lit):
  temp_env -> mem -> outcome -> Prop :=
  SeqK ge pick_ret (Returns f_pick (@PickPost lt m S N lss x lims res)).

(* The statements of the loop of pick after heap_pop. *)
Definition pick_rest: statement :=
  drop_stmts 3 (loop_body (first_stmt (drop_stmts 1 (fn_body f_pick)))).

(* The loop of pick after heap_pop took atom a out, leaving the heuristic h1, with
   fuel f + 1, for which the model gives res:

     {{ RepL m2 S N lss (with_heur x h1) lims lt /\ a < N }}
       int l = s->dlit[a];
       if (l >= 0) {
     {{ dlit h1 a = Some l' /\ l = key l' }}
         if (lit_value(s, l) == 0) return l;                         (lit_value_correct)
     {{ l' is unassigned: res = (h1, Some l'), and the result is l: PickPost res }}
       }
     {{ the model goes on: pick (vals x) h1 f = res }}
       fuel--;                                                       (pick_dec_correct)
     {{ PickInv res f }}                                                             *)
Lemma pick_rest_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (res: Heur * option Lit) (h1: Heur) (a f: nat)
  (le: temp_env) (m m2: mem),
  RepL m2 S N lss (with_heur x h1) lims lt -> (a < N)%nat -> (Datatypes.S f <= N)%nat ->
  match tget (dlit h1) a with
  | Some l => if lookup_undef (vals x) l then (h1, Some l) else pick (vals x) h1 f
  | None   => pick (vals x) h1 f
  end = res ->
  Mem.unchanged_on (HeurFrame S) m m2 ->
  le ! _s = Some (sptr S) -> le ! _fuel = Some (vint (Z.of_nat (Datatypes.S f))) ->
  le ! _b = Some (vint (Z.of_nat a)) ->
  Exec ge le m2 pick_rest (LoopK Peano.lt (@PickInv lt m S N lss x lims res)
    (@PickExit lt m S N lss x lims res) (Datatypes.S f)).
Proof.
  intros S N lss x lims res h1 a f le m m2 HRep2 Ha Hf Hres Hframe2 Hs Hfuel Hb.
  pose proof (r_n _ _ _ _ _ _ _ HRep2) as HN.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep2) as Hnd.
  pose proof (r_dlit _ _ _ _ _ _ _ HRep2) as Fdlit.
  pose proof (a_dlit _ _ _ _ _ _ _ HRep2) as Adlit.
  pose proof (ho_dlit _ _ (r_heur _ _ _ _ _ _ _ HRep2) a) as Hdl.
  cbn [with_heur hr] in Adlit, Hdl.
  unfold pick_rest, f_pick. cbn [fn_body drop_stmts first_stmt loop_body Swhile].
  (* int l = s->dlit[a]; *)
  run. destruct (tget (dlit h1) a) as [l|] eqn:Hd.
  - (* a literal l: if (l >= 0) ... *)
    assert (Hl: (extract l < N)%nat).
    { apply (Hdl l Ha). reflexivity. }
    pose proof (key_small l N Hl HN) as Hkey.
    cbn [enc_lit]. eapply (exec_if_cmp _ _ _ Cge).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + unfold Small. lia.
    + unfold Small. lia.
    + replace (zcmp Cge (key l) 0) with true
        by (symmetry; cbn [zcmp]; apply Z.leb_le; lia).
      (* if (lit_value(s, l) == 0) return l; *)
      cbv beta iota. run. call lit_value_fun. eapply call_weaken.
      { apply (lit_value_correct (lt := lt) S N lss (with_heur x h1) lims l). split.
        - apply HRep2.
        - assumption. }
      intros m3 v3 [-> ->]. normal. change (vals (with_heur x h1)) with (vals x).
      eapply (exec_if_cmp _ _ _ Ceq).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * apply enc_small.
      * unfold Small. lia.
      * cbn [zcmp]. rewrite enc_undef. destruct (lookup_undef (vals x) l) eqn:Hu.
        -- (* unassigned: return l, as the model does *)
           cbv beta iota. eapply exec_return.
           ++ ev.
           ++ ret. exists (vint (key l)). split.
              ** apply result_int.
              ** unfold PickPost. rewrite <- Hres. split.
                 --- apply HRep2.
                 --- split.
                     +++ reflexivity.
                     +++ assumption.
        -- (* assigned: the loop goes on *)
           cbv beta iota. apply exec_skip. normal.
           apply (pick_dec_correct S N lss x lims res h1 f).
           ++ tmp.
           ++ tmp.
           ++ assumption.
           ++ assumption.
           ++ apply HRep2.
           ++ assumption.
  - (* no literal: the loop goes on *)
    cbn [enc_lit]. eapply (exec_if_cmp _ _ _ Cge).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + unfold Small. lia.
    + unfold Small. lia.
    + replace (zcmp Cge (-1) 0) with false by reflexivity.
      cbv beta iota. apply exec_skip. normal.
      apply (pick_dec_correct S N lss x lims res h1 f).
      * tmp.
      * tmp.
      * assumption.
      * assumption.
      * apply HRep2.
      * assumption.
Qed.

(* pick takes atoms out of the heap, at most N of them, until one has a literal to decide
   on that is unassigned, and returns it, or -1. Writing res for pick (vals x) (hr x) N
   and h for the heuristic of the invariant:

     {{ RepL m S N lss x lims lt }}
       int fuel = s->nv;
     {{ PickInv res N }}
       while (fuel > 0) {
     {{ PickInv res fuel /\ fuel > 0 }}
         if (s->hsize <= 0) return -1;
     {{ PickInv res fuel /\ hsize h > 0 }}
         int b = heap_pop(s);                                         (heap_pop_correct)
     {{ RepL with fst (heap_pop h) =: h1 /\ b = snd (heap_pop h) }}
         int l = s->dlit[b];
         if (l >= 0) {
     {{ RepL with h1 /\ l = key l' for dlit h1 b = Some l' }}
           if (lit_value(s, l) == 0) return l;                       (lit_value_correct)
         }
     {{ PickInv res (fuel - 1), as the model goes on with h1 }}
         fuel--;                                                     (pick_dec_correct)
       }
     {{ PickInv res 0: res is (h, None) }}
       return -1;
     {{ RepL m' S N lss (with_heur x (fst res)) lims lt /\ result = enc_lit (snd res) }}

   The loop ends: fuel decreases. *)
Lemma pick_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat),
  {{ m | RepL m S N lss x lims lt }}
    f_pick(sptr S)
  {{ m', v | match pick (vals x) (hr x) N with
             | (h, ol) => RepL m' S N lss (with_heur x h) lims lt /\
                          v = vint (enc_lit ol) /\
                          Mem.unchanged_on (HeurFrame S) m m'
             end }}.
Proof.
  intros S N lss x lims m HRep.
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_nv _ _ _ _ _ _ _ HRep) as Fnv.
  set (res := pick (vals x) (hr x) N).
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_pick. cbn [fn_body fn_return].
    (* int fuel = s->nv; *)
    run. clear Fnv.
    change (SeqK ge _ _) with (@PickExit lt m S N lss x lims res). unfold Swhile.
    apply exec_loop with (R := Peano.lt) (I := @PickInv lt m S N lss x lims res)
      (a := N).
    + apply lt_wf.
    + intros f le1 m1 HI. destruct HI as [Hs Hfuel Hf (h & Hres & HRep1) Hframe].
      pose proof (r_nodup _ _ _ _ _ _ _ HRep1) as Hnd.
      pose proof (r_heur _ _ _ _ _ _ _ HRep1) as Hok. cbn [with_heur hr] in Hok.
      apply exec_seq.
      (* if (fuel > 0) ... else break; *)
      eapply (exec_if_cmp _ _ _ Cgt).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * destruct f as [|f].
        -- (* fuel = 0: break; return -1, as the model gives (h, None) *)
           replace (zcmp Cgt (Z.of_nat 0) 0) with false by reflexivity.
           cbv beta iota. apply exec_break. abrupt. apply loopk_break.
           unfold PickExit. normal. unfold pick_ret, f_pick. cbn [fn_body drop_stmts].
           eapply exec_return.
           ++ ev.
           ++ exists (vint (-1)). split.
              ** apply result_int.
              ** unfold PickPost. cbn [pick] in Hres. rewrite <- Hres. split.
                 --- apply HRep1.
                 --- split.
                     +++ reflexivity.
                     +++ assumption.
        -- replace (zcmp Cgt (Z.of_nat (Datatypes.S f)) 0) with true
             by (symmetry; cbn [zcmp]; apply Z.ltb_lt; lia).
           cbn [pick] in Hres.
           pose proof (r_hsize _ _ _ _ _ _ _ HRep1) as Fhsize.
           cbn [with_heur hr] in Fhsize.
           pose proof (ho_hsize _ _ Hok) as Hhs.
           (* if (s->hsize <= 0) return -1; *)
           cbv beta iota. run. eapply (exec_if_cmp _ _ _ Cle).
           ++ ev.
           ++ ev.
           ++ reflexivity.
           ++ reflexivity.
           ++ unfold Small. lia.
           ++ unfold Small. lia.
           ++ destruct (Nat.eq_dec (hsize h) 0) as [Hempty | Hsize].
              ** (* the heap is empty: return -1, as the model gives (h, None) *)
                 replace (zcmp Cle (Z.of_nat (hsize h)) 0) with true
                   by (symmetry; cbn [zcmp]; apply Z.leb_le; lia).
                 replace (hsize h <=? 0)%nat with true in Hres
                   by (symmetry; apply Nat.leb_le; lia).
                 cbv beta iota. eapply exec_return.
                 --- ev.
                 --- ret. exists (vint (-1)). split.
                     +++ apply result_int.
                     +++ unfold PickPost. rewrite <- Hres. split.
                         *** apply HRep1.
                         *** split.
                             ---- reflexivity.
                             ---- assumption.
              ** (* int b = heap_pop(s); *)
                 replace (zcmp Cle (Z.of_nat (hsize h)) 0) with false
                   by (symmetry; cbn [zcmp]; apply Z.leb_gt; lia).
                 replace (hsize h <=? 0)%nat with false in Hres
                   by (symmetry; apply Nat.leb_gt; lia).
                 assert (Hb: (snd (heap_pop h) < N)%nat).
                 { rewrite heap_pop_snd. apply (ho_heap _ _ Hok). lia. }
                 cbv beta iota. run. call heap_pop_fun. eapply call_weaken.
                 { apply (heap_pop_correct (lt := lt) S N lss (with_heur x h) lims).
                   split.
                   - assumption.
                   - cbn [with_heur hr]. lia. }
                 intros m2 v2 (HRep2 & -> & Hun2). normal. keep_mem m2.
                 change (hr (with_heur x h)) with h in HRep2 |- *.
                 destruct (heap_pop h) as [h1 a] eqn:Hpop.
                 cbn [fst snd] in HRep2, Hb |- *.
                 cbv beta iota in Hres.
                 assert (Hframe2: Mem.unchanged_on (HeurFrame S) m m2).
                 { apply (Mem.unchanged_on_trans _ m m1 m2).
                   - assumption.
                   - assumption. }
                 eapply exec_set.
                 --- ev.
                 --- (* the rest of the loop (pick_rest_correct) *)
                     normal. apply (pick_rest_correct S N lss x lims res h1 a f).
                     +++ apply HRep2.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
    + (* The invariant holds at N. *)
      constructor.
      * tmp.
      * tmp.
      * lia.
      * exists (hr x). split.
        -- reflexivity.
        -- destruct x. apply HRep.
      * apply Mem.unchanged_on_refl.
Qed.

Lemma pick_fun: exists (b: block),
  Genv.find_symbol ge _pick = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_pick).
Proof. apply find_fun. reflexivity. Qed.
