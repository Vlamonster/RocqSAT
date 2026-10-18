(* pick takes atoms out of the heap until the literal to decide on of one is unassigned
   (pick). *)
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
From RocqSAT.refinement Require Import Heur.
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement Require Import Analysis.
From RocqSAT.refinement Require Import Step.
From RocqSAT.refinement.c Require Import Arrays.
From RocqSAT.refinement.c Require Import Logic.
From RocqSAT.refinement.c Require Import Common.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Rep.
From RocqSAT.refinement.c Require Import RepHeur.
From RocqSAT.refinement.c Require Import LitValue.
From RocqSAT.refinement.c Require Import HeapPop.

(* The invariant of the loop of pick at fuel f, for the memory m of the call and the
   result res of the model: the temporaries hold s and f, f is at most N, the memory
   represents x with a heuristic h for which pick with fuel f gives res, and only the
   heuristic is written. *)
Record PickInv {m: mem} {sh: Shape} {N: nat} {lss: list (list Lit)}
  {x: Ctx} {res: Heur * option Lit} {f: nat} {le: temp_env}
  {m1: mem}: Prop := {
  pi_s: le ! _s = Some (sptr sh);
  pi_fuel: le ! _fuel = Some (vnat f);
  pi_le: (f <= N)%nat;
  pi_heur: exists (h: Heur), pick (vals x) h f = res /\
    RepL m1 sh N lss (x <| hr := h |>);
  pi_frame: Mem.unchanged_on (HeurFrame sh) m m1;
}.
Arguments PickInv : clear implicits.

(* The last statement of the loop of pick: fuel--. *)
Definition pick_dec: statement :=
  drop_stmts 5 (loop_body (first_stmt (drop_stmts 1 (fn_body f_pick)))).

(* fuel--, once the atom taken out did not give a literal: the loop goes on with fuel f
   for the heuristic h, from which pick with fuel f gives res. Q is what the loop
   promises when it ends. *)
Lemma pick_dec_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (res: Heur * option Lit) (h: Heur) (f: nat)
  (Q: temp_env -> mem -> outcome -> Prop) (le: temp_env) (m m1: mem),
  le ! _s = Some (sptr sh) -> le ! _fuel = Some (vnat (S f)) ->
  (S f <= N)%nat -> pick (vals x) h f = res ->
  RepL m1 sh N lss (x <| hr := h |>) -> Mem.unchanged_on (HeurFrame sh) m m1 ->
  Exec ge le m1 pick_dec
    (LoopK Peano.lt (PickInv m sh N lss x res) Q (S f)).
Proof.
  intros sh N lss x res h f Q le m m1 Hs Hfuel Hf Hres HRep1 Hframe.
  pose proof (r_n HRep1) as HN.
  assert (Hsub: Int.sub (Int.repr (Z.of_nat (S f))) (Int.repr 1)
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

(* What pick promises for the result res = (h, ol) of the model, from the memory m of
   the call: the heuristic h is in memory, and the result encodes ol. *)
Definition PickPost (m: mem) (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (res: Heur * option Lit) (m': mem) (v: val): Prop :=
  match res with
  | (h, ol) => HeurPost sh N lss x m h m' /\ v = vint (enc_lit ol)
  end.

(* The statement after the loop of pick, return -1, and what follows the loop: it and
   the end of pick with PickPost. *)
Definition pick_ret: statement := drop_stmts 2 (fn_body f_pick).

Definition PickExit (m: mem) (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (res: Heur * option Lit):
  temp_env -> mem -> outcome -> Prop :=
  SeqK ge pick_ret (Returns f_pick (PickPost m sh N lss x res)).

(* What pick gives after heap_pop took atom a out, leaving h1, with fuel f left: the
   literal of a if it is unassigned in v, or else what the next atoms give. *)
Definition pick_next (v: Values) (h1: Heur) (a f: nat): Heur * option Lit :=
  match tget (dlit h1) a with
  | Some l => if lookup_undef v l then (h1, Some l) else pick v h1 f
  | None   => pick v h1 f
  end.

(* The statements of the loop of pick after heap_pop. *)
Definition pick_rest: statement :=
  drop_stmts 3 (loop_body (first_stmt (drop_stmts 1 (fn_body f_pick)))).

(* The loop of pick after heap_pop took atom a out, leaving the heuristic h1, with
   fuel f + 1, for which the model gives res:

     {{ RepL m2 sh N lss (x <| hr := h1 |>) /\ a < N }}
       int l = s->dlit[a];
       if (l >= 0) {
     {{ dlit h1 a = Some l' /\ l = key l' }}
         if (lit_value(s, l) == 0) return l;                         (lit_value_correct)
     {{ l' is unassigned: res = (h1, Some l'), and the result is l: PickPost res }}
       }
     {{ the model goes on: pick (vals x) h1 f = res }}
       fuel--;                                                       (pick_dec_correct)
     {{ PickInv res f }}                                                             *)
Lemma pick_rest_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (res: Heur * option Lit) (h1: Heur) (a f: nat)
  (le: temp_env) (m m2: mem),
  RepL m2 sh N lss (x <| hr := h1 |>) -> (a < N)%nat -> (S f <= N)%nat ->
  pick_next (vals x) h1 a f = res ->
  Mem.unchanged_on (HeurFrame sh) m m2 ->
  le ! _s = Some (sptr sh) -> le ! _fuel = Some (vnat (S f)) ->
  le ! _b = Some (vnat a) ->
  Exec ge le m2 pick_rest (LoopK Peano.lt (PickInv m sh N lss x res)
    (PickExit m sh N lss x res) (S f)).
Proof.
  intros sh N lss x res h1 a f le m m2 HRep2 Ha Hf Hres Hframe2 Hs Hfuel Hb.
  unfold pick_next in Hres.
  pose proof (r_n HRep2) as HN.
  pose proof (r_nodup HRep2) as Hnd.
  pose proof (r_dlit HRep2) as Fdlit.
  pose proof (a_dlit HRep2) as Adlit.
  pose proof (ho_dlit (r_heur HRep2) a) as Hdl.
  cbn [set_hr hr] in Adlit, Hdl.
  unfold pick_rest, f_pick. cbn [fn_body drop_stmts first_stmt loop_body Swhile].
  (* int l = s->dlit[a]; *)
  run. destruct (tget (dlit h1) a) as [l|] eqn:Hd.
  - (* a literal l: if (l >= 0) ... *)
    assert (Hl: (extract l < N)%nat).
    { apply (Hdl l Ha). reflexivity. }
    pose proof (key_small l N Hl HN) as Hkey.
    cbn [enc_lit]. eapply exec_if_ge.
    + ev.
    + ev.
    + reflexivity.
    + lia.
    + (* if (lit_value(s, l) == 0) return l; *)
      intros Hpos. run.
      eapply (exec_call_triple lit_value_fun
                (lit_value_correct sh N lss (x <| hr := h1 |>) l)).
      * reflexivity.
      * evs.
      * split.
        -- apply HRep2.
        -- assumption.
      * intros m3 v3 [-> ->]. normal. change (vals (x <| hr := h1 |>)) with (vals x).
        eapply exec_if_eq.
        -- ev.
        -- ev.
        -- reflexivity.
        -- split.
           ++ apply enc_small.
           ++ lia.
        -- (* unassigned: return l, as the model does *)
           intros Hz. assert (Hu: lookup_undef (vals x) l = true).
           { rewrite <- enc_undef. now apply Z.eqb_eq. }
           rewrite Hu in Hres. eapply exec_return.
           ++ ev.
           ++ ret. exists (vint (key l)). split.
              ** apply result_int.
              ** unfold PickPost. rewrite <- Hres. split.
                 --- split.
                     +++ apply HRep2.
                     +++ assumption.
                 --- reflexivity.
        -- (* assigned: the loop goes on *)
           intros Hz. assert (Hu: lookup_undef (vals x) l = false).
           { rewrite <- enc_undef. now apply Z.eqb_neq. }
           rewrite Hu in Hres. apply exec_skip. normal.
           apply (pick_dec_correct sh N lss x res h1 f).
           ++ tmp.
           ++ tmp.
           ++ assumption.
           ++ assumption.
           ++ apply HRep2.
           ++ assumption.
    + (* a literal has a key of at least 0 *)
      intros Hneg. lia.
  - (* no literal: the loop goes on *)
    cbn [enc_lit]. eapply exec_if_ge.
    + ev.
    + ev.
    + reflexivity.
    + lia.
    + (* -1 is not at least 0 *)
      intros Hpos. lia.
    + intros Hneg. apply exec_skip. normal.
      apply (pick_dec_correct sh N lss x res h1 f).
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

     {{ RepL m sh N lss x }}
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
     {{ RepL m' sh N lss (x <| hr := fst res |>) /\ result = enc_lit (snd res) }}

   The loop ends: fuel decreases. *)
Lemma pick_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx),
  {{ m | RepL m sh N lss x }}
    f_pick(sptr sh)
  {{ m', v | PickPost m sh N lss x (pick (vals x) (hr x) N) m' v }}.
Proof.
  intros sh N lss x m HRep.
  pose proof (r_n HRep) as HN.
  pose proof (r_nv HRep) as Fnv.
  set (res := pick (vals x) (hr x) N).
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_pick. cbn [fn_body fn_return].
    (* int fuel = s->nv; *)
    run. clear Fnv.
    change (SeqK ge _ _) with (PickExit m sh N lss x res). unfold Swhile.
    apply exec_loop with (R := Peano.lt) (I := PickInv m sh N lss x res)
      (a := N).
    + apply lt_wf.
    + intros f le1 m1 HI. destruct HI as [Hs Hfuel Hf (h & Hres & HRep1) Hframe].
      pose proof (r_nodup HRep1) as Hnd.
      pose proof (r_heur HRep1) as Hok. cbn [set_hr hr] in Hok.
      apply exec_seq.
      (* if (fuel > 0) ... else break; *)
      eapply exec_if_gt.
      * ev.
      * ev.
      * reflexivity.
      * lia.
      * intros Hpos. destruct f as [|f].
        -- (* fuel 0 is not positive *)
           lia.
        -- cbn [pick] in Hres.
           pose proof (r_hsize HRep1) as Fhsize.
           cbn [set_hr hr] in Fhsize.
           pose proof (ho_hsize Hok) as Hhs.
           (* if (s->hsize <= 0) return -1; *)
           run. eapply exec_if_le.
           ++ ev.
           ++ ev.
           ++ reflexivity.
           ++ lia.
           ++ (* the heap is empty: return -1, as the model gives (h, None) *)
              intros Hempty. replace (hsize h <=? 0)%nat with true in Hres
                by (symmetry; apply Nat.leb_le; lia).
              eapply exec_return.
              ** ev.
              ** ret. exists (vint (-1)). split.
                 --- apply result_int.
                 --- unfold PickPost. rewrite <- Hres. split.
                     +++ split.
                         *** apply HRep1.
                         *** assumption.
                     +++ reflexivity.
           ++ (* int b = heap_pop(s); *)
              intros Hsize. replace (hsize h <=? 0)%nat with false in Hres
                by (symmetry; apply Nat.leb_gt; lia).
              assert (Hb: (snd (heap_pop h) < N)%nat).
              { rewrite heap_pop_snd. apply (ho_heap Hok). lia. }
              run.
              eapply (exec_call_triple heap_pop_fun
                        (heap_pop_correct sh N lss (x <| hr := h |>))).
              ** reflexivity.
              ** evs.
              ** split.
                 --- apply HRep1.
                 --- cbn [set_hr hr]. lia.
              ** intros m2 v2 ((HRep2 & Hun2) & ->). normal. keep_mem m2.
                 change (hr (x <| hr := h |>)) with h in HRep2 |- *.
                 destruct (heap_pop h) as [h1 a] eqn:Hpop.
                 cbn [fst snd] in HRep2, Hb |- *.
                 cbv beta iota in Hres.
                 assert (Hframe2: Mem.unchanged_on (HeurFrame sh) m m2).
                 { apply (Mem.unchanged_on_trans _ m m1 m2).
                   + assumption.
                   + assumption. }
                 eapply exec_set.
                 --- ev.
                 --- (* the rest of the loop (pick_rest_correct) *)
                     normal. apply (pick_rest_correct sh N lss x res h1 a f).
                     +++ apply HRep2.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
      * (* fuel = 0: break; return -1, as the model gives (h, None) *)
        intros Hle. assert (Hf0: f = 0%nat) by lia. subst f.
        apply exec_break. abrupt. apply loopk_break.
        unfold PickExit. normal. unfold pick_ret, f_pick. cbn [fn_body drop_stmts].
        eapply exec_return.
        -- ev.
        -- exists (vint (-1)). split.
           ++ apply result_int.
           ++ unfold PickPost. cbn [pick] in Hres. rewrite <- Hres. split.
              ** split.
                 --- apply HRep1.
                 --- assumption.
              ** reflexivity.
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

Lemma pick_fun: FunAt _pick f_pick.
Proof. apply find_fun. reflexivity. Qed.
