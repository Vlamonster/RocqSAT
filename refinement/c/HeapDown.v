(* heap_down moves the atom at a heap position down while a child has a higher activity
   (heap_down). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Ctypesdefs Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Heur Propagate Step.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep RepHeur Rescale HeapUp.
Import ListNotations.

(* The position k + 1 after the one in temporary id, as C computes it. *)
Lemma eval_succ: forall (le: temp_env) (m: mem) (id: ident) (k: nat),
  le ! id = Some (vint (Z.of_nat k)) ->
  eval_expr ge empty_env le m
    (Ebinop Oadd (Etempvar id tint) (Econst_int (Int.repr 1) tint) tint)
    (vint (Z.of_nat (Datatypes.S k))).
Proof.
  intros le m id k Hk. eapply eval_Ebinop.
  - apply eval_Etempvar. apply Hk.
  - apply eval_Econst_int.
  - replace (Z.of_nat (Datatypes.S k)) with (Z.of_nat k + 1) by lia.
    unfold vint. rewrite <- add_repr. cbn -[Int.add Int.repr].
    unfold sem_binarith, sem_cast, tint. cbn -[Int.add Int.repr]. cbv [Archi.ptr64].
    cbn -[Int.add Int.repr]. reflexivity.
Qed.

(* The first child 2i + 1 of the position i, as C computes it. *)
Lemma eval_left: forall (le: temp_env) (m: mem) (i: nat),
  le ! _i = Some (vint (Z.of_nat i)) ->
  eval_expr ge empty_env le m
    (Ebinop Oadd (Ebinop Omul (Econst_int (Int.repr 2) tint) (Etempvar _i tint) tint)
      (Econst_int (Int.repr 1) tint) tint)
    (vint (Z.of_nat (Datatypes.S (2 * i)))).
Proof.
  intros le m i Hi. eapply eval_Ebinop.
  - eapply eval_Ebinop.
    + apply eval_Econst_int.
    + apply eval_Etempvar. apply Hi.
    + reflexivity.
  - apply eval_Econst_int.
  - replace (Z.of_nat (Datatypes.S (2 * i))) with (2 * Z.of_nat i + 1) by lia.
    unfold vint. rewrite <- add_repr, <- mul_repr. cbn -[Int.add Int.mul Int.repr].
    unfold sem_binarith, sem_cast, tint. cbn -[Int.add Int.mul Int.repr].
    cbv [Archi.ptr64]. cbn -[Int.add Int.mul Int.repr]. reflexivity.
Qed.

(* The child heap_down looks at is a position of the heap. *)
Lemma child_lt: forall (h: Heur) (n i: nat), (Datatypes.S (2 * i) < n)%nat ->
  (child h n i < n)%nat.
Proof.
  intros h n i Hi. unfold child.
  destruct (Nat.ltb_spec (Datatypes.S (Datatypes.S (2 * i))) n).
  - destruct (_ <? _)%Z.
    + assumption.
    + assumption.
  - assumption.
Qed.

(* The invariant of the loop of heap_down at fuel, for the memory m of the call and the
   atom a moved down from position i0, of the n = hsize (hr x) positions: the
   temporaries hold s, a, n, fuel and a position i below N, the memory m1 represents x
   with a heuristic h from which down_loop gives what it gives from the start (the loop
   follows the recursion of down_loop), and m1 is m but for the heuristic. *)
Record DownInv (m: mem) (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (lt: list Lit) (i0: nat) (fuel: nat) (le: temp_env) (m1: mem):
  Prop := {
  dni_s: le ! _s = Some (sptr S);
  dni_a: le ! _a = Some (vint (Z.of_nat (atom_at (hr x) i0)));
  dni_n: le ! _n = Some (vint (Z.of_nat (hsize (hr x))));
  dni_fuel: le ! _fuel = Some (vint (Z.of_nat fuel));
  dni_fuel_le: (fuel <= N)%nat;
  dni_pos: exists (h: Heur) (i: nat),
    le ! _i = Some (vint (Z.of_nat i)) /\ (i < N)%nat /\
    down_loop h (hsize (hr x)) (atom_at (hr x) i0) i fuel
    = down_loop (hr x) (hsize (hr x)) (atom_at (hr x) i0) i0 (hsize (hr x)) /\
    RepL m1 S N lss (with_heur x h) lims lt;
  dni_frame: Mem.unchanged_on (HeurFrame S) m m1;
}.

(* What heap_down promises, for the memory m of the call. *)
Definition down_post (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (lt: list Lit) (i0: nat) (m: mem): mem -> val -> Prop :=
  fun (m': mem) (_: val) =>
    RepL m' S N lss (with_heur x (heap_down (hr x) i0)) lims lt /\
    Mem.unchanged_on (HeurFrame S) m m'.

(* The statements of heap_down after its loop: heap[i] = a; hpos[a] = i. *)
Definition heap_down_end: statement := drop_stmts 4 (fn_body f_heap_down).

(* The end of heap_down, once the loop left the heuristic h and position i, which is
   what down_loop gives:

     {{ RepL (with_heur x h) /\ down_loop (hr x) n a i0 n = (h, i) }}
       s->heap[i] = a;
       s->hpos[a] = i;                                         (place_end_correct)
     {{ RepL (with_heur x (place h i a)), and place h i a = heap_down (hr x) i0 }} *)
Lemma heap_down_end_correct {lt: list Lit}: forall (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (i0: nat) (h: Heur) (i: nat)
  (le: temp_env) (m m1: mem),
  RepL m1 S N lss (with_heur x h) lims lt -> (i < N)%nat ->
  (atom_at (hr x) i0 < N)%nat ->
  down_loop (hr x) (hsize (hr x)) (atom_at (hr x) i0) i0 (hsize (hr x)) = (h, i) ->
  Mem.unchanged_on (HeurFrame S) m m1 ->
  le ! _s = Some (sptr S) -> le ! _i = Some (vint (Z.of_nat i)) ->
  le ! _a = Some (vint (Z.of_nat (atom_at (hr x) i0))) ->
  Exec ge le m1 heap_down_end
    (Returns f_heap_down (down_post S N lss x lims lt i0 m)).
Proof.
  intros S N lss x lims i0 h i le m m1 HRep1 Hi Ha Hres Hun1 Hs Hi' Ha'.
  unfold down_post, heap_down. fold (atom_at (hr x) i0). rewrite Hres.
  apply (place_end_correct (lt := lt) S N lss x lims h i (atom_at (hr x) i0)).
  - reflexivity.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

(* What the choice of the child keeps: the memory, and the temporaries but c, which
   holds the child c. *)
Record ChildPost (le: temp_env) (m1: mem) (c: nat) (le': temp_env) (m': mem)
  (out: outcome): Prop := {
  cp_out: out = Out_normal;
  cp_mem: m' = m1;
  cp_c: le' ! _c = Some (vint (Z.of_nat c));
  cp_s: le' ! _s = le ! _s;
  cp_a: le' ! _a = le ! _a;
  cp_i: le' ! _i = le ! _i;
  cp_n: le' ! _n = le ! _n;
  cp_fuel: le' ! _fuel = le ! _fuel;
}.

(* The statements of the loop of heap_down from the choice of the child on. *)
Definition down_rest: statement :=
  drop_stmts 3 (loop_body (first_stmt (drop_stmts 3 (fn_body f_heap_down)))).

(* The choice of the child. *)
Definition child_stmt: statement := first_stmt down_rest.

(* The choice of the child of position i of the n positions, with 2i + 1 < n: the
   second child if it is a position and more active than the first.

     {{ RepL (with_heur x h) /\ c = 2i + 1 < n }}
       if (c + 1 < n) {
         if (s->act[s->heap[c + 1]] > s->act[s->heap[c]]) c = c + 1;
       }
     {{ ChildPost: c = child h n i }}                                             *)
Lemma child_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (h: Heur) (n i: nat) (le: temp_env) (m1: mem),
  RepL m1 S N lss (with_heur x h) lims lt -> (Datatypes.S (2 * i) < n)%nat ->
  (n <= N)%nat -> le ! _s = Some (sptr S) ->
  le ! _c = Some (vint (Z.of_nat (Datatypes.S (2 * i)))) ->
  le ! _n = Some (vint (Z.of_nat n)) ->
  Exec ge le m1 child_stmt (ChildPost le m1 (child h n i)).
Proof.
  intros S N lss x lims h n i le m1 HRep1 Hc Hn Hs Hc' Hn'.
  pose proof (r_n _ _ _ _ _ _ _ HRep1) as HN.
  pose proof (r_heur _ _ _ _ _ _ _ HRep1) as Hok1. cbn [with_heur hr] in Hok1.
  unfold child_stmt, down_rest, f_heap_down.
  cbn [fn_body drop_stmts first_stmt loop_body Swhile].
  (* if (c + 1 < n) ... *)
  apply (exec_if_cmp _ _ _ Clt _ _ (Z.of_nat (Datatypes.S (Datatypes.S (2 * i))))
           (Z.of_nat n)).
  - apply eval_succ. assumption.
  - ev.
  - reflexivity.
  - reflexivity.
  - unfold Small. lia.
  - unfold Small. lia.
  - cbn [zcmp]. unfold child.
    destruct (Nat.ltb_spec (Datatypes.S (Datatypes.S (2 * i))) n) as [Hlt | Hge].
    + (* two children: compare their activities *)
      replace (Z.of_nat (Datatypes.S (Datatypes.S (2 * i))) <? Z.of_nat n) with true
        by (symmetry; apply Z.ltb_lt; lia).
      assert (Hsucc: Int.add (Int.repr (Z.of_nat (Datatypes.S (2 * i)))) (Int.repr 1)
                     = Int.repr (Z.of_nat (Datatypes.S (Datatypes.S (2 * i))))).
      { rewrite add_repr. f_equal. lia. }
      assert (Hleft: (tget (heap h) (Datatypes.S (2 * i)) < N)%nat).
      { apply (ho_heap _ _ Hok1). lia. }
      assert (Hright: (tget (heap h) (Datatypes.S (Datatypes.S (2 * i))) < N)%nat).
      { apply (ho_heap _ _ Hok1). lia. }
      pose proof (ho_act _ _ Hok1 _ Hleft) as Hactl.
      pose proof (ho_act _ _ Hok1 _ Hright) as Hactr.
      unfold act_lim in Hactl, Hactr.
      change (2 ^ 30)%Z with 1073741824 in Hactl, Hactr.
      pose proof (r_heap _ _ _ _ _ _ _ HRep1) as Fheap.
      pose proof (a_heap _ _ _ _ _ _ _ HRep1) as Aheap.
      pose proof (r_act _ _ _ _ _ _ _ HRep1) as Fact.
      pose proof (a_act _ _ _ _ _ _ _ HRep1) as Aact.
      cbn [with_heur hr] in Aheap, Aact.
      run.
      (* if (s->act[s->heap[c + 1]] > s->act[s->heap[c]]) c = c + 1; *)
      eapply (exec_if_cmp _ _ _ Cgt).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * cbn [zcmp].
        destruct (Z.ltb_spec (tget (act h) (tget (heap h) (Datatypes.S (2 * i))))
                    (tget (act h) (tget (heap h) (Datatypes.S (Datatypes.S (2 * i))))))
          as [Hmore | Hless].
        -- (* the second child is more active: c = c + 1; *)
           apply exec_set with (vint (Z.of_nat (Datatypes.S (Datatypes.S (2 * i))))).
           ++ apply eval_succ. tmp.
           ++ constructor.
              ** reflexivity.
              ** reflexivity.
              ** tmp.
              ** tmp.
              ** tmp.
              ** tmp.
              ** tmp.
              ** tmp.
        -- (* the first child is at least as active *)
           apply exec_skip. constructor.
           ++ reflexivity.
           ++ reflexivity.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ tmp.
    + (* one child *)
      replace (Z.of_nat (Datatypes.S (Datatypes.S (2 * i))) <? Z.of_nat n) with false
        by (symmetry; apply Z.ltb_ge; lia).
      apply exec_skip. constructor.
      * reflexivity.
      * reflexivity.
      * assumption.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
Qed.

(* The statements of the loop of heap_down that move the child b at c up to i. *)
Definition down_move: statement :=
  drop_stmts 6 (loop_body (first_stmt (drop_stmts 3 (fn_body f_heap_down)))).

(* Moving the child b at c, more active than a, up to position i; the loop goes on from
   c with one less fuel:

     {{ DownInv (fuel + 1): heuristic h, position i /\ act a < act b }}
       s->heap[i] = b; s->hpos[b] = i; i = c; fuel--;               (move_correct)
     {{ DownInv fuel: heuristic place h i b, position c }}                        *)
Lemma down_move_correct {lt: list Lit}: forall (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (i0: nat) (h: Heur) (i c fuel: nat)
  (le: temp_env) (m m1: mem) (Q: temp_env -> mem -> outcome -> Prop),
  RepL m1 S N lss (with_heur x h) lims lt -> (i < N)%nat -> (c < N)%nat ->
  (Datatypes.S fuel <= N)%nat -> (tget (heap h) c < N)%nat ->
  down_loop (place h i (tget (heap h) c)) (hsize (hr x)) (atom_at (hr x) i0) c fuel
  = down_loop (hr x) (hsize (hr x)) (atom_at (hr x) i0) i0 (hsize (hr x)) ->
  Mem.unchanged_on (HeurFrame S) m m1 ->
  le ! _s = Some (sptr S) -> le ! _a = Some (vint (Z.of_nat (atom_at (hr x) i0))) ->
  le ! _n = Some (vint (Z.of_nat (hsize (hr x)))) ->
  le ! _i = Some (vint (Z.of_nat i)) -> le ! _c = Some (vint (Z.of_nat c)) ->
  le ! _b = Some (vint (Z.of_nat (tget (heap h) c))) ->
  le ! _fuel = Some (vint (Z.of_nat (Datatypes.S fuel))) ->
  Exec ge le m1 down_move
    (LoopK Peano.lt (DownInv m S N lss x lims lt i0) Q (Datatypes.S fuel)).
Proof.
  intros S N lss x lims i0 h i c fuel le m m1 Q HRep1 Hi Hc Hfle Hb Hres Hun1 Hs Ha Hn
    Hi' Hc' Hb' Hfuel.
  unfold down_move, f_heap_down. cbn [fn_body drop_stmts first_stmt loop_body Swhile].
  fold (move_stmt _c).
  apply (move_correct (lt := lt) S N lss x lims h _c i (tget (heap h) c) c fuel le m m1).
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - discriminate.
  - discriminate.
  - (* the loop goes on from c *)
    intros m3 HRep3 Hun3. apply loopk_next with fuel.
    + lia.
    + constructor.
      * tmp.
      * tmp.
      * tmp.
      * tmp.
      * lia.
      * exists (place h i (tget (heap h) c)), c. split.
        -- tmp.
        -- split.
           ++ assumption.
           ++ split.
              ** assumption.
              ** apply HRep3.
      * assumption.
Qed.

(* The loop body of heap_down from the choice of the child on, at position i with
   2i + 1 < n:

     {{ DownInv (fuel + 1): heuristic h, position i /\ c = 2i + 1 < n }}
       choose the child c;                                            (child_correct)
       int b = s->heap[c];
       if (s->act[b] <= s->act[a]) break;                         (heap_down_end_correct)
       s->heap[i] = b; s->hpos[b] = i; i = c; fuel--;            (down_move_correct)
     {{ DownInv fuel: heuristic place h i b, position c }}                        *)
Lemma down_rest_correct {lt: list Lit}: forall (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (i0: nat) (h: Heur) (i fuel: nat)
  (le: temp_env) (m m1: mem),
  RepL m1 S N lss (with_heur x h) lims lt -> (i < N)%nat ->
  (Datatypes.S (2 * i) < hsize (hr x))%nat -> (hsize (hr x) <= N)%nat ->
  (Datatypes.S fuel <= N)%nat -> (atom_at (hr x) i0 < N)%nat ->
  down_loop h (hsize (hr x)) (atom_at (hr x) i0) i (Datatypes.S fuel)
  = down_loop (hr x) (hsize (hr x)) (atom_at (hr x) i0) i0 (hsize (hr x)) ->
  Mem.unchanged_on (HeurFrame S) m m1 ->
  le ! _s = Some (sptr S) -> le ! _a = Some (vint (Z.of_nat (atom_at (hr x) i0))) ->
  le ! _n = Some (vint (Z.of_nat (hsize (hr x)))) ->
  le ! _i = Some (vint (Z.of_nat i)) ->
  le ! _c = Some (vint (Z.of_nat (Datatypes.S (2 * i)))) ->
  le ! _fuel = Some (vint (Z.of_nat (Datatypes.S fuel))) ->
  Exec ge le m1 down_rest
    (LoopK Peano.lt (DownInv m S N lss x lims lt i0)
       (SeqK ge heap_down_end (Returns f_heap_down (down_post S N lss x lims lt i0 m)))
       (Datatypes.S fuel)).
Proof.
  intros S N lss x lims i0 h i fuel le m m1 HRep1 Hi Hleft Hn Hfle Ha Hres Hun1 Hs Ha'
    Hn' Hi' Hc Hfuel.
  pose proof (r_n _ _ _ _ _ _ _ HRep1) as HN.
  pose proof (r_heur _ _ _ _ _ _ _ HRep1) as Hok1. cbn [with_heur hr] in Hok1.
  pose proof (child_lt h (hsize (hr x)) i Hleft) as Hchild.
  assert (Hb: (tget (heap h) (child h (hsize (hr x)) i) < N)%nat).
  { apply (ho_heap _ _ Hok1). lia. }
  pose proof (ho_act _ _ Hok1 _ Hb) as Hactb.
  pose proof (ho_act _ _ Hok1 _ Ha) as Hacta.
  unfold act_lim in Hactb, Hacta.
  change (2 ^ 30)%Z with 1073741824 in Hactb, Hacta.
  cbn [down_loop] in Hres.
  replace (hsize (hr x) <=? Datatypes.S (2 * i))%nat with false in Hres
    by (symmetry; apply Nat.leb_gt; lia).
  unfold down_rest. apply exec_seq.
  (* choose the child c *)
  apply exec_weaken with (Q := ChildPost le m1 (child h (hsize (hr x)) i)).
  - apply (child_correct (lt := lt) S N lss x lims).
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
  - intros le2 m2 out [-> -> Hc2 Hs2 Ha2 Hi2 Hn2 Hfuel2]. apply seqk_normal.
    rewrite <- Hs2 in Hs. rewrite <- Ha2 in Ha'. rewrite <- Hn2 in Hn'.
    rewrite <- Hi2 in Hi'. rewrite <- Hfuel2 in Hfuel. clear Hs2 Ha2 Hn2 Hi2 Hfuel2.
    pose proof (r_heap _ _ _ _ _ _ _ HRep1) as Fheap.
    pose proof (a_heap _ _ _ _ _ _ _ HRep1) as Aheap.
    pose proof (r_act _ _ _ _ _ _ _ HRep1) as Fact.
    pose proof (a_act _ _ _ _ _ _ _ HRep1) as Aact.
    cbn [with_heur hr] in Aheap, Aact.
    (* int b = s->heap[c]; if (s->act[b] <= s->act[a]) break; *)
    run.
    eapply (exec_if_cmp _ _ _ Cle).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + unfold Small. lia.
    + unfold Small. lia.
    + cbn [zcmp].
      destruct (Z.leb_spec (tget (act h) (tget (heap h) (child h (hsize (hr x)) i)))
                  (tget (act h) (atom_at (hr x) i0))) as [Hle | Hgt].
      * (* the child is not more active: break; and the end *)
        apply exec_break. abrupt.
        apply loopk_break. normal.
        apply (heap_down_end_correct (lt := lt) S N lss x lims i0 h i _ m m1).
        -- assumption.
        -- assumption.
        -- assumption.
        -- symmetry. assumption.
        -- assumption.
        -- tmp.
        -- tmp.
        -- tmp.
      * (* the child is more active: it moves up to i *)
        apply exec_skip. normal.
        apply (down_move_correct (lt := lt) S N lss x lims i0 h i
                 (child h (hsize (hr x)) i) fuel _ m m1).
        -- assumption.
        -- assumption.
        -- lia.
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- tmp.
        -- tmp.
        -- tmp.
        -- tmp.
        -- tmp.
        -- tmp.
        -- tmp.
Qed.

(* heap_down moves the atom a at position i0 down: while the more active child b at c
   of its position i has a higher activity, b moves up to i, at most hsize times; then
   a goes to the position left. Only the heuristic changes. Writing a for
   atom_at (hr x) i0 and n for hsize (hr x):

     {{ RepL m S N lss x lims lt /\ i0 < N }}
       int a = s->heap[i];
       int n = s->hsize;
       int fuel = n;
     {{ DownInv n: heuristic hr x, i = i0 }}
       while (fuel > 0) {
     {{ DownInv fuel: heuristic h, position i /\ fuel > 0 }}
         int c = 2 * i + 1;                                                 (eval_left)
         if (c >= n) break;
     {{ DownInv fuel /\ c = 2i + 1 < n }}
         choose the child c; int b = s->heap[c];
         if (s->act[b] <= s->act[a]) break;
         s->heap[i] = b; s->hpos[b] = i; i = c; fuel--;          (down_rest_correct)
     {{ DownInv (fuel - 1): heuristic place h i b, position c }}
       }
     {{ DownInv fuel: heuristic h, position i with the model's (h, i), at each break }}
       s->heap[i] = a;
       s->hpos[a] = i;                                       (heap_down_end_correct)
     {{ RepL (with_heur x (heap_down (hr x) i0)) /\ only the heuristic changed }}

   The loop ends: fuel decreases. *)
Lemma heap_down_correct {lt: list Lit}: forall (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (i: nat),
  {{ m | RepL m S N lss x lims lt /\ (i < N)%nat }}
    f_heap_down(sptr S, vint (Z.of_nat i))
  {{ m', v | RepL m' S N lss (with_heur x (heap_down (hr x) i)) lims lt /\
             Mem.unchanged_on (HeurFrame S) m m' }}.
Proof.
  intros S N lss x lims i0 m [HRep Hi0]. pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_heur _ _ _ _ _ _ _ HRep) as Hok.
  assert (Ha: (atom_at (hr x) i0 < N)%nat).
  { apply (ho_heap _ _ Hok). assumption. }
  pose proof (ho_hsize _ _ Hok) as Hhsize.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - fold (down_post S N lss x lims lt i0 m). unfold f_heap_down.
    cbn [fn_body fn_return].
    pose proof (r_heap _ _ _ _ _ _ _ HRep) as Fheap.
    pose proof (a_heap _ _ _ _ _ _ _ HRep) as Aheap.
    pose proof (r_hsize _ _ _ _ _ _ _ HRep) as Fhsize.
    (* int a = s->heap[i]; int n = s->hsize; int fuel = n; *)
    run. clear Fheap Aheap Fhsize. unfold Swhile.
    apply exec_loop with (R := Peano.lt) (I := DownInv m S N lss x lims lt i0)
      (a := hsize (hr x)).
    + apply lt_wf.
    + intros fuel le1 m1 HI.
      destruct HI as [Hs Ha' Hn Hfuel Hfle (h & i & Hi & Hilt & Hres & HRep1) Hun1].
      apply exec_seq.
      (* if (fuel > 0) ... else break; *)
      eapply (exec_if_cmp _ _ _ Cgt).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * destruct fuel as [|fuel].
        -- (* no fuel left: break; and the end *)
           replace (zcmp Cgt (Z.of_nat 0) 0) with false by reflexivity.
           cbv beta iota. apply exec_break. abrupt. apply loopk_break. normal.
           cbn [down_loop] in Hres.
           apply (heap_down_end_correct (lt := lt) S N lss x lims i0 h i le1 m m1).
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ symmetry. assumption.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ assumption.
        -- replace (zcmp Cgt (Z.of_nat (Datatypes.S fuel)) 0) with true
             by (symmetry; cbn [zcmp]; apply Z.ltb_lt; lia).
           cbv beta iota. apply exec_skip. normal.
           (* int c = 2 * i + 1; *)
           apply exec_seq.
           apply exec_set with (vint (Z.of_nat (Datatypes.S (2 * i)))).
           ++ apply eval_left. assumption.
           ++ normal. apply exec_seq.
              (* if (c >= n) break; *)
              eapply (exec_if_cmp _ _ _ Cge).
              ** ev.
              ** ev.
              ** reflexivity.
              ** reflexivity.
              ** unfold Small. lia.
              ** unfold Small. lia.
              ** cbn [zcmp].
                 destruct (Nat.leb_spec (hsize (hr x)) (Datatypes.S (2 * i)))
                   as [Hleaf | Hleft].
                 --- (* no child: break; and the end *)
                     replace (Z.of_nat (hsize (hr x)) <=? Z.of_nat (Datatypes.S (2 * i)))
                       with true by (symmetry; apply Z.leb_le; lia).
                     apply exec_break. abrupt.
                     apply loopk_break. normal.
                     cbn [down_loop] in Hres.
                     replace (hsize (hr x) <=? Datatypes.S (2 * i))%nat with true
                       in Hres by (symmetry; apply Nat.leb_le; lia).
                     apply (heap_down_end_correct (lt := lt) S N lss x lims i0 h i _ m
                              m1).
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ symmetry. assumption.
                     +++ assumption.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
                 --- (* a child: the rest of the loop body *)
                     replace (Z.of_nat (hsize (hr x)) <=? Z.of_nat (Datatypes.S (2 * i)))
                       with false by (symmetry; apply Z.leb_gt; lia).
                     apply exec_skip. normal.
                     apply (down_rest_correct (lt := lt) S N lss x lims i0 h i fuel _ m
                              m1).
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
    + (* The invariant holds at the start: heuristic hr x, position i0. *)
      constructor.
      * tmp.
      * tmp.
      * tmp.
      * tmp.
      * assumption.
      * exists (hr x), i0. split.
        -- tmp.
        -- split.
           ++ assumption.
           ++ split.
              ** reflexivity.
              ** rewrite with_heur_hr. assumption.
      * apply Mem.unchanged_on_refl.
Qed.

Lemma heap_down_fun: exists (b: block),
  Genv.find_symbol ge _heap_down = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_heap_down).
Proof. apply find_fun. reflexivity. Qed.
