(* heap_down moves the atom at a heap position down while a child has a higher activity
   (heap_down). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Ctypesdefs Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Heur Propagate Step Ctx.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep RepHeur Rescale HeapUp.
Import ListNotations.

(* The position k + 1 after the one in temporary id, as C computes it. *)
Lemma eval_succ: forall (le: temp_env) (m: mem) (id: ident) (k: nat),
  le ! id = Some (vnat k) ->
  eval_expr ge empty_env le m
    (Ebinop Oadd (Etempvar id tint) (Econst_int (Int.repr 1) tint) tint)
    (vnat (S k)).
Proof.
  intros le m id k Hk. eapply eval_Ebinop.
  - apply eval_Etempvar. apply Hk.
  - apply eval_Econst_int.
  - replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia.
    unfold vint. rewrite <- add_repr. cbn -[Int.add Int.repr].
    unfold sem_binarith, sem_cast, tint. cbn -[Int.add Int.repr]. cbv [Archi.ptr64].
    cbn -[Int.add Int.repr]. reflexivity.
Qed.

(* The first child of heap position i. *)
Abbreviation first_child i := (S (2 * i)).

(* The first child of the position i, as C computes it. *)
Lemma eval_left: forall (le: temp_env) (m: mem) (i: nat),
  le ! _i = Some (vnat i) ->
  eval_expr ge empty_env le m
    (Ebinop Oadd (Ebinop Omul (Econst_int (Int.repr 2) tint) (Etempvar _i tint) tint)
      (Econst_int (Int.repr 1) tint) tint)
    (vnat (first_child i)).
Proof.
  intros le m i Hi. eapply eval_Ebinop.
  - eapply eval_Ebinop.
    + apply eval_Econst_int.
    + apply eval_Etempvar. apply Hi.
    + reflexivity.
  - apply eval_Econst_int.
  - replace (Z.of_nat (S (2 * i))) with (2 * Z.of_nat i + 1) by lia.
    unfold vint. rewrite <- add_repr, <- mul_repr. cbn -[Int.add Int.mul Int.repr].
    unfold sem_binarith, sem_cast, tint. cbn -[Int.add Int.mul Int.repr].
    cbv [Archi.ptr64]. cbn -[Int.add Int.mul Int.repr]. reflexivity.
Qed.

(* The statements of heap_down after its loop: heap[i] = a; hpos[a] = i. *)
Definition heap_down_end: statement := drop_stmts 4 (fn_body f_heap_down).

(* What the choice of the child keeps: the memory, and the temporaries but c, which
   holds the child c. *)
Record ChildPost {le: temp_env} {m1: mem} {c: nat} {le': temp_env} {m': mem}
  {out: outcome}: Prop := {
  cp_out: out = Out_normal;
  cp_mem: m' = m1;
  cp_c: le' ! _c = Some (vnat c);
  cp_s: le' ! _s = le ! _s;
  cp_a: le' ! _a = le ! _a;
  cp_i: le' ! _i = le ! _i;
  cp_n: le' ! _n = le ! _n;
  cp_fuel: le' ! _fuel = le ! _fuel;
}.
Arguments ChildPost : clear implicits.

(* The statements of the loop of heap_down from the choice of the child on. *)
Definition down_rest: statement :=
  drop_stmts 3 (loop_body (first_stmt (drop_stmts 3 (fn_body f_heap_down)))).

(* The choice of the child. *)
Definition child_stmt: statement := first_stmt down_rest.

(* The choice of the child of position i of the n positions, with 2i + 1 < n: the
   second child if it is a position and more active than the first.

     {{ RepL (x <| hr := h |>) /\ c = 2i + 1 < n }}
       if (c + 1 < n) {
         if (s->act[s->heap[c + 1]] > s->act[s->heap[c]]) c = c + 1;
       }
     {{ ChildPost: c = child h n i }}                                             *)
Lemma child_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (h: Heur) (n i: nat) (le: temp_env) (m1: mem),
  RepL m1 sh N lss (x <| hr := h |>) -> (first_child i < n)%nat ->
  (n <= N)%nat -> le ! _s = Some (sptr sh) ->
  le ! _c = Some (vnat (first_child i)) ->
  le ! _n = Some (vnat n) ->
  Exec ge le m1 child_stmt (ChildPost le m1 (child h n i)).
Proof.
  intros sh N lss x h n i le m1 HRep1 Hc Hn Hs Hc' Hn'.
  pose proof (r_n HRep1) as HN.
  pose proof (r_heur HRep1) as Hok1. cbn [set_hr hr] in Hok1.
  unfold child_stmt, down_rest, f_heap_down.
  cbn [fn_body drop_stmts first_stmt loop_body Swhile].
  unfold child.
  (* if (c + 1 < n) ... *)
  apply (exec_if_lt (Z.of_nat (S (S (2 * i)))) (Z.of_nat n)).
  - apply eval_succ. assumption.
  - ev.
  - reflexivity.
  - lia.
  - (* two children: compare their activities *)
    intros Hlt.
    replace (S (S (2 * i)) <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    assert (Hsucc: Int.add (Int.repr (Z.of_nat (S (2 * i)))) (Int.repr 1)
                   = Int.repr (Z.of_nat (S (S (2 * i))))).
    { rewrite add_repr. f_equal. lia. }
    assert (Hleft: (tget (heap h) (S (2 * i)) < N)%nat).
    { apply (ho_heap Hok1). lia. }
    assert (Hright: (tget (heap h) (S (S (2 * i))) < N)%nat).
    { apply (ho_heap Hok1). lia. }
    pose proof (ho_act Hok1 _ Hleft) as Hactl.
    pose proof (ho_act Hok1 _ Hright) as Hactr.
    unfold act_lim in Hactl, Hactr.
    change (2 ^ 30)%Z with small_bound in Hactl, Hactr.
    pose proof (r_heap HRep1) as Fheap.
    pose proof (a_heap HRep1) as Aheap.
    pose proof (r_act HRep1) as Fact.
    pose proof (a_act HRep1) as Aact.
    cbn [set_hr hr] in Aheap, Aact.
    run.
    (* if (s->act[s->heap[c + 1]] > s->act[s->heap[c]]) c = c + 1; *)
    eapply exec_if_gt.
    + ev.
    + ev.
    + reflexivity.
    + lia.
    + (* the second child is more active: c = c + 1; *)
      intros Hmore. apply Z.ltb_lt in Hmore. rewrite Hmore.
      apply exec_set with (vnat (S (S (2 * i)))).
      * apply eval_succ. tmp.
      * constructor.
        -- reflexivity.
        -- reflexivity.
        -- tmp.
        -- tmp.
        -- tmp.
        -- tmp.
        -- tmp.
        -- tmp.
    + (* the first child is at least as active *)
      intros Hless. apply Z.ltb_ge in Hless. rewrite Hless.
      apply exec_skip. constructor.
      * reflexivity.
      * reflexivity.
      * tmp.
      * tmp.
      * tmp.
      * tmp.
      * tmp.
      * tmp.
  - (* one child *)
    intros Hge.
    replace (S (S (2 * i)) <? n)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
    apply exec_skip. constructor.
    + reflexivity.
    + reflexivity.
    + assumption.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
Qed.

(* The loop of heap_down, called from the memory m on the context x to move the atom a at
   position i0 down. *)
Section Loop.
  Context (m: mem) (sh: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx) (i0: nat).

  (* The atom moved down, and the number of positions of the heap. *)
  Abbreviation a := (atom_at (hr x) i0).
  Abbreviation n := (hsize (hr x)).

  (* What down_loop gives for a from i0: the heuristic and the position left for a. *)
  Abbreviation res := (down_loop (hr x) n a i0 n).

  (* What heap_down promises. *)
  Definition down_post: mem -> val -> Prop :=
    fun (m': mem) (_: val) => HeurPost sh N lss x m (heap_down (hr x) i0) m'.

  (* The temporaries of the loop at position i with fuel left. *)
  Record DownTemps {le: temp_env} {i fuel: nat}: Prop := {
    dt_s: le ! _s = Some (sptr sh);
    dt_a: le ! _a = Some (vnat a);
    dt_n: le ! _n = Some (vnat n);
    dt_i: le ! _i = Some (vnat i);
    dt_fuel: le ! _fuel = Some (vnat fuel);
  }.
  Arguments DownTemps : clear implicits.

  (* The end of heap_down, once the loop left the heuristic h and position i, which is
     what down_loop gives:

       {{ RepL (x <| hr := h |>) /\ res = (h, i) }}
         s->heap[i] = a;
         s->hpos[a] = i;                                         (place_end_correct)
       {{ RepL (x <| hr := place h i a |>), and place h i a = heap_down (hr x) i0 }} *)
  Lemma heap_down_end_correct: forall (h: Heur) (i fuel: nat) (le: temp_env) (m1: mem),
    RepL m1 sh N lss (x <| hr := h |>) -> (i < N)%nat -> (a < N)%nat -> res = (h, i) ->
    Mem.unchanged_on (HeurFrame sh) m m1 -> DownTemps le i fuel ->
    Exec ge le m1 heap_down_end (Returns f_heap_down down_post).
  Proof.
    intros h i fuel le m1 HRep1 Hi Ha Hres Hun1 [Hs Ha' _ Hi' _].
    unfold down_post, heap_down. fold a. rewrite Hres.
    apply (place_end_correct sh N lss x h i a).
    - reflexivity.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
  Qed.

  (* The invariant of the loop at fuel: the temporaries hold a position i below N, and
     the memory represents x with a heuristic h from which down_loop gives res, changed
     from m only in the heuristic. *)
  Record DownInv {fuel: nat} {le: temp_env} {m1: mem}: Prop := {
    dni_fuel_le: (fuel <= N)%nat;
    dni_pos: exists (h: Heur) (i: nat),
      DownTemps le i fuel /\ (i < N)%nat /\ down_loop h n a i fuel = res /\
      RepL m1 sh N lss (x <| hr := h |>);
    dni_frame: Mem.unchanged_on (HeurFrame sh) m m1;
  }.
  Arguments DownInv : clear implicits.

  (* The statements of the loop of heap_down that move the child b at c up to i. *)
  Definition down_move: statement :=
    drop_stmts 6 (loop_body (first_stmt (drop_stmts 3 (fn_body f_heap_down)))).

  (* Moving the child b at c, more active than a, up to position i; the loop goes on
     from c with one less fuel:

       {{ DownInv (fuel + 1): heuristic h, position i /\ act a < act b }}
         s->heap[i] = b; s->hpos[b] = i; i = c; fuel--;               (move_correct)
       {{ DownInv fuel: heuristic place h i b, position c }}                        *)
  Lemma down_move_correct: forall (h: Heur) (i c fuel: nat) (le: temp_env) (m1: mem)
    (Q: temp_env -> mem -> outcome -> Prop),
    RepL m1 sh N lss (x <| hr := h |>) -> (i < N)%nat -> (c < N)%nat ->
    (S fuel <= N)%nat -> (tget (heap h) c < N)%nat ->
    down_loop (place h i (tget (heap h) c)) n a c fuel = res ->
    Mem.unchanged_on (HeurFrame sh) m m1 -> DownTemps le i (S fuel) ->
    le ! _c = Some (vnat c) -> le ! _b = Some (vnat (tget (heap h) c)) ->
    Exec ge le m1 down_move (LoopK Peano.lt DownInv Q (S fuel)).
  Proof.
    intros h i c fuel le m1 Q HRep1 Hi Hc Hfle Hb Hres Hun1 [Hs Ha Hn Hi' Hfuel] Hc'
      Hb'.
    unfold down_move, f_heap_down.
    cbn [fn_body drop_stmts first_stmt loop_body Swhile].
    fold (move_stmt _c).
    apply (move_correct sh N lss x h _c i (tget (heap h) c) c fuel le m m1).
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
      intros m3 HRep3 Hun3. unfold move_temps. apply loopk_next with fuel.
      + lia.
      + constructor.
        * lia.
        * exists (place h i (tget (heap h) c)), c. split.
          -- constructor.
             ++ tmp.
             ++ tmp.
             ++ tmp.
             ++ tmp.
             ++ tmp.
          -- split.
             ++ assumption.
             ++ split.
                ** assumption.
                ** apply HRep3.
        * assumption.
  Qed.

  (* The loop body of heap_down from the choice of the child on, at position i with
     first_child i < n:

       {{ DownInv (fuel + 1): heuristic h, position i /\ c = first_child i < n }}
         choose the child c;                                            (child_correct)
         int b = s->heap[c];
         if (s->act[b] <= s->act[a]) break;                       (heap_down_end_correct)
         s->heap[i] = b; s->hpos[b] = i; i = c; fuel--;            (down_move_correct)
       {{ DownInv fuel: heuristic place h i b, position c }}                        *)
  Lemma down_rest_correct: forall (h: Heur) (i fuel: nat) (le: temp_env) (m1: mem),
    RepL m1 sh N lss (x <| hr := h |>) -> (i < N)%nat -> (first_child i < n)%nat ->
    (n <= N)%nat -> (S fuel <= N)%nat -> (a < N)%nat ->
    down_loop h n a i (S fuel) = res ->
    Mem.unchanged_on (HeurFrame sh) m m1 -> DownTemps le i (S fuel) ->
    le ! _c = Some (vnat (first_child i)) ->
    Exec ge le m1 down_rest
      (LoopK Peano.lt DownInv (SeqK ge heap_down_end (Returns f_heap_down down_post))
         (S fuel)).
  Proof.
    intros h i fuel le m1 HRep1 Hi Hleft Hn Hfle Ha Hres Hun1 [Hs Ha' Hn' Hi' Hfuel] Hc.
    pose proof (r_n HRep1) as HN.
    pose proof (r_heur HRep1) as Hok1. cbn [set_hr hr] in Hok1.
    pose proof (child_lt h (hsize (hr x)) i Hleft) as Hchild.
    assert (Hb: (tget (heap h) (child h (hsize (hr x)) i) < N)%nat).
    { apply (ho_heap Hok1). lia. }
    pose proof (ho_act Hok1 _ Hb) as Hactb.
    pose proof (ho_act Hok1 _ Ha) as Hacta.
    unfold act_lim in Hactb, Hacta.
    change (2 ^ 30)%Z with small_bound in Hactb, Hacta.
    cbn [down_loop] in Hres.
    replace (hsize (hr x) <=? S (2 * i))%nat with false in Hres
      by (symmetry; apply Nat.leb_gt; lia).
    unfold down_rest. apply exec_seq.
    (* choose the child c *)
    apply exec_weaken with (Q := ChildPost le m1 (child h (hsize (hr x)) i)).
    - apply (child_correct sh N lss x).
      + assumption.
      + assumption.
      + assumption.
      + assumption.
      + assumption.
      + assumption.
    - intros le2 m2 out [-> -> Hc2 Hs2 Ha2 Hi2 Hn2 Hfuel2]. apply seqk_normal.
      rewrite <- Hs2 in Hs. rewrite <- Ha2 in Ha'. rewrite <- Hn2 in Hn'.
      rewrite <- Hi2 in Hi'. rewrite <- Hfuel2 in Hfuel. clear Hs2 Ha2 Hn2 Hi2 Hfuel2.
      pose proof (r_heap HRep1) as Fheap.
      pose proof (a_heap HRep1) as Aheap.
      pose proof (r_act HRep1) as Fact.
      pose proof (a_act HRep1) as Aact.
      cbn [set_hr hr] in Aheap, Aact.
      (* int b = s->heap[c]; if (s->act[b] <= s->act[a]) break; *)
      run.
      eapply exec_if_le.
      + ev.
      + ev.
      + reflexivity.
      + lia.
      + (* the child is not more active: break; and the end *)
        intros Hle. apply Z.leb_le in Hle. rewrite Hle in Hres.
        apply exec_break. abrupt.
        apply loopk_break. normal.
        apply (heap_down_end_correct h i (S fuel) _ m1).
        * assumption.
        * assumption.
        * assumption.
        * symmetry. assumption.
        * assumption.
        * constructor.
          -- tmp.
          -- tmp.
          -- tmp.
          -- tmp.
          -- tmp.
      + (* the child is more active: it moves up to i *)
        intros Hgt. apply Z.leb_gt in Hgt. rewrite Hgt in Hres.
        apply exec_skip. normal.
        apply (down_move_correct h i (child h n i) fuel _ m1).
        * assumption.
        * assumption.
        * lia.
        * assumption.
        * assumption.
        * assumption.
        * assumption.
        * constructor.
          -- tmp.
          -- tmp.
          -- tmp.
          -- tmp.
          -- tmp.
        * tmp.
        * tmp.
  Qed.
End Loop.
Arguments DownTemps : clear implicits.
Arguments DownInv : clear implicits.

(* heap_down moves the atom a at position i0 down: while the more active child b at c
   of its position i has a higher activity, b moves up to i, at most hsize times; then
   a goes to the position left. Only the heuristic changes. Writing a for
   atom_at (hr x) i0 and n for hsize (hr x):

     {{ RepL m sh N lss x /\ i0 < N }}
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
     {{ RepL (x <| hr := heap_down (hr x) i0 |>) /\ only the heuristic changed }}

   The loop ends: fuel decreases. *)
Lemma heap_down_correct: forall (sh: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (i: nat),
  {{ m | RepL m sh N lss x /\ (i < N)%nat }}
    f_heap_down(sptr sh, vnat i)
  {{ m', v | HeurPost sh N lss x m (heap_down (hr x) i) m' }}.
Proof.
  intros sh N lss x i0 m [HRep Hi0]. pose proof (r_n HRep) as HN.
  pose proof (r_heur HRep) as Hok.
  assert (Ha: (atom_at (hr x) i0 < N)%nat).
  { apply (ho_heap Hok). assumption. }
  pose proof (ho_hsize Hok) as Hhsize.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - fold (down_post m sh N lss x i0). unfold f_heap_down.
    cbn [fn_body fn_return].
    pose proof (r_heap HRep) as Fheap.
    pose proof (a_heap HRep) as Aheap.
    pose proof (r_hsize HRep) as Fhsize.
    (* int a = s->heap[i]; int n = s->hsize; int fuel = n; *)
    run. clear Fheap Aheap Fhsize. unfold Swhile.
    apply exec_loop with (R := Peano.lt) (I := DownInv m sh N lss x i0)
      (a := hsize (hr x)).
    + apply lt_wf.
    + intros fuel le1 m1 HI.
      destruct HI as [Hfle (h & i & [Hs Ha' Hn Hi Hfuel] & Hilt & Hres & HRep1) Hun1].
      apply exec_seq.
      (* if (fuel > 0) ... else break; *)
      eapply exec_if_gt.
      * ev.
      * ev.
      * reflexivity.
      * lia.
      * intros Hfuel_left. destruct fuel as [|fuel].
        -- (* no fuel left: impossible *)
           lia.
        -- (* fuel left *)
           apply exec_skip. normal.
           (* int c = 2 * i + 1; *)
           apply exec_seq.
           apply exec_set with (vnat (S (2 * i))).
           ++ apply eval_left. assumption.
           ++ normal. apply exec_seq.
              (* if (c >= n) break; *)
              eapply exec_if_ge.
              ** ev.
              ** ev.
              ** reflexivity.
              ** lia.
              ** (* no child: break; and the end *)
                 intros Hleaf. apply exec_break. abrupt.
                 apply loopk_break. normal.
                 cbn [down_loop] in Hres.
                 replace (hsize (hr x) <=? S (2 * i))%nat with true
                   in Hres by (symmetry; apply Nat.leb_le; lia).
                 apply (heap_down_end_correct m sh N lss x i0 h i (S fuel) _ m1).
                 --- assumption.
                 --- assumption.
                 --- assumption.
                 --- symmetry. assumption.
                 --- assumption.
                 --- constructor.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
              ** (* a child: the rest of the loop body *)
                 intros Hchild. apply exec_skip. normal.
                 apply (down_rest_correct m sh N lss x i0 h i fuel _ m1).
                 --- assumption.
                 --- assumption.
                 --- lia.
                 --- assumption.
                 --- assumption.
                 --- assumption.
                 --- assumption.
                 --- assumption.
                 --- constructor.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
                 --- tmp.
      * intros Hno_fuel. destruct fuel as [|fuel].
        -- (* no fuel left: break; and the end *)
           apply exec_break. abrupt. apply loopk_break. normal.
           cbn [down_loop] in Hres.
           apply (heap_down_end_correct m sh N lss x i0 h i 0 le1 m1).
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ symmetry. assumption.
           ++ assumption.
           ++ constructor.
              ** assumption.
              ** assumption.
              ** assumption.
              ** assumption.
              ** assumption.
        -- (* fuel left: impossible *)
           lia.
    + (* The invariant holds at the start: heuristic hr x, position i0. *)
      constructor.
      * assumption.
      * exists (hr x), i0. split.
        -- constructor.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ tmp.
        -- split.
           ++ assumption.
           ++ split.
              ** reflexivity.
              ** rewrite set_hr_same. assumption.
      * apply Mem.unchanged_on_refl.
Qed.

Lemma heap_down_fun: FunAt _heap_down f_heap_down.
Proof. apply find_fun. reflexivity. Qed.
