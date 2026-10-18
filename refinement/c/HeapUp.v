(* heap_up moves the atom at a heap position up while its parent has a lower activity
   (heap_up). *)
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
From compcert Require Import Ctypesdefs.
From compcert Require Import Clight.
From compcert Require Import ClightBigstep.

From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import Heur.
From RocqSAT.refinement Require Import Ctx.
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement Require Import Step.
From RocqSAT.refinement.c Require Import Arrays.
From RocqSAT.refinement.c Require Import Logic.
From RocqSAT.refinement.c Require Import Common.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Rep.
From RocqSAT.refinement.c Require Import RepHeur.
From RocqSAT.refinement.c Require Import Rescale.

(* C's division of a natural number k by 2. *)
Lemma div2_nat: forall (ge: genv) (m: mem) (k: nat), Z.of_nat k < small_bound ->
  sem_binary_operation ge Odiv (vnat k) Ctypesdefs.tint (vint 2)
    Ctypesdefs.tint m
  = Some (vnat (k / 2)).
Proof.
  intros ge m k Hk. assert (Hmax: Int.max_signed = 2147483647) by reflexivity.
  assert (Hmin: Int.min_signed = - int_bound) by reflexivity.
  unfold sem_binary_operation, sem_div, sem_binarith, sem_cast, vint.
  simpl. cbv [Archi.ptr64]. simpl. change (fst (Nat.divmod k 1 0 1)) with (k / 2)%nat.
  (* k is not the least int, so C divides *)
  replace (Int.eq (Int.repr (Z.of_nat k)) (Int.repr Int.min_signed)) with false.
  - cbn - [Nat.div Int.divs]. unfold Int.divs. rewrite !Int.signed_repr by lia.
    rewrite Nat2Z.inj_div. rewrite Z.quot_div_nonneg by lia. reflexivity.
  - symmetry. apply Int.eq_false. intros Heq. apply (f_equal Int.signed) in Heq.
    rewrite !Int.signed_repr in Heq by lia. lia.
Qed.

(* The parent of heap position i > 0. *)
Abbreviation parent i := ((i - 1) / 2)%nat.

(* The parent of the position i > 0, as C computes it. *)
Lemma eval_parent: forall (le: temp_env) (m: mem) (i: nat),
  le ! _i = Some (vnat i) -> (0 < i)%nat -> Z.of_nat i < small_bound ->
  eval_expr ge empty_env le m
    (Ebinop Odiv (Ebinop Osub (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)
      (Econst_int (Int.repr 2) tint) tint)
    (vnat (parent i)).
Proof.
  intros le m i Hi Hpos Hsmall.
  assert (Hsub: Int.sub (Int.repr (Z.of_nat i)) (Int.repr 1)
                = Int.repr (Z.of_nat (i - 1))).
  { rewrite sub_repr. f_equal. lia. }
  eapply eval_Ebinop.
  - ev.
  - ev.
  - cbn [cast_int_int typeof]. ints. apply div2_nat. lia.
Qed.

(* Storing atom tb at heap position ti, with temporary th for the array:
   th = s->heap; th[ti] = tb; *)
Definition heap_stmt (th ti tb: ident): statement :=
  Ssequence
    (Sset th
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _solver noattr)))
          (Tstruct _solver noattr)) _heap (tptr tint)))
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar th (tptr tint)) (Etempvar ti tint) (tptr tint)) tint)
      (Etempvar tb tint)).

(* Storing the heap position ti of atom tb, with temporary tp for the array:
   tp = s->hpos; tp[tb] = ti; *)
Definition hpos_stmt (tp tb ti: ident): statement :=
  Ssequence
    (Sset tp
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _solver noattr)))
          (Tstruct _solver noattr)) _hpos (tptr tint)))
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar tp (tptr tint)) (Etempvar tb tint) (tptr tint)) tint)
      (Etempvar ti tint)).

(* The store of heap_stmt, on the memory of the heuristic h:

     {{ RepL (x <| hr := h |>) /\ i < N /\ b < N }}
       th = s->heap; th[i] = b;                                         (rep_store_heap)
     {{ RepL (x <| hr := set_heap h i b |>) /\ only the heuristic changed }}          *)
Lemma heap_stmt_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (h: Heur) (th ti tb: ident) (i b: nat) (le: temp_env)
  (m: mem) (Q: temp_env -> mem -> outcome -> Prop),
  RepL m sh N lss (x <| hr := h |>) -> (i < N)%nat -> (b < N)%nat ->
  le ! _s = Some (sptr sh) -> le ! ti = Some (vnat i) ->
  le ! tb = Some (vnat b) -> ti <> th -> tb <> th ->
  (forall (m': mem), RepL m' sh N lss (x <| hr := set_heap h i b |>) ->
     Mem.unchanged_on (HeurFrame sh) m m' ->
     Q (PTree.set th (Vptr (b_heap sh) Ptrofs.zero) le) m' Out_normal) ->
  Exec ge le m (heap_stmt th ti tb) Q.
Proof.
  intros sh N lss x h th ti tb i b le m Q HRep Hi Hb Hs Hti Htb Hith Hbth HQ.
  pose proof (r_n HRep) as HN.
  pose proof (r_heap HRep) as Fheap.
  pose proof (a_heap HRep) as Aheap.
  unfold heap_stmt. apply exec_seq.
  (* th = s->heap; *)
  eapply exec_set.
  - ev.
  - normal.
    assert (Hti': (PTree.set th (Vptr (b_heap sh) Ptrofs.zero) le) ! ti
                  = Some (vnat i)).
    { rewrite PTree.gso by assumption. assumption. }
    assert (Htb': (PTree.set th (Vptr (b_heap sh) Ptrofs.zero) le) ! tb
                  = Some (vnat b)).
    { rewrite PTree.gso by assumption. assumption. }
    (* th[i] = b; *)
    eapply (exec_store_arr Aheap Hi).
    + evl.
    + ofs.
    + reflexivity.
    + ev.
    + intros m1 Hst. apply HQ.
      * apply (rep_store_heap m m1 i b HRep Hi Hb Hst).
      * apply (store_unchanged _ m m m1 Mint32 (b_heap sh) (4 * Z.of_nat i) (vnat b)).
        -- apply Mem.unchanged_on_refl.
        -- apply Hst.
        -- apply heap_not_frame.
Qed.

(* The store of hpos_stmt, on the memory of the heuristic h:

     {{ RepL (x <| hr := h |>) /\ b < N /\ i < N }}
       tp = s->hpos; tp[b] = i;                                         (rep_store_hpos)
     {{ RepL (x <| hr := set_hpos h b (Some i) |>) /\ only the heuristic changed }}   *)
Lemma hpos_stmt_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (h: Heur) (tp tb ti: ident) (b i: nat) (le: temp_env)
  (m: mem) (Q: temp_env -> mem -> outcome -> Prop),
  RepL m sh N lss (x <| hr := h |>) -> (b < N)%nat -> (i < N)%nat ->
  le ! _s = Some (sptr sh) -> le ! tb = Some (vnat b) ->
  le ! ti = Some (vnat i) -> tb <> tp -> ti <> tp ->
  (forall (m': mem), RepL m' sh N lss (x <| hr := set_hpos h b (Some i) |>) ->
     Mem.unchanged_on (HeurFrame sh) m m' ->
     Q (PTree.set tp (Vptr (b_hpos sh) Ptrofs.zero) le) m' Out_normal) ->
  Exec ge le m (hpos_stmt tp tb ti) Q.
Proof.
  intros sh N lss x h tp tb ti b i le m Q HRep Hb Hi Hs Htb Hti Hbtp Hitp HQ.
  pose proof (r_n HRep) as HN.
  pose proof (r_hpos HRep) as Fhpos.
  pose proof (a_hpos HRep) as Ahpos.
  unfold hpos_stmt. apply exec_seq.
  (* tp = s->hpos; *)
  eapply exec_set.
  - ev.
  - normal.
    assert (Htb': (PTree.set tp (Vptr (b_hpos sh) Ptrofs.zero) le) ! tb
                  = Some (vnat b)).
    { rewrite PTree.gso by assumption. assumption. }
    assert (Hti': (PTree.set tp (Vptr (b_hpos sh) Ptrofs.zero) le) ! ti
                  = Some (vnat i)).
    { rewrite PTree.gso by assumption. assumption. }
    (* tp[b] = i; *)
    eapply (exec_store_arr Ahpos Hb).
    + evl.
    + ofs.
    + reflexivity.
    + ev.
    + intros m1 Hst. apply HQ.
      * apply (rep_store_hpos m m1 b (Some i) HRep Hb).
        -- intros i' Hi'. injection Hi' as <-. assumption.
        -- apply Hst.
      * apply (store_unchanged _ m m m1 Mint32 (b_hpos sh) (4 * Z.of_nat b) (vnat i)).
        -- apply Mem.unchanged_on_refl.
        -- apply Hst.
        -- apply hpos_not_frame.
Qed.

(* Moving atom b to position i, then going on from position j with one less fuel, as
   the loops of heap_up (j = p) and heap_down (j = c) do. *)
Definition move_stmt (tj: ident): statement :=
  Ssequence (heap_stmt _t'4 _i _b)
    (Ssequence (hpos_stmt _t'3 _b _i)
      (Ssequence (Sset _i (Etempvar tj tint))
        (Sset _fuel
          (Ebinop Osub (Etempvar _fuel tint) (Econst_int (Int.repr 1) tint) tint)))).

(* The temporaries after move_stmt from le: i = j, one less fuel, and the arrays heap and
   hpos in the temporaries clightgen made for them. *)
Definition move_temps (sh: Shape) (j fuel: nat) (le: temp_env): temp_env :=
  PTree.set _fuel (vnat fuel)
    (PTree.set _i (vnat j)
       (PTree.set _t'3 (Vptr (b_hpos sh) Ptrofs.zero)
          (PTree.set _t'4 (Vptr (b_heap sh) Ptrofs.zero) le))).

(* The statements of move_stmt, on the memory of the heuristic h:

     {{ RepL (x <| hr := h |>) /\ i < N /\ b < N }}
       s->heap[i] = b;
       s->hpos[b] = i;                      (heap_stmt_correct, hpos_stmt_correct)
       i = j;
       fuel--;
     {{ RepL (x <| hr := place h i b |>) /\ only the heuristic changed }}         *)
Lemma move_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (h: Heur) (tj: ident) (i b j fuel: nat) (le: temp_env)
  (m m1: mem) (Q: temp_env -> mem -> outcome -> Prop),
  RepL m1 sh N lss (x <| hr := h |>) -> (i < N)%nat -> (b < N)%nat ->
  Mem.unchanged_on (HeurFrame sh) m m1 ->
  le ! _s = Some (sptr sh) -> le ! _i = Some (vnat i) ->
  le ! _b = Some (vnat b) -> le ! tj = Some (vnat j) ->
  le ! _fuel = Some (vnat (S fuel)) ->
  tj <> _t'4 -> tj <> _t'3 ->
  (forall (m3: mem), RepL m3 sh N lss (x <| hr := place h i b |>) ->
     Mem.unchanged_on (HeurFrame sh) m m3 ->
     Q (move_temps sh j fuel le) m3 Out_normal) ->
  Exec ge le m1 (move_stmt tj) Q.
Proof.
  intros sh N lss x h tj i b j fuel le m m1 Q HRep1 Hi Hb Hun1 Hs Hi' Hb' Hj Hfuel
    Htj4 Htj3 HQ.
  assert (Hfsub: Int.sub (Int.repr (Z.of_nat (S fuel))) (Int.repr 1)
                 = Int.repr (Z.of_nat fuel)).
  { rewrite sub_repr. f_equal. lia. }
  unfold move_stmt. apply exec_seq.
  (* s->heap[i] = b; *)
  apply (heap_stmt_correct sh N lss x h _ _ _ i b).
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - discriminate.
  - discriminate.
  - intros m2 HRep2 Hun2. normal. apply exec_seq.
    (* s->hpos[b] = i; *)
    apply (hpos_stmt_correct sh N lss x (set_heap h i b) _ _ _ b i).
    + assumption.
    + assumption.
    + assumption.
    + tmp.
    + tmp.
    + tmp.
    + discriminate.
    + discriminate.
    + intros m3 HRep3 Hun3. normal.
      assert (Hj': (PTree.set _t'3 (Vptr (b_hpos sh) Ptrofs.zero)
                      (PTree.set _t'4 (Vptr (b_heap sh) Ptrofs.zero) le)) ! tj
                   = Some (vnat j)).
      { rewrite !PTree.gso by assumption. assumption. }
      (* i = j; fuel--; *)
      run. ints. apply HQ.
      * apply HRep3.
      * apply (Mem.unchanged_on_trans _ m m2 m3).
        -- apply (Mem.unchanged_on_trans _ m m1 m2).
           ++ assumption.
           ++ assumption.
        -- assumption.
Qed.

(* The atom heap_up or heap_down moves: the one at position i. *)
Definition atom_at (h: Heur) (i: nat): nat := tget (heap h) i.

(* Atom a to position i, at the end of heap_up and heap_down. *)
Definition place_end_stmt: statement :=
  Ssequence (heap_stmt _t'2 _i _a) (hpos_stmt _t'1 _a _i).

(* The stores of place_end_stmt, at the end of a function f without result:

     {{ RepL (x <| hr := h |>) /\ i < N /\ a < N }}
       s->heap[i] = a;
       s->hpos[a] = i;                      (heap_stmt_correct, hpos_stmt_correct)
     {{ RepL (x <| hr := place h i a |>) /\ only the heuristic changed }}         *)
Lemma place_end_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (h: Heur) (i a: nat) (f: function) (le: temp_env)
  (m m1: mem),
  fn_return f = tvoid -> RepL m1 sh N lss (x <| hr := h |>) -> (i < N)%nat ->
  (a < N)%nat -> Mem.unchanged_on (HeurFrame sh) m m1 ->
  le ! _s = Some (sptr sh) -> le ! _i = Some (vnat i) ->
  le ! _a = Some (vnat a) ->
  Exec ge le m1 place_end_stmt (Returns f (fun (m': mem) (_: val) =>
    HeurPost sh N lss x m (place h i a) m')).
Proof.
  intros sh N lss x h i a f le m m1 Hvoid HRep1 Hi Ha Hun1 Hs Hi' Ha'.
  unfold place_end_stmt. apply exec_seq.
  (* s->heap[i] = a; *)
  apply (heap_stmt_correct sh N lss x h _ _ _ i a).
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - discriminate.
  - discriminate.
  - intros m2 HRep2 Hun2. normal.
    (* s->hpos[a] = i; *)
    apply (hpos_stmt_correct sh N lss x (set_heap h i a) _ _ _ a i).
    + assumption.
    + assumption.
    + assumption.
    + tmp.
    + tmp.
    + tmp.
    + discriminate.
    + discriminate.
    + intros m3 HRep3 Hun3. exists Vundef. split.
      * rewrite Hvoid. reflexivity.
      * split.
        -- apply HRep3.
        -- apply (Mem.unchanged_on_trans _ m m2 m3).
           ++ apply (Mem.unchanged_on_trans _ m m1 m2).
              ** assumption.
              ** assumption.
           ++ assumption.
Qed.

(* The statements of heap_up after its loop: heap[i] = a; hpos[a] = i. *)
Definition heap_up_end: statement := drop_stmts 3 (fn_body f_heap_up).

(* The loop of heap_up, called from the memory m on the context x to move the atom a at
   position i0 up. *)
Section Loop.
  Context (m: mem) (sh: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx) (i0: nat).

  (* The atom moved up. *)
  Abbreviation a := (atom_at (hr x) i0).

  (* What up_loop gives for a from i0: the heuristic and the position left for a. *)
  Abbreviation res := (up_loop (hr x) a i0 (hsize (hr x))).

  (* The temporaries of the loop at position i with fuel left. *)
  Record UpTemps {le: temp_env} {i fuel: nat}: Prop := {
    ut_s: le ! _s = Some (sptr sh);
    ut_a: le ! _a = Some (vnat a);
    ut_i: le ! _i = Some (vnat i);
    ut_fuel: le ! _fuel = Some (vnat fuel);
  }.
  Arguments UpTemps : clear implicits.

  (* The end of heap_up, once the loop left the heuristic h and position i, which is
     what up_loop gives:

       {{ RepL (x <| hr := h |>) /\ res = (h, i) }}
         s->heap[i] = a;
         s->hpos[a] = i;                                         (place_end_correct)
       {{ RepL (x <| hr := place h i a |>), and place h i a = heap_up (hr x) i0 }} *)
  Lemma heap_up_end_correct: forall (h: Heur) (i fuel: nat) (le: temp_env) (m1: mem),
    RepL m1 sh N lss (x <| hr := h |>) -> (i < N)%nat -> (a < N)%nat -> res = (h, i) ->
    Mem.unchanged_on (HeurFrame sh) m m1 -> UpTemps le i fuel ->
    Exec ge le m1 heap_up_end (Returns f_heap_up (fun (m': mem) (_: val) =>
      HeurPost sh N lss x m (heap_up (hr x) i0) m')).
  Proof.
    intros h i fuel le m1 HRep1 Hi Ha Hres Hun1 [Hs Ha' Hi' _].
    unfold heap_up. fold a. rewrite Hres.
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
     the memory represents x with a heuristic h from which up_loop gives res, changed
     from m only in the heuristic. *)
  Record UpInv {fuel: nat} {le: temp_env} {m1: mem}: Prop := {
    upi_fuel_le: (fuel <= N)%nat;
    upi_pos: exists (h: Heur) (i: nat),
      UpTemps le i fuel /\ (i < N)%nat /\ up_loop h a i fuel = res /\
      RepL m1 sh N lss (x <| hr := h |>);
    upi_frame: Mem.unchanged_on (HeurFrame sh) m m1;
  }.
  Arguments UpInv : clear implicits.

  (* The statements of the loop of heap_up that move the parent b at p down to i. *)
  Definition up_move: statement :=
    drop_stmts 5 (loop_body (first_stmt (drop_stmts 2 (fn_body f_heap_up)))).

  (* Moving the parent b at p = parent i, less active than a, down to position i; the
     loop goes on from p with one less fuel:

       {{ UpInv (fuel + 1): heuristic h, position i /\ 0 < i /\ act b < act a }}
         s->heap[i] = b; s->hpos[b] = i; i = p; fuel--;               (move_correct)
       {{ UpInv fuel: heuristic place h i b, position p }}                          *)
  Lemma up_move_correct: forall (h: Heur) (i fuel: nat) (le: temp_env) (m1: mem)
    (Q: temp_env -> mem -> outcome -> Prop),
    RepL m1 sh N lss (x <| hr := h |>) -> (0 < i < N)%nat -> (S fuel <= N)%nat ->
    (tget (heap h) (parent i) < N)%nat ->
    up_loop (place h i (tget (heap h) (parent i))) a (parent i) fuel = res ->
    Mem.unchanged_on (HeurFrame sh) m m1 -> UpTemps le i (S fuel) ->
    le ! _p = Some (vnat (parent i)) ->
    le ! _b = Some (vnat (tget (heap h) (parent i))) ->
    Exec ge le m1 up_move (LoopK Peano.lt UpInv Q (S fuel)).
  Proof.
    intros h i fuel le m1 Q HRep1 Hi Hfle Hb Hres Hun1 [Hs Ha Hi' Hfuel] Hp Hb'.
    assert (Hpi: (parent i <= i - 1)%nat).
    { apply Nat.Div0.div_le_upper_bound. lia. }
    unfold up_move, f_heap_up. cbn [fn_body drop_stmts first_stmt loop_body Swhile].
    fold (move_stmt _p).
    apply (move_correct sh N lss x h _p i (tget (heap h) (parent i)) (parent i) fuel le
             m m1).
    - assumption.
    - lia.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - discriminate.
    - discriminate.
    - (* the loop goes on from p *)
      intros m3 HRep3 Hun3. unfold move_temps. apply loopk_next with fuel.
      + lia.
      + constructor.
        * lia.
        * exists (place h i (tget (heap h) (parent i))), (parent i). split.
          -- constructor.
             ++ tmp.
             ++ tmp.
             ++ tmp.
             ++ tmp.
          -- split.
             ++ lia.
             ++ split.
                ** assumption.
                ** apply HRep3.
        * assumption.
  Qed.
End Loop.
Arguments UpTemps : clear implicits.
Arguments UpInv : clear implicits.

(* heap_up moves the atom a at position i0 up: while the parent b at p = parent i of
   its position i has a lower activity, b moves down to i, at most hsize times; then a
   goes to the position left. Only the heuristic changes. Writing a for
   atom_at (hr x) i0 and res for up_loop (hr x) a i0 (hsize (hr x)):

     {{ RepL m sh N lss x /\ i0 < N }}
       int a = s->heap[i];
       int fuel = s->hsize;
     {{ UpInv (hsize (hr x)): heuristic hr x, i = i0 }}
       while (fuel > 0) {
     {{ UpInv fuel: heuristic h, position i /\ fuel > 0 }}
         if (i <= 0) break;
         int p = (i - 1) / 2;                                        (eval_parent)
         int b = s->heap[p];
         if (s->act[b] >= s->act[a]) break;
     {{ UpInv fuel /\ i > 0 /\ act b < act a }}
         s->heap[i] = b;
         s->hpos[b] = i;                    (heap_stmt_correct, hpos_stmt_correct)
         i = p;
         fuel--;
     {{ UpInv (fuel - 1): heuristic place h i b, position p }}
       }
     {{ UpInv fuel: heuristic h, position i with res = (h, i), at each break }}
       s->heap[i] = a;
       s->hpos[a] = i;                                         (heap_up_end_correct)
     {{ RepL (x <| hr := heap_up (hr x) i0 |>) /\ only the heuristic changed }}

   The loop ends: fuel decreases. *)
Lemma heap_up_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (i: nat),
  {{ m | RepL m sh N lss x /\ (i < N)%nat }}
    f_heap_up(sptr sh, vnat i)
  {{ m', v | HeurPost sh N lss x m (heap_up (hr x) i) m' }}.
Proof.
  intros sh N lss x i0 m [HRep Hi0]. pose proof (r_n HRep) as HN.
  pose proof (r_heur HRep) as Hok.
  assert (Ha: (atom_at (hr x) i0 < N)%nat).
  { apply (ho_heap Hok). assumption. }
  pose proof (ho_hsize Hok) as Hhsize.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_heap_up. cbn [fn_body fn_return].
    pose proof (r_heap HRep) as Fheap.
    pose proof (a_heap HRep) as Aheap.
    pose proof (r_hsize HRep) as Fhsize.
    (* int a = s->heap[i]; int fuel = s->hsize; *)
    run. clear Fheap Aheap Fhsize. unfold Swhile.
    apply exec_loop with (R := Peano.lt) (I := UpInv m sh N lss x i0)
      (a := hsize (hr x)).
    + apply lt_wf.
    + intros fuel le1 m1 HI.
      destruct HI as [Hfle (h & i & [Hs Ha' Hi Hfuel] & Hilt & Hres & HRep1) Hun1].
      pose proof (r_heur HRep1) as Hok1. cbn [set_hr hr] in Hok1.
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
           apply exec_skip. normal. run. cbn [up_loop] in Hres.
           (* if (i <= 0) break; *)
           eapply exec_if_le.
           ++ ev.
           ++ ev.
           ++ reflexivity.
           ++ lia.
           ++ (* at the top: break; and the end *)
              intros Htop.
              replace (i <=? 0)%nat with true in Hres
                by (symmetry; apply Nat.leb_le; lia).
              apply exec_break. abrupt.
              apply loopk_break. normal.
              apply (heap_up_end_correct m sh N lss x i0 h i (S fuel) _ m1).
              ** assumption.
              ** assumption.
              ** assumption.
              ** symmetry. assumption.
              ** assumption.
              ** constructor.
                 *** tmp.
                 *** tmp.
                 *** tmp.
                 *** tmp.
           ++ (* below the top: the parent at p *)
              intros Hipos.
              replace (i <=? 0)%nat with false in Hres
                by (symmetry; apply Nat.leb_gt; lia).
              apply exec_skip. normal.
              assert (Hp: (parent i <= i - 1)%nat).
              { apply Nat.Div0.div_le_upper_bound. lia. }
              assert (Hb: (tget (heap h) (parent i) < N)%nat).
              { apply (ho_heap Hok1). lia. }
              pose proof (ho_act Hok1 _ Hb) as Hactb.
              pose proof (ho_act Hok1 _ Ha) as Hacta.
              unfold act_lim in Hactb, Hacta.
              change (2 ^ 30)%Z with small_bound in Hactb, Hacta.
              pose proof (r_heap HRep1) as Fheap.
              pose proof (a_heap HRep1) as Aheap.
              pose proof (r_act HRep1) as Fact.
              pose proof (a_act HRep1) as Aact.
              cbn [set_hr hr] in Aheap, Aact.
              (* int p = (i - 1) / 2; *)
              apply exec_seq. apply exec_set with (vnat (parent i)).
              ** apply eval_parent.
                 --- tmp.
                 --- lia.
                 --- lia.
              ** normal.
                 (* int b = s->heap[p]; if (s->act[b] >= s->act[a]) break; *)
                 run.
                 eapply exec_if_ge.
                 --- ev.
                 --- ev.
                 --- reflexivity.
                 --- lia.
                 --- (* the parent is as active: break; and the end *)
                     intros Hle. apply Z.leb_le in Hle. rewrite Hle in Hres.
                     apply exec_break. abrupt.
                     apply loopk_break. normal.
                     apply (heap_up_end_correct m sh N lss x i0 h i (S fuel) _ m1).
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ symmetry. assumption.
                     +++ assumption.
                     +++ constructor.
                         ++++ tmp.
                         ++++ tmp.
                         ++++ tmp.
                         ++++ tmp.
                 --- (* the parent is less active: it moves down to i *)
                     intros Hgt. apply Z.leb_gt in Hgt. rewrite Hgt in Hres.
                     apply exec_skip. normal.
                     apply (up_move_correct m sh N lss x i0 h i fuel _ m1).
                     +++ assumption.
                     +++ lia.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ constructor.
                         *** tmp.
                         *** tmp.
                         *** tmp.
                         *** tmp.
                     +++ tmp.
                     +++ tmp.
      * intros Hno_fuel. destruct fuel as [|fuel].
        -- (* no fuel left: break; and the end *)
           apply exec_break. abrupt. apply loopk_break. normal.
           cbn [up_loop] in Hres.
           apply (heap_up_end_correct m sh N lss x i0 h i 0 _ m1).
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ symmetry. assumption.
           ++ assumption.
           ++ constructor.
              +++ tmp.
              +++ tmp.
              +++ tmp.
              +++ tmp.
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
        -- split.
           ++ assumption.
           ++ split.
              ** reflexivity.
              ** rewrite set_hr_same. assumption.
      * apply Mem.unchanged_on_refl.
Qed.

Lemma heap_up_fun: FunAt _heap_up f_heap_up.
Proof. apply find_fun. reflexivity. Qed.
