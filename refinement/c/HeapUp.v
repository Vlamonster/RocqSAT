(* heap_up moves the atom at a heap position up while its parent has a lower activity
   (heap_up). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Ctypesdefs Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Heur Propagate Step.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep RepHeur Rescale.
Import ListNotations.

(* C's division of a natural number k by 2. *)
Lemma div2_nat: forall (ge: genv) (m: mem) (k: nat), Z.of_nat k < 1073741824 ->
  sem_binary_operation ge Odiv (vint (Z.of_nat k)) Ctypesdefs.tint (vint 2)
    Ctypesdefs.tint m
  = Some (vint (Z.of_nat (k / 2))).
Proof.
  intros ge m k Hk. assert (Hmax: Int.max_signed = 2147483647) by reflexivity.
  assert (Hmin: Int.min_signed = -2147483648) by reflexivity.
  unfold sem_binary_operation, sem_div, sem_binarith, sem_cast, vint.
  simpl. cbv [Archi.ptr64]. simpl. change (fst (Nat.divmod k 1 0 1)) with (k / 2)%nat.
  (* k is not the least int, so C divides *)
  replace (Int.eq (Int.repr (Z.of_nat k)) (Int.repr Int.min_signed)) with false.
  - cbn - [Nat.div Int.divs]. unfold Int.divs. rewrite !Int.signed_repr by lia.
    rewrite Nat2Z.inj_div. rewrite Z.quot_div_nonneg by lia. reflexivity.
  - symmetry. apply Int.eq_false. intros Heq. apply (f_equal Int.signed) in Heq.
    rewrite !Int.signed_repr in Heq by lia. lia.
Qed.

(* The parent (i - 1) / 2 of the position i > 0, as C computes it. *)
Lemma eval_parent: forall (le: temp_env) (m: mem) (i: nat),
  le ! _i = Some (vint (Z.of_nat i)) -> (0 < i)%nat -> Z.of_nat i < 1073741824 ->
  eval_expr ge empty_env le m
    (Ebinop Odiv (Ebinop Osub (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint)
      (Econst_int (Int.repr 2) tint) tint)
    (vint (Z.of_nat ((i - 1) / 2))).
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

     {{ RepL (with_heur x h) /\ i < N /\ b < N }}
       th = s->heap; th[i] = b;                                         (rep_store_heap)
     {{ RepL (with_heur x (set_heap h i b)) /\ only the heuristic changed }}          *)
Lemma heap_stmt_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (h: Heur) (th ti tb: ident) (i b: nat) (le: temp_env)
  (m: mem) (Q: temp_env -> mem -> outcome -> Prop),
  RepL m S N lss (with_heur x h) lims lt -> (i < N)%nat -> (b < N)%nat ->
  le ! _s = Some (sptr S) -> le ! ti = Some (vint (Z.of_nat i)) ->
  le ! tb = Some (vint (Z.of_nat b)) -> ti <> th -> tb <> th ->
  (forall (m': mem), RepL m' S N lss (with_heur x (set_heap h i b)) lims lt ->
     Mem.unchanged_on (HeurFrame S) m m' ->
     Q (PTree.set th (Vptr (b_heap S) Ptrofs.zero) le) m' Out_normal) ->
  Exec ge le m (heap_stmt th ti tb) Q.
Proof.
  intros S N lss x lims h th ti tb i b le m Q HRep Hi Hb Hs Hti Htb Hith Hbth HQ.
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_heap _ _ _ _ _ _ _ HRep) as Fheap.
  pose proof (a_heap _ _ _ _ _ _ _ HRep) as Aheap.
  unfold heap_stmt. apply exec_seq.
  (* th = s->heap; *)
  eapply exec_set.
  - ev.
  - normal.
    assert (Hti': (PTree.set th (Vptr (b_heap S) Ptrofs.zero) le) ! ti
                  = Some (vint (Z.of_nat i))).
    { rewrite PTree.gso by assumption. assumption. }
    assert (Htb': (PTree.set th (Vptr (b_heap S) Ptrofs.zero) le) ! tb
                  = Some (vint (Z.of_nat b))).
    { rewrite PTree.gso by assumption. assumption. }
    (* th[i] = b; *)
    eapply exec_store.
    + evl.
    + ev.
    + reflexivity.
    + reflexivity.
    + ofs. bound.
    + ofs. cbn [cast_int_int].
      destruct (arr_storable m (b_heap S) N i _ (Z.of_nat b) Aheap Hi) as [m1 Hst].
      exists m1. split.
      * apply Hst.
      * apply HQ.
        -- apply (rep_store_heap m m1 S N lss (with_heur x h) lims i b HRep Hi Hb Hst).
        -- apply (store_unchanged _ m m m1 Mint32 (b_heap S) (4 * Z.of_nat i)
                    (vint (Z.of_nat b))).
           ++ apply Mem.unchanged_on_refl.
           ++ apply Hst.
           ++ apply heap_not_frame.
Qed.

(* The store of hpos_stmt, on the memory of the heuristic h:

     {{ RepL (with_heur x h) /\ b < N /\ i < N }}
       tp = s->hpos; tp[b] = i;                                         (rep_store_hpos)
     {{ RepL (with_heur x (set_hpos h b (Some i))) /\ only the heuristic changed }}   *)
Lemma hpos_stmt_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (h: Heur) (tp tb ti: ident) (b i: nat) (le: temp_env)
  (m: mem) (Q: temp_env -> mem -> outcome -> Prop),
  RepL m S N lss (with_heur x h) lims lt -> (b < N)%nat -> (i < N)%nat ->
  le ! _s = Some (sptr S) -> le ! tb = Some (vint (Z.of_nat b)) ->
  le ! ti = Some (vint (Z.of_nat i)) -> tb <> tp -> ti <> tp ->
  (forall (m': mem), RepL m' S N lss (with_heur x (set_hpos h b (Some i))) lims lt ->
     Mem.unchanged_on (HeurFrame S) m m' ->
     Q (PTree.set tp (Vptr (b_hpos S) Ptrofs.zero) le) m' Out_normal) ->
  Exec ge le m (hpos_stmt tp tb ti) Q.
Proof.
  intros S N lss x lims h tp tb ti b i le m Q HRep Hb Hi Hs Htb Hti Hbtp Hitp HQ.
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_hpos _ _ _ _ _ _ _ HRep) as Fhpos.
  pose proof (a_hpos _ _ _ _ _ _ _ HRep) as Ahpos.
  unfold hpos_stmt. apply exec_seq.
  (* tp = s->hpos; *)
  eapply exec_set.
  - ev.
  - normal.
    assert (Htb': (PTree.set tp (Vptr (b_hpos S) Ptrofs.zero) le) ! tb
                  = Some (vint (Z.of_nat b))).
    { rewrite PTree.gso by assumption. assumption. }
    assert (Hti': (PTree.set tp (Vptr (b_hpos S) Ptrofs.zero) le) ! ti
                  = Some (vint (Z.of_nat i))).
    { rewrite PTree.gso by assumption. assumption. }
    (* tp[b] = i; *)
    eapply exec_store.
    + evl.
    + ev.
    + reflexivity.
    + reflexivity.
    + ofs. bound.
    + ofs. cbn [cast_int_int].
      destruct (arr_storable m (b_hpos S) N b _ (Z.of_nat i) Ahpos Hb) as [m1 Hst].
      exists m1. split.
      * apply Hst.
      * apply HQ.
        -- apply (rep_store_hpos m m1 S N lss (with_heur x h) lims b (Some i) HRep Hb).
           ++ intros i' Hi'. injection Hi' as <-. assumption.
           ++ apply Hst.
        -- apply (store_unchanged _ m m m1 Mint32 (b_hpos S) (4 * Z.of_nat b)
                    (vint (Z.of_nat i))).
           ++ apply Mem.unchanged_on_refl.
           ++ apply Hst.
           ++ apply hpos_not_frame.
Qed.

(* Moving atom b to position i, then going on from position j with one less fuel, as
   the loops of heap_up (j = p) and heap_down (j = c) do. *)
Definition move_stmt (tj: ident): statement :=
  Ssequence (heap_stmt _t'4 _i _b)
    (Ssequence (hpos_stmt _t'3 _b _i)
      (Ssequence (Sset _i (Etempvar tj tint))
        (Sset _fuel
          (Ebinop Osub (Etempvar _fuel tint) (Econst_int (Int.repr 1) tint) tint)))).

(* The statements of move_stmt, on the memory of the heuristic h:

     {{ RepL (with_heur x h) /\ i < N /\ b < N }}
       s->heap[i] = b;
       s->hpos[b] = i;                      (heap_stmt_correct, hpos_stmt_correct)
       i = j;
       fuel--;
     {{ RepL (with_heur x (place h i b)) /\ only the heuristic changed }}         *)
Lemma move_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (h: Heur) (tj: ident) (i b j fuel: nat) (le: temp_env)
  (m m1: mem) (Q: temp_env -> mem -> outcome -> Prop),
  RepL m1 S N lss (with_heur x h) lims lt -> (i < N)%nat -> (b < N)%nat ->
  Mem.unchanged_on (HeurFrame S) m m1 ->
  le ! _s = Some (sptr S) -> le ! _i = Some (vint (Z.of_nat i)) ->
  le ! _b = Some (vint (Z.of_nat b)) -> le ! tj = Some (vint (Z.of_nat j)) ->
  le ! _fuel = Some (vint (Z.of_nat (Datatypes.S fuel))) ->
  tj <> _t'4 -> tj <> _t'3 ->
  (forall (m3: mem), RepL m3 S N lss (with_heur x (place h i b)) lims lt ->
     Mem.unchanged_on (HeurFrame S) m m3 ->
     Q (PTree.set _fuel (vint (Z.of_nat fuel))
          (PTree.set _i (vint (Z.of_nat j))
             (PTree.set _t'3 (Vptr (b_hpos S) Ptrofs.zero)
                (PTree.set _t'4 (Vptr (b_heap S) Ptrofs.zero) le))))
       m3 Out_normal) ->
  Exec ge le m1 (move_stmt tj) Q.
Proof.
  intros S N lss x lims h tj i b j fuel le m m1 Q HRep1 Hi Hb Hun1 Hs Hi' Hb' Hj Hfuel
    Htj4 Htj3 HQ.
  assert (Hfsub: Int.sub (Int.repr (Z.of_nat (Datatypes.S fuel))) (Int.repr 1)
                 = Int.repr (Z.of_nat fuel)).
  { rewrite sub_repr. f_equal. lia. }
  unfold move_stmt. apply exec_seq.
  (* s->heap[i] = b; *)
  apply (heap_stmt_correct (lt := lt) S N lss x lims h _ _ _ i b).
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
    apply (hpos_stmt_correct (lt := lt) S N lss x lims (set_heap h i b) _ _ _ b i).
    + assumption.
    + assumption.
    + assumption.
    + tmp.
    + tmp.
    + tmp.
    + discriminate.
    + discriminate.
    + intros m3 HRep3 Hun3. normal.
      assert (Hj': (PTree.set _t'3 (Vptr (b_hpos S) Ptrofs.zero)
                      (PTree.set _t'4 (Vptr (b_heap S) Ptrofs.zero) le)) ! tj
                   = Some (vint (Z.of_nat j))).
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

     {{ RepL (with_heur x h) /\ i < N /\ a < N }}
       s->heap[i] = a;
       s->hpos[a] = i;                      (heap_stmt_correct, hpos_stmt_correct)
     {{ RepL (with_heur x (place h i a)) /\ only the heuristic changed }}         *)
Lemma place_end_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (h: Heur) (i a: nat) (f: function) (le: temp_env)
  (m m1: mem),
  fn_return f = tvoid -> RepL m1 S N lss (with_heur x h) lims lt -> (i < N)%nat ->
  (a < N)%nat -> Mem.unchanged_on (HeurFrame S) m m1 ->
  le ! _s = Some (sptr S) -> le ! _i = Some (vint (Z.of_nat i)) ->
  le ! _a = Some (vint (Z.of_nat a)) ->
  Exec ge le m1 place_end_stmt (Returns f (fun (m': mem) (_: val) =>
    RepL m' S N lss (with_heur x (place h i a)) lims lt /\
    Mem.unchanged_on (HeurFrame S) m m')).
Proof.
  intros S N lss x lims h i a f le m m1 Hvoid HRep1 Hi Ha Hun1 Hs Hi' Ha'.
  unfold place_end_stmt. apply exec_seq.
  (* s->heap[i] = a; *)
  apply (heap_stmt_correct (lt := lt) S N lss x lims h _ _ _ i a).
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
    apply (hpos_stmt_correct (lt := lt) S N lss x lims (set_heap h i a) _ _ _ a i).
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

(* The end of heap_up, once the loop left the heuristic h and position i, which is what
   up_loop gives:

     {{ RepL (with_heur x h) /\ up_loop (hr x) a i0 (hsize (hr x)) = (h, i) }}
       s->heap[i] = a;
       s->hpos[a] = i;                                         (place_end_correct)
     {{ RepL (with_heur x (place h i a)), and place h i a = heap_up (hr x) i0 }} *)
Lemma heap_up_end_correct {lt: list Lit}: forall (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (i0: nat) (h: Heur) (i: nat)
  (le: temp_env) (m m1: mem),
  RepL m1 S N lss (with_heur x h) lims lt -> (i < N)%nat ->
  (atom_at (hr x) i0 < N)%nat ->
  up_loop (hr x) (atom_at (hr x) i0) i0 (hsize (hr x)) = (h, i) ->
  Mem.unchanged_on (HeurFrame S) m m1 ->
  le ! _s = Some (sptr S) -> le ! _i = Some (vint (Z.of_nat i)) ->
  le ! _a = Some (vint (Z.of_nat (atom_at (hr x) i0))) ->
  Exec ge le m1 heap_up_end (Returns f_heap_up (fun (m': mem) (_: val) =>
    RepL m' S N lss (with_heur x (heap_up (hr x) i0)) lims lt /\
    Mem.unchanged_on (HeurFrame S) m m')).
Proof.
  intros S N lss x lims i0 h i le m m1 HRep1 Hi Ha Hres Hun1 Hs Hi' Ha'.
  unfold heap_up. fold (atom_at (hr x) i0). rewrite Hres.
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

(* The invariant of the loop of heap_up at fuel, for the memory m of the call and the
   atom a moved up from position i0: the temporaries hold s, a, fuel and a position i
   below N, the memory m1 represents x with a heuristic h from which up_loop gives what
   it gives from the start (the loop follows the recursion of up_loop), and m1 is m but
   for the heuristic. *)
Record UpInv (m: mem) (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (lt: list Lit) (i0: nat) (fuel: nat) (le: temp_env) (m1: mem):
  Prop := {
  upi_s: le ! _s = Some (sptr S);
  upi_a: le ! _a = Some (vint (Z.of_nat (atom_at (hr x) i0)));
  upi_fuel: le ! _fuel = Some (vint (Z.of_nat fuel));
  upi_fuel_le: (fuel <= N)%nat;
  upi_pos: exists (h: Heur) (i: nat),
    le ! _i = Some (vint (Z.of_nat i)) /\ (i < N)%nat /\
    up_loop h (atom_at (hr x) i0) i fuel
    = up_loop (hr x) (atom_at (hr x) i0) i0 (hsize (hr x)) /\
    RepL m1 S N lss (with_heur x h) lims lt;
  upi_frame: Mem.unchanged_on (HeurFrame S) m m1;
}.

(* The statements of the loop of heap_up that move the parent b at p down to i. *)
Definition up_move: statement :=
  drop_stmts 5 (loop_body (first_stmt (drop_stmts 2 (fn_body f_heap_up)))).

(* Moving the parent b at p = (i - 1) / 2, less active than a, down to position i; the
   loop goes on from p with one less fuel:

     {{ UpInv (fuel + 1): heuristic h, position i /\ 0 < i /\ act b < act a }}
       s->heap[i] = b; s->hpos[b] = i; i = p; fuel--;               (move_correct)
     {{ UpInv fuel: heuristic place h i b, position p }}                          *)
Lemma up_move_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (i0: nat) (h: Heur) (i fuel: nat) (le: temp_env)
  (m m1: mem) (Q: temp_env -> mem -> outcome -> Prop),
  RepL m1 S N lss (with_heur x h) lims lt -> (0 < i < N)%nat ->
  (Datatypes.S fuel <= N)%nat -> (tget (heap h) ((i - 1) / 2) < N)%nat ->
  up_loop (place h i (tget (heap h) ((i - 1) / 2))) (atom_at (hr x) i0) ((i - 1) / 2)
    fuel
  = up_loop (hr x) (atom_at (hr x) i0) i0 (hsize (hr x)) ->
  Mem.unchanged_on (HeurFrame S) m m1 ->
  le ! _s = Some (sptr S) -> le ! _a = Some (vint (Z.of_nat (atom_at (hr x) i0))) ->
  le ! _i = Some (vint (Z.of_nat i)) -> le ! _p = Some (vint (Z.of_nat ((i - 1) / 2))) ->
  le ! _b = Some (vint (Z.of_nat (tget (heap h) ((i - 1) / 2)))) ->
  le ! _fuel = Some (vint (Z.of_nat (Datatypes.S fuel))) ->
  Exec ge le m1 up_move
    (LoopK Peano.lt (UpInv m S N lss x lims lt i0) Q (Datatypes.S fuel)).
Proof.
  intros S N lss x lims i0 h i fuel le m m1 Q HRep1 Hi Hfle Hb Hres Hun1 Hs Ha Hi' Hp
    Hb' Hfuel.
  assert (Hpi: ((i - 1) / 2 <= i - 1)%nat).
  { apply Nat.Div0.div_le_upper_bound. lia. }
  unfold up_move, f_heap_up. cbn [fn_body drop_stmts first_stmt loop_body Swhile].
  fold (move_stmt _p).
  apply (move_correct (lt := lt) S N lss x lims h _p i (tget (heap h) ((i - 1) / 2))
           ((i - 1) / 2) fuel le m m1).
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
    intros m3 HRep3 Hun3. apply loopk_next with fuel.
    + lia.
    + constructor.
      * tmp.
      * tmp.
      * tmp.
      * lia.
      * exists (place h i (tget (heap h) ((i - 1) / 2))), ((i - 1) / 2)%nat. split.
        -- tmp.
        -- split.
           ++ lia.
           ++ split.
              ** assumption.
              ** apply HRep3.
      * assumption.
Qed.

(* heap_up moves the atom a at position i0 up: while the parent b at p = (i - 1) / 2 of
   its position i has a lower activity, b moves down to i, at most hsize times; then a
   goes to the position left. Only the heuristic changes. Writing a for
   atom_at (hr x) i0 and res for up_loop (hr x) a i0 (hsize (hr x)):

     {{ RepL m S N lss x lims lt /\ i0 < N }}
       int a = s->heap[i];
       int fuel = s->hsize;
     {{ UpInv (hsize (hr x)): heuristic hr x, i = i0 }}
       while (fuel > 0) {
     {{ UpInv fuel: heuristic h, position i /\ fuel > 0 }}
         if (i <= 0) break;
         int p = (i - 1) / 2;                                               (div2_nat)
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
     {{ RepL (with_heur x (heap_up (hr x) i0)) /\ only the heuristic changed }}

   The loop ends: fuel decreases. *)
Lemma heap_up_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (i: nat),
  {{ m | RepL m S N lss x lims lt /\ (i < N)%nat }}
    f_heap_up(sptr S, vint (Z.of_nat i))
  {{ m', v | RepL m' S N lss (with_heur x (heap_up (hr x) i)) lims lt /\
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
  - unfold f_heap_up. cbn [fn_body fn_return].
    pose proof (r_heap _ _ _ _ _ _ _ HRep) as Fheap.
    pose proof (a_heap _ _ _ _ _ _ _ HRep) as Aheap.
    pose proof (r_hsize _ _ _ _ _ _ _ HRep) as Fhsize.
    (* int a = s->heap[i]; int fuel = s->hsize; *)
    run. clear Fheap Aheap Fhsize. unfold Swhile.
    apply exec_loop with (R := Peano.lt) (I := UpInv m S N lss x lims lt i0)
      (a := hsize (hr x)).
    + apply lt_wf.
    + intros fuel le1 m1 HI.
      destruct HI as [Hs Ha' Hfuel Hfle (h & i & Hi & Hilt & Hres & HRep1) Hun1].
      pose proof (r_heur _ _ _ _ _ _ _ HRep1) as Hok1. cbn [with_heur hr] in Hok1.
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
           cbn [up_loop] in Hres.
           apply (heap_up_end_correct (lt := lt) S N lss x lims i0 h i _ m m1).
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ symmetry. assumption.
           ++ assumption.
           ++ tmp.
           ++ tmp.
           ++ tmp.
        -- replace (zcmp Cgt (Z.of_nat (Datatypes.S fuel)) 0) with true
             by (symmetry; cbn [zcmp]; apply Z.ltb_lt; lia).
           cbv beta iota. apply exec_skip. normal. run.
           (* if (i <= 0) break; *)
           eapply (exec_if_cmp _ _ _ Cle).
           ++ ev.
           ++ ev.
           ++ reflexivity.
           ++ reflexivity.
           ++ unfold Small. lia.
           ++ unfold Small. lia.
           ++ cbn [zcmp]. cbn [up_loop] in Hres.
              destruct (Nat.leb_spec i 0) as [Hi0' | Hipos].
              ** (* at the top: break; and the end *)
                 replace (Z.of_nat i <=? 0) with true by (symmetry; apply Z.leb_le; lia).
                 apply exec_break. abrupt.
                 apply loopk_break. normal.
                 apply (heap_up_end_correct (lt := lt) S N lss x lims i0 h i _ m m1).
                 --- assumption.
                 --- assumption.
                 --- assumption.
                 --- symmetry. assumption.
                 --- assumption.
                 --- tmp.
                 --- tmp.
                 --- tmp.
              ** (* below the top: the parent at p *)
                 replace (Z.of_nat i <=? 0) with false
                   by (symmetry; apply Z.leb_gt; lia).
                 apply exec_skip. normal.
                 assert (Hp: ((i - 1) / 2 <= i - 1)%nat).
                 { apply Nat.Div0.div_le_upper_bound. lia. }
                 assert (Hb: (tget (heap h) ((i - 1) / 2) < N)%nat).
                 { apply (ho_heap _ _ Hok1). lia. }
                 pose proof (ho_act _ _ Hok1 _ Hb) as Hactb.
                 pose proof (ho_act _ _ Hok1 _ Ha) as Hacta.
                 unfold act_lim in Hactb, Hacta.
                 change (2 ^ 30)%Z with 1073741824 in Hactb, Hacta.
                 pose proof (r_heap _ _ _ _ _ _ _ HRep1) as Fheap.
                 pose proof (a_heap _ _ _ _ _ _ _ HRep1) as Aheap.
                 pose proof (r_act _ _ _ _ _ _ _ HRep1) as Fact.
                 pose proof (a_act _ _ _ _ _ _ _ HRep1) as Aact.
                 cbn [with_heur hr] in Aheap, Aact.
                 (* int p = (i - 1) / 2; *)
                 apply exec_seq. apply exec_set with (vint (Z.of_nat ((i - 1) / 2))).
                 --- apply eval_parent.
                     +++ tmp.
                     +++ assumption.
                     +++ lia.
                 --- normal.
                     (* int b = s->heap[p]; if (s->act[b] >= s->act[a]) break; *)
                     run.
                     eapply (exec_if_cmp _ _ _ Cge).
                     +++ ev.
                     +++ ev.
                     +++ reflexivity.
                     +++ reflexivity.
                     +++ unfold Small. lia.
                     +++ unfold Small. lia.
                     +++ cbn [zcmp].
                         destruct (Z.leb_spec (tget (act h) (atom_at (hr x) i0))
                                     (tget (act h) (tget (heap h) ((i - 1) / 2))))
                           as [Hle | Hgt].
                         *** (* the parent is as active: break; and the end *)
                             apply exec_break.
                             abrupt.
                             apply loopk_break. normal.
                             apply (heap_up_end_correct (lt := lt) S N lss x lims i0 h
                                      i _ m m1).
                             ---- assumption.
                             ---- assumption.
                             ---- assumption.
                             ---- symmetry. assumption.
                             ---- assumption.
                             ---- tmp.
                             ---- tmp.
                             ---- tmp.
                         *** (* the parent is less active: it moves down to i *)
                             apply exec_skip. normal.
                             apply (up_move_correct (lt := lt) S N lss x lims i0 h i
                                      fuel _ m m1).
                             ---- assumption.
                             ---- lia.
                             ---- assumption.
                             ---- assumption.
                             ---- assumption.
                             ---- assumption.
                             ---- tmp.
                             ---- tmp.
                             ---- tmp.
                             ---- tmp.
                             ---- tmp.
                             ---- tmp.
    + (* The invariant holds at the start: heuristic hr x, position i0. *)
      constructor.
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

Lemma heap_up_fun: exists (b: block),
  Genv.find_symbol ge _heap_up = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_heap_up).
Proof. apply find_fun. reflexivity. Qed.
