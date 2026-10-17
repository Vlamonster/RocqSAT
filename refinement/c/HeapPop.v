(* heap_pop takes the atom at the top out of the non-empty heap (heap_pop). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Ctypesdefs Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Heur Propagate Step.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep RepHeur Rescale HeapUp
  HeapDown.
Import ListNotations.

(* The atom heap_pop takes is the one at the top. *)
Lemma pop_atom: forall (h: Heur), snd (heap_pop h) = atom_at h 0.
Proof.
  intros h. unfold heap_pop. destruct (0 <? hsize h - 1)%nat.
  - reflexivity.
  - reflexivity.
Qed.

(* The heuristic h without its top atom a, in a heap one smaller, before the last atom
   moves to the top. *)
Definition pop_top (h: Heur): Heur :=
  set_hpos (set_hsize h (hsize h - 1)%nat) (atom_at h 0) None.

(* What holds after the branch of heap_pop, for the memory m of the call: a still holds
   the top atom, and the memory represents the heuristic of the model. *)
Definition PopPost (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx) (lims: list nat)
  (lt: list Lit) (m: mem) (le': temp_env) (m': mem) (out: outcome): Prop :=
  out = Out_normal /\ le' ! _a = Some (vint (Z.of_nat (atom_at (hr x) 0))) /\
  RepL m' S N lss (with_heur x (fst (heap_pop (hr x)))) lims lt /\
  Mem.unchanged_on (HeurFrame S) m m'.

(* The branch of heap_pop for a heap that is not empty after the top atom is taken. *)
Definition pop_down: statement :=
  then_stmt (first_stmt (drop_stmts 4 (fn_body f_heap_pop))).

(* With n = hsize - 1 > 0 atoms left, the last one, b at n, goes to the top and moves
   down:

     {{ RepL (with_heur x (pop_top (hr x))) /\ 0 < n }}
       int b = s->heap[n];
       s->heap[0] = b;                                                  (rep_store_heap)
       s->hpos[b] = 0;                                                  (rep_store_hpos)
     {{ RepL (with_heur x (place (pop_top (hr x)) 0 b)) }}
       heap_down(s, 0);                                             (heap_down_correct)
     {{ PopPost: heuristic heap_down (place (pop_top (hr x)) 0 b) 0 }}            *)
Lemma pop_down_correct {lt: list Lit}: forall (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (le: temp_env) (m m1: mem),
  RepL m1 S N lss (with_heur x (pop_top (hr x))) lims lt ->
  (0 < hsize (hr x) - 1)%nat -> (hsize (hr x) <= N)%nat ->
  Mem.unchanged_on (HeurFrame S) m m1 ->
  le ! _s = Some (sptr S) -> le ! _a = Some (vint (Z.of_nat (atom_at (hr x) 0))) ->
  le ! _n = Some (vint (Z.of_nat (hsize (hr x) - 1)%nat)) ->
  Exec ge le m1 pop_down (PopPost S N lss x lims lt m).
Proof.
  intros S N lss x lims le m m1 HRep1 Hn Hhsize Hun1 Hs Ha Hn'.
  pose proof (r_n _ _ _ _ _ _ _ HRep1) as HN.
  pose proof (r_heur _ _ _ _ _ _ _ HRep1) as Hok1.
  unfold pop_top, set_hpos, set_hsize in Hok1. cbn [with_heur hr] in Hok1.
  assert (Hb: (tget (heap (hr x)) (hsize (hr x) - 1)%nat < N)%nat).
  { apply (ho_heap _ _ Hok1). lia. }
  assert (H0N: (0 < N)%nat) by lia.
  pose proof (r_heap _ _ _ _ _ _ _ HRep1) as Fheap.
  pose proof (a_heap _ _ _ _ _ _ _ HRep1) as Aheap.
  pose proof (r_hpos _ _ _ _ _ _ _ HRep1) as Fhpos.
  pose proof (a_hpos _ _ _ _ _ _ _ HRep1) as Ahpos.
  unfold pop_top, set_hpos, set_hsize in Aheap, Ahpos.
  cbn [with_heur hr heap hpos] in Aheap, Ahpos.
  set (b := tget (heap (hr x)) (hsize (hr x) - 1)%nat) in *.
  unfold pop_down, f_heap_pop. cbn [fn_body drop_stmts first_stmt then_stmt].
  (* the index 0 as a natural number, for the loads and stores *)
  change (Econst_int (Int.repr 0) tint) with (Econst_int (Int.repr (Z.of_nat 0)) tint).
  (* int b = s->heap[n]; *)
  run.
  (* s->heap[0] = b; *)
  eapply exec_store.
  - evl.
  - ev.
  - reflexivity.
  - reflexivity.
  - ofs. bound.
  - ofs. cbn [cast_int_int].
    destruct (arr_storable m1 (b_heap S) N 0 _ (Z.of_nat b) Aheap H0N)
      as [m2 Hst2].
    exists m2. split.
    + apply Hst2.
    + normal.
      pose proof (rep_store_heap m1 m2 S N lss _ lims 0 b HRep1 H0N Hb Hst2)
        as HRep2.
      pose proof (r_hpos _ _ _ _ _ _ _ HRep2) as Fhpos2.
      pose proof (a_hpos _ _ _ _ _ _ _ HRep2) as Ahpos2.
      clear Fheap Aheap Fhpos Ahpos.
      (* s->hpos[b] = 0; *)
      run. eapply exec_store.
      * evl.
      * ev.
      * reflexivity.
      * reflexivity.
      * ofs. bound.
      * ofs. cbn [cast_int_int].
        destruct (arr_storable m2 (b_hpos S) N b _ (enc_pos (Some 0%nat)) Ahpos2 Hb)
          as [m3 Hst3].
        exists m3. split.
        -- apply Hst3.
        -- normal.
           pose proof (rep_store_hpos m2 m3 S N lss _ lims b (Some 0%nat) HRep2 Hb)
             as HRep3.
           assert (Hun3: Mem.unchanged_on (HeurFrame S) m m3).
           { apply (store_unchanged _ m m2 m3 Mint32 (b_hpos S) (4 * Z.of_nat b)
                      (vint (enc_pos (Some 0%nat)))).
             - apply (store_unchanged _ m m1 m2 Mint32 (b_heap S) (4 * Z.of_nat 0)
                        (vint (Z.of_nat b))).
               + assumption.
               + assumption.
               + apply heap_not_frame.
             - assumption.
             - apply hpos_not_frame. }
           (* heap_down(s, 0); *)
           call heap_down_fun. eapply call_weaken.
           ++ apply (heap_down_correct (lt := lt) S N lss
                       (with_heur x (place (pop_top (hr x)) 0 b)) lims 0 m3).
              split.
              ** apply HRep3.
                 --- intros i Hi. injection Hi as <-. assumption.
                 --- apply Hst3.
              ** assumption.
           ++ intros m4 v4 [HRep4 Hun4]. split.
              ** reflexivity.
              ** split.
                 --- tmp.
                 --- split.
                     +++ unfold heap_pop.
                         replace (0 <? hsize (hr x) - 1)%nat with true
                           by (symmetry; apply Nat.ltb_lt; assumption).
                         apply HRep4.
                     +++ apply (Mem.unchanged_on_trans _ m m3 m4).
                         *** assumption.
                         *** assumption.
Qed.

(* heap_pop takes the top atom a out of the heap: the heap gets one smaller, a gets no
   position, and if atoms are left, the last one goes to the top and moves down. Only
   the heuristic changes. Writing n for hsize (hr x) - 1:

     {{ RepL m S N lss x lims lt /\ 0 < hsize (hr x) }}
       int a = s->heap[0];
       int n = s->hsize - 1;
       s->hsize = n;                                                   (rep_store_hsize)
       s->hpos[a] = -1;                                                 (rep_store_hpos)
     {{ RepL (with_heur x (pop_top (hr x))) }}
       if (n > 0) { ... }                                            (pop_down_correct)
     {{ PopPost: a, and the heuristic fst (heap_pop (hr x)) }}
       return a;
     {{ RepL (with_heur x (fst (heap_pop (hr x)))) /\ result = snd (heap_pop (hr x))
        /\ only the heuristic changed }}                                            *)
Lemma heap_pop_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat),
  {{ m | RepL m S N lss x lims lt /\ (0 < hsize (hr x))%nat }}
    f_heap_pop(sptr S)
  {{ m', v | RepL m' S N lss (with_heur x (fst (heap_pop (hr x)))) lims lt /\
             v = vint (Z.of_nat (snd (heap_pop (hr x)))) /\
             Mem.unchanged_on (HeurFrame S) m m' }}.
Proof.
  intros S N lss x lims m [HRep Hpos]. pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_heur _ _ _ _ _ _ _ HRep) as Hok.
  pose proof (ho_hsize _ _ Hok) as Hhsize.
  assert (Ha: (atom_at (hr x) 0 < N)%nat).
  { apply (ho_heap _ _ Hok). lia. }
  assert (Ha0: (tget (heap (hr x)) 0 < N)%nat) by apply Ha.
  assert (Hsub: Int.sub (Int.repr (Z.of_nat (hsize (hr x)))) (Int.repr 1)
                = Int.repr (Z.of_nat (hsize (hr x) - 1)%nat)).
  { rewrite sub_repr. f_equal. lia. }
  assert (Hneg: Int.neg (Int.repr 1) = Int.repr (enc_pos None)).
  { reflexivity. }
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_heap_pop. cbn [fn_body fn_return].
    (* the index 0 as a natural number, for the loads *)
    change (Econst_int (Int.repr 0) tint) with (Econst_int (Int.repr (Z.of_nat 0)) tint).
    pose proof (r_heap _ _ _ _ _ _ _ HRep) as Fheap.
    pose proof (a_heap _ _ _ _ _ _ _ HRep) as Aheap.
    pose proof (r_hsize _ _ _ _ _ _ _ HRep) as Fhsize.
    (* int a = s->heap[0]; int n = s->hsize - 1; *)
    run.
    (* s->hsize = n; *)
    eapply exec_store.
    + evl.
    + ev.
    + reflexivity.
    + reflexivity.
    + fofs. bound.
    + fofs. cbn [cast_int_int]. rewrite Hsub.
      destruct (fld_storable m (b_s S) 272 Mint32 _
                  (vint (Z.of_nat (hsize (hr x) - 1)%nat)) Fhsize) as [m2 Hst2].
      exists m2. split.
      * apply Hst2.
      * normal.
        assert (Hle: (hsize (hr x) - 1 <= N)%nat) by lia.
        pose proof (rep_store_hsize m m2 S N lss x lims _ HRep Hle Hst2) as HRep2.
        pose proof (r_hpos _ _ _ _ _ _ _ HRep2) as Fhpos.
        pose proof (a_hpos _ _ _ _ _ _ _ HRep2) as Ahpos.
        clear Fheap Aheap Fhsize.
        (* s->hpos[a] = -1; *)
        run. eapply exec_store.
        -- evl.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- ofs. bound.
        -- ofs. cbn [cast_int_int].
           destruct (arr_storable m2 (b_hpos S) N (atom_at (hr x) 0) _ (enc_pos None)
                       Ahpos Ha) as [m3 Hst3].
           exists m3. split.
           ++ apply Hst3.
           ++ normal.
              assert (Hnone: forall (i: nat), None = Some i -> (i < N)%nat).
              { intros i Hi. discriminate. }
              pose proof (rep_store_hpos m2 m3 S N lss _ lims _ None HRep2 Ha Hnone Hst3)
                as HRep3.
              assert (Hun3: Mem.unchanged_on (HeurFrame S) m m3).
              { apply (store_unchanged _ m m2 m3 Mint32 (b_hpos S)
                         (4 * Z.of_nat (atom_at (hr x) 0)) (vint (enc_pos None))).
                - apply (store_unchanged _ m m m2 Mint32 (b_s S) 272
                           (vint (Z.of_nat (hsize (hr x) - 1)%nat))).
                  + apply Mem.unchanged_on_refl.
                  + assumption.
                  + apply s_not_frame.
                - assumption.
                - apply hpos_not_frame. }
              (* if (n > 0) ...; both branches end in PopPost *)
              apply exec_seq. apply exec_weaken with (Q := PopPost S N lss x lims lt m).
              ** eapply (exec_if_cmp _ _ _ Cgt).
                 --- ev.
                 --- ev.
                 --- reflexivity.
                 --- reflexivity.
                 --- unfold Small. lia.
                 --- unfold Small. lia.
                 --- cbn [zcmp].
                     destruct (Nat.ltb_spec 0 (hsize (hr x) - 1)) as [Hn | Hn].
                     +++ (* atoms are left: the last one goes to the top *)
                         replace (Z.of_nat 0 <? Z.of_nat (hsize (hr x) - 1)%nat)
                           with true by (symmetry; apply Z.ltb_lt; lia).
                         apply (pop_down_correct (lt := lt) S N lss x lims _ m m3).
                         *** apply HRep3.
                         *** assumption.
                         *** assumption.
                         *** assumption.
                         *** tmp.
                         *** tmp.
                         *** tmp.
                     +++ (* the heap is empty now *)
                         replace (Z.of_nat 0 <? Z.of_nat (hsize (hr x) - 1)%nat)
                           with false by (symmetry; apply Z.ltb_ge; lia).
                         apply exec_skip. split.
                         *** reflexivity.
                         *** split.
                             ---- tmp.
                             ---- split.
                                  ++++ unfold heap_pop.
                                       replace (0 <? hsize (hr x) - 1)%nat with false
                                         by (symmetry; apply Nat.ltb_ge; assumption).
                                       apply HRep3.
                                  ++++ assumption.
              ** (* return a; *)
                 intros le4 m4 out (-> & Ha4 & HRep4 & Hun4). apply seqk_normal.
                 eapply exec_return.
                 --- ev.
                 --- exists (vint (Z.of_nat (atom_at (hr x) 0))). split.
                     +++ apply result_int.
                     +++ split.
                         *** assumption.
                         *** split.
                             ---- rewrite pop_atom. reflexivity.
                             ---- assumption.
Qed.

Lemma heap_pop_fun: exists (b: block),
  Genv.find_symbol ge _heap_pop = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_heap_pop).
Proof. apply find_fun. reflexivity. Qed.
