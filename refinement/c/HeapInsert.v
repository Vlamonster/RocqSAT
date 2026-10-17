(* heap_insert puts an atom in the heap, unless it is there, is not decided on, or the
   heap is full (heap_insert). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Ctypesdefs Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Heur Propagate Step.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep RepHeur Rescale HeapUp.
Import ListNotations.

(* A return without a value:

       ---------------------------------------- (exec_return_none)
       {{ Q (return) }} return; {{ Q }}                                             *)
Lemma exec_return_none: forall (le: temp_env) (m: mem)
  (Q: temp_env -> mem -> outcome -> Prop),
  Q le m (Out_return None) -> Exec ge le m (Sreturn None) Q.
Proof.
  intros le m Q HQ. exists le, m, (Out_return None). split.
  - apply exec_Sreturn_none.
  - assumption.
Qed.

(* Returning from heap_insert with the heuristic unchanged, when the model leaves it. *)
Lemma insert_return_same {lt: list Lit}: forall (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (a: nat) (le: temp_env) (m: mem),
  RepL m S N lss x lims lt -> heap_insert (hr x) N a = hr x ->
  Returns f_heap_insert (fun (m': mem) (_: val) =>
    RepL m' S N lss (with_heur x (heap_insert (hr x) N a)) lims lt /\
    Mem.unchanged_on (HeurFrame S) m m') le m (Out_return None).
Proof.
  intros S N lss x lims a le m HRep Hsame. exists Vundef. split.
  - reflexivity.
  - split.
    + rewrite Hsame, with_heur_hr. assumption.
    + apply Mem.unchanged_on_refl.
Qed.

(* The heuristic h with atom a put at its end, in a heap one larger. *)
Definition put_last (h: Heur) (a: nat): Heur :=
  mkHeur (act h) (inc h) (tset (heap h) (hsize h) a) (tset (hpos h) a (Some (hsize h)))
    (Datatypes.S (hsize h)) (dlit h).

(* The statements of heap_insert that put a at the end and move it up. *)
Definition insert_put: statement := drop_stmts 4 (fn_body f_heap_insert).

(* Putting atom a, not in the heap and with a literal l to decide on, at the end
   n = hsize (hr x) < N of the heap, and moving it up:

     {{ RepL x /\ hpos a = None /\ dlit a = Some l /\ n < N }}
       s->heap[n] = a;
       s->hpos[a] = n;                      (heap_stmt_correct, hpos_stmt_correct)
       s->hsize = n + 1;                                              (rep_store_hsize)
     {{ RepL (with_heur x (put_last (hr x) a)) }}
       heap_up(s, n);                                                 (heap_up_correct)
     {{ RepL (with_heur x (heap_up (put_last (hr x) a) n)) /\ only the heuristic
        changed, and heap_up (put_last (hr x) a) n = heap_insert (hr x) N a }}      *)
Lemma insert_put_correct {lt: list Lit}: forall (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (a: nat) (l: Lit) (le: temp_env)
  (m: mem),
  RepL m S N lss x lims lt -> (a < N)%nat -> tget (hpos (hr x)) a = None ->
  tget (dlit (hr x)) a = Some l -> (hsize (hr x) < N)%nat ->
  le ! _s = Some (sptr S) -> le ! _a = Some (vint (Z.of_nat a)) ->
  le ! _n = Some (vint (Z.of_nat (hsize (hr x)))) ->
  Exec ge le m insert_put (Returns f_heap_insert (fun (m': mem) (_: val) =>
    RepL m' S N lss (with_heur x (heap_insert (hr x) N a)) lims lt /\
    Mem.unchanged_on (HeurFrame S) m m')).
Proof.
  intros S N lss x lims a l le m HRep Ha Hpos Hdl Hroom Hs Ha' Hn.
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  (* the model puts a at the end and moves it up *)
  assert (Hput: heap_insert (hr x) N a = heap_up (put_last (hr x) a) (hsize (hr x))).
  { unfold heap_insert. rewrite Hpos, Hdl.
    replace (N <=? hsize (hr x))%nat with false
      by (symmetry; apply Nat.leb_gt; assumption).
    reflexivity. }
  rewrite Hput. unfold insert_put, f_heap_insert. cbn [fn_body drop_stmts].
  fold (heap_stmt _t'2 _n _a) (hpos_stmt _t'1 _a _n). apply exec_seq.
  (* s->heap[n] = a; *)
  apply (heap_stmt_correct (lt := lt) S N lss x lims (hr x) _ _ _ (hsize (hr x)) a).
  - rewrite with_heur_hr. assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - discriminate.
  - discriminate.
  - intros m2 HRep2 Hun2. normal. apply exec_seq.
    (* s->hpos[a] = n; *)
    apply (hpos_stmt_correct (lt := lt) S N lss x lims (set_heap (hr x) (hsize (hr x)) a)
             _ _ _ a (hsize (hr x))).
    + assumption.
    + assumption.
    + assumption.
    + tmp.
    + tmp.
    + tmp.
    + discriminate.
    + discriminate.
    + intros m3 HRep3 Hun3. normal.
      pose proof (r_hsize _ _ _ _ _ _ _ HRep3) as Fhsize.
      assert (Hsucc: Int.add (Int.repr (Z.of_nat (hsize (hr x)))) (Int.repr 1)
                     = Int.repr (Z.of_nat (Datatypes.S (hsize (hr x))))).
      { rewrite add_repr. f_equal. lia. }
      (* s->hsize = n + 1; *)
      apply exec_seq. eapply exec_store.
      * evl.
      * ev.
      * reflexivity.
      * reflexivity.
      * fofs. bound.
      * fofs. cbn [cast_int_int]. rewrite Hsucc.
        destruct (fld_storable m3 (b_s S) 272 Mint32 _
                    (vint (Z.of_nat (Datatypes.S (hsize (hr x))))) Fhsize) as [m4 Hst4].
        exists m4. split.
        -- apply Hst4.
        -- normal.
           pose proof (rep_store_hsize m3 m4 S N lss _ lims (Datatypes.S (hsize (hr x)))
                         HRep3 Hroom Hst4) as HRep4.
           assert (Hun4: Mem.unchanged_on (HeurFrame S) m m4).
           { apply (store_unchanged _ m m3 m4 Mint32 (b_s S) 272
                      (vint (Z.of_nat (Datatypes.S (hsize (hr x)))))).
             - apply (Mem.unchanged_on_trans _ m m2 m3).
               + assumption.
               + assumption.
             - assumption.
             - apply s_not_frame. }
           (* heap_up(s, n); *)
           call heap_up_fun. eapply call_weaken.
           ++ apply (heap_up_correct (lt := lt) S N lss (with_heur x (put_last (hr x) a))
                       lims (hsize (hr x)) m4).
              split.
              ** apply HRep4.
              ** assumption.
           ++ intros m5 v5 [HRep5 Hun5]. exists Vundef. split.
              ** reflexivity.
              ** split.
                 --- apply HRep5.
                 --- apply (Mem.unchanged_on_trans _ m m4 m5).
                     +++ assumption.
                     +++ assumption.
Qed.

(* heap_insert puts atom a at the end hs = hsize (hr x) of the heap and moves it up, if
   it is not in the heap, has a literal to decide on and the heap has room. Only the
   heuristic changes:

     {{ RepL m S N lss x lims lt /\ a < N }}
       if (s->hpos[a] >= 0) return;
     {{ hpos a = None }}
       if (s->dlit[a] < 0) return;
     {{ dlit a = Some l }}
       int n = s->hsize;
       if (n >= s->nv) return;
     {{ n = hs < N }}
       s->heap[n] = a; s->hpos[a] = n; s->hsize = n + 1;
       heap_up(s, n);                                             (insert_put_correct)
     {{ RepL (with_heur x (heap_up (put_last (hr x) a) hs)) /\ only the heuristic
        changed }}

   and each return leaves the heuristic as the model does (insert_return_same). *)
Lemma heap_insert_correct {lt: list Lit}: forall (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (a: nat),
  {{ m | RepL m S N lss x lims lt /\ (a < N)%nat }}
    f_heap_insert(sptr S, vint (Z.of_nat a))
  {{ m', v | RepL m' S N lss (with_heur x (heap_insert (hr x) N a)) lims lt /\
             Mem.unchanged_on (HeurFrame S) m m' }}.
Proof.
  intros S N lss x lims a m [HRep Ha]. pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_heur _ _ _ _ _ _ _ HRep) as Hok.
  pose proof (ho_hsize _ _ Hok) as Hhsize.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_heap_insert. cbn [fn_body fn_return].
    pose proof (r_hpos _ _ _ _ _ _ _ HRep) as Fhpos.
    pose proof (a_hpos _ _ _ _ _ _ _ HRep) as Ahpos.
    (* if (s->hpos[a] >= 0) return; *)
    run. eapply (exec_if_cmp _ _ _ Cge).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + destruct (tget (hpos (hr x)) a) as [i|] eqn:Hpos.
      * pose proof (ho_hpos _ _ Hok a i Ha Hpos) as Hi. unfold enc_pos, Small. lia.
      * unfold enc_pos, Small. lia.
    + unfold Small. lia.
    + cbn [zcmp]. destruct (tget (hpos (hr x)) a) as [i|] eqn:Hpos.
      * (* in the heap: return *)
        replace (0 <=? enc_pos (Some i)) with true
          by (symmetry; apply Z.leb_le; unfold enc_pos; lia).
        apply exec_return_none. ret.
        apply (insert_return_same S N lss x lims a).
        -- assumption.
        -- unfold heap_insert. rewrite Hpos. reflexivity.
      * (* not in the heap *)
        replace (0 <=? enc_pos None) with false by reflexivity.
        apply exec_skip. normal.
        pose proof (r_dlit _ _ _ _ _ _ _ HRep) as Fdlit.
        pose proof (a_dlit _ _ _ _ _ _ _ HRep) as Adlit.
        (* if (s->dlit[a] < 0) return; *)
        run. eapply (exec_if_cmp _ _ _ Clt).
        -- ev.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- destruct (tget (dlit (hr x)) a) as [l|] eqn:Hdl.
           ++ pose proof (ho_dlit _ _ Hok a l Ha Hdl) as Hl.
              pose proof (key_small l N Hl HN) as Hkey. unfold enc_lit, Small. lia.
           ++ unfold enc_lit, Small. lia.
        -- unfold Small. lia.
        -- cbn [zcmp]. destruct (tget (dlit (hr x)) a) as [l|] eqn:Hdl.
           ++ (* a literal to decide on *)
              replace (enc_lit (Some l) <? 0) with false
                by (symmetry; apply Z.ltb_ge; unfold enc_lit, key; lia).
              apply exec_skip. normal.
              pose proof (r_hsize _ _ _ _ _ _ _ HRep) as Fhsize.
              pose proof (r_nv _ _ _ _ _ _ _ HRep) as Fnv.
              (* int n = s->hsize; if (n >= s->nv) return; *)
              run. eapply (exec_if_cmp _ _ _ Cge).
              ** ev.
              ** ev.
              ** reflexivity.
              ** reflexivity.
              ** unfold Small. lia.
              ** unfold Small. lia.
              ** cbn [zcmp]. destruct (Nat.leb_spec N (hsize (hr x))) as [Hfull | Hroom].
                 --- (* the heap is full: return *)
                     replace (Z.of_nat N <=? Z.of_nat (hsize (hr x))) with true
                       by (symmetry; apply Z.leb_le; lia).
                     apply exec_return_none. ret.
                     apply (insert_return_same S N lss x lims a).
                     +++ assumption.
                     +++ unfold heap_insert. rewrite Hpos, Hdl.
                         replace (N <=? hsize (hr x))%nat with true
                           by (symmetry; apply Nat.leb_le; assumption).
                         reflexivity.
                 --- (* room: put a at the end *)
                     replace (Z.of_nat N <=? Z.of_nat (hsize (hr x))) with false
                       by (symmetry; apply Z.leb_gt; lia).
                     apply exec_skip. normal.
                     apply (insert_put_correct (lt := lt) S N lss x lims a l).
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
           ++ (* no literal to decide on: return *)
              replace (enc_lit None <? 0) with true by reflexivity.
              apply exec_return_none. ret.
              apply (insert_return_same S N lss x lims a).
              ** assumption.
              ** unfold heap_insert. rewrite Hpos, Hdl. reflexivity.
Qed.

Lemma heap_insert_fun: exists (b: block),
  Genv.find_symbol ge _heap_insert = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_heap_insert).
Proof. apply find_fun. reflexivity. Qed.
