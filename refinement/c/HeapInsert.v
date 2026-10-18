(* heap_insert puts an atom in the heap, unless it is there, is not decided on, or the
   heap is full (heap_insert). *)
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
From RocqSAT.refinement.c Require Import HeapUp.

(* Returning from heap_insert with the heuristic unchanged, when the model leaves it. *)
Lemma insert_return_same: forall (sh: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (a: nat) (le: temp_env) (m: mem),
  RepL m sh N lss x -> heap_insert (hr x) N a = hr x ->
  Returns f_heap_insert (fun (m': mem) (_: val) =>
    HeurPost sh N lss x m (heap_insert (hr x) N a) m') le m (Out_return None).
Proof.
  intros sh N lss x a le m HRep Hsame. return_none.
  split.
  - rewrite Hsame, set_hr_same. assumption.
  - frame.
Qed.

(* The heuristic h with atom a put at its end, in a heap one larger. *)
Definition put_last (h: Heur) (a: nat): Heur :=
  mkHeur (act h) (inc h) (tset (heap h) (hsize h) a) (tset (hpos h) a (Some (hsize h)))
    (S (hsize h)) (dlit h).

(* The statements of heap_insert that put a at the end and move it up. *)
Definition insert_put: statement := drop_stmts 4 (fn_body f_heap_insert).

(* Putting atom a, not in the heap and with a literal l to decide on, at the end
   n = hsize (hr x) < N of the heap, and moving it up:

     {{ RepL x /\ hpos a = None /\ dlit a = Some l /\ n < N }}
       s->heap[n] = a;
       s->hpos[a] = n;                      (heap_stmt_correct, hpos_stmt_correct)
       s->hsize = n + 1;                                              (rep_store_hsize)
     {{ RepL (x <| hr := put_last (hr x) a |>) }}
       heap_up(s, n);                                                 (heap_up_correct)
     {{ RepL (x <| hr := heap_up (put_last (hr x) a) n |>) /\ only the heuristic
        changed, and heap_up (put_last (hr x) a) n = heap_insert (hr x) N a }}      *)
Lemma insert_put_correct: forall (sh: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (a: nat) (l: Lit) (le: temp_env)
  (m: mem),
  RepL m sh N lss x -> (a < N)%nat -> tget (hpos (hr x)) a = None ->
  tget (dlit (hr x)) a = Some l -> (hsize (hr x) < N)%nat ->
  le ! _s = Some (sptr sh) -> le ! _a = Some (vnat a) ->
  le ! _n = Some (vnat (hsize (hr x))) ->
  Exec ge le m insert_put (Returns f_heap_insert (fun (m': mem) (_: val) =>
    HeurPost sh N lss x m (heap_insert (hr x) N a) m')).
Proof.
  intros sh N lss x a l le m HRep Ha Hpos Hdl Hroom Hs Ha' Hn.
  pose proof (r_n HRep) as HN.
  (* the model puts a at the end and moves it up *)
  assert (Hput: heap_insert (hr x) N a = heap_up (put_last (hr x) a) (hsize (hr x))).
  { unfold heap_insert. rewrite Hpos, Hdl.
    replace (N <=? hsize (hr x))%nat with false
      by (symmetry; apply Nat.leb_gt; assumption).
    reflexivity. }
  rewrite Hput. unfold insert_put, f_heap_insert. cbn [fn_body drop_stmts].
  fold (heap_stmt _t'2 _n _a) (hpos_stmt _t'1 _a _n). apply exec_seq.
  (* s->heap[n] = a; *)
  apply (heap_stmt_correct sh N lss x (hr x) _ _ _ (hsize (hr x)) a).
  - rewrite set_hr_same. assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - discriminate.
  - discriminate.
  - intros m2 HRep2 Hun2. normal. apply exec_seq.
    (* s->hpos[a] = n; *)
    apply (hpos_stmt_correct sh N lss x (set_heap (hr x) (hsize (hr x)) a)
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
      pose proof (r_hsize HRep3) as Fhsize.
      assert (Hsucc: Int.add (Int.repr (Z.of_nat (hsize (hr x)))) (Int.repr 1)
                     = Int.repr (Z.of_nat (S (hsize (hr x))))).
      { rewrite add_repr. f_equal. lia. }
      (* s->hsize = n + 1; *)
      apply exec_seq. store Fhsize as m4 Hst4.
      cbn [cast_int_int] in Hst4. rewrite Hsucc in Hst4.
      pose proof (rep_store_hsize m3 m4 (S (hsize (hr x)))
                    HRep3 Hroom Hst4) as HRep4.
      assert (Hun4: Mem.unchanged_on (HeurFrame sh) m m4).
      { apply (store_unchanged _ m m3 m4 Mint32 (b_s sh) o_hsize
                 (vnat (S (hsize (hr x))))).
        - frame.
        - assumption.
        - apply s_not_frame. }
      (* heap_up(s, n); *)
      call heap_up_fun
        (heap_up_correct sh N lss (x <| hr := put_last (hr x) a |>) (hsize (hr x))).
      * split.
        -- apply HRep4.
        -- assumption.
      * intros m5 v5 [HRep5 Hun5]. return_none.
        split.
        -- apply HRep5.
        -- frame.
Qed.

(* heap_insert puts atom a at the end hs = hsize (hr x) of the heap and moves it up, if
   it is not in the heap, has a literal to decide on and the heap has room. Only the
   heuristic changes:

     {{ RepL m sh N lss x /\ a < N }}
       if (s->hpos[a] >= 0) return;
     {{ hpos a = None }}
       if (s->dlit[a] < 0) return;
     {{ dlit a = Some l }}
       int n = s->hsize;
       if (n >= s->nv) return;
     {{ n = hs < N }}
       s->heap[n] = a; s->hpos[a] = n; s->hsize = n + 1;
       heap_up(s, n);                                             (insert_put_correct)
     {{ RepL (x <| hr := heap_up (put_last (hr x) a) hs |>) /\ only the heuristic
        changed }}

   and each return leaves the heuristic as the model does (insert_return_same). *)
Lemma heap_insert_correct: forall (sh: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (a: nat),
  {{ m | RepL m sh N lss x /\ (a < N)%nat }}
    f_heap_insert(sptr sh, vnat a)
  {{ m', v | HeurPost sh N lss x m (heap_insert (hr x) N a) m' }}.
Proof.
  intros sh N lss x a m [HRep Ha]. pose proof (r_n HRep) as HN.
  pose proof (r_heur HRep) as Hok.
  pose proof (ho_hsize Hok) as Hhsize.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_heap_insert. cbn [fn_body fn_return].
    pose proof (r_hpos HRep) as Fhpos.
    pose proof (a_hpos HRep) as Ahpos.
    (* if (s->hpos[a] >= 0) return; *)
    run. eapply exec_if_ge.
    + ev.
    + ev.
    + reflexivity.
    + destruct (tget (hpos (hr x)) a) as [i|] eqn:Hpos.
      * pose proof (ho_hpos Hok a i Ha Hpos) as Hi. unfold enc_pos. lia.
      * unfold enc_pos. lia.
    + intros Hin. destruct (tget (hpos (hr x)) a) as [i|] eqn:Hpos.
      * (* in the heap: return *)
        apply exec_return_none. ret.
        apply (insert_return_same sh N lss x a).
        -- assumption.
        -- unfold heap_insert. rewrite Hpos. reflexivity.
      * (* not in the heap: its position -1 is negative *)
        unfold enc_pos in Hin. lia.
    + intros Hout. destruct (tget (hpos (hr x)) a) as [i|] eqn:Hpos.
      * (* in the heap: its position is not negative *)
        unfold enc_pos in Hout. lia.
      * (* not in the heap *)
        apply exec_skip. normal.
        pose proof (r_dlit HRep) as Fdlit.
        pose proof (a_dlit HRep) as Adlit.
        (* if (s->dlit[a] < 0) return; *)
        run. eapply exec_if_lt.
        -- ev.
        -- ev.
        -- reflexivity.
        -- destruct (tget (dlit (hr x)) a) as [l|] eqn:Hdl.
           ++ pose proof (ho_dlit Hok a l Ha Hdl) as Hl.
              pose proof (key_small l N Hl HN) as Hkey. unfold enc_lit. lia.
           ++ unfold enc_lit. lia.
        -- intros Hnone. destruct (tget (dlit (hr x)) a) as [l|] eqn:Hdl.
           ++ (* a literal to decide on: keys are not negative *)
              unfold enc_lit, key in Hnone. lia.
           ++ (* no literal to decide on: return *)
              apply exec_return_none. ret.
              apply (insert_return_same sh N lss x a).
              ** assumption.
              ** unfold heap_insert. rewrite Hpos, Hdl. reflexivity.
        -- intros Hsome. destruct (tget (dlit (hr x)) a) as [l|] eqn:Hdl.
           ++ (* a literal to decide on *)
              apply exec_skip. normal.
              pose proof (r_hsize HRep) as Fhsize.
              pose proof (r_nv HRep) as Fnv.
              (* int n = s->hsize; if (n >= s->nv) return; *)
              run. branch.
              ** (* the heap is full: return *)
                 intros Hfull. apply exec_return_none. ret.
                 apply (insert_return_same sh N lss x a).
                 --- assumption.
                 --- unfold heap_insert. rewrite Hpos, Hdl.
                     replace (N <=? hsize (hr x))%nat with true
                       by (symmetry; apply Nat.leb_le; lia).
                     reflexivity.
              ** (* room: put a at the end *)
                 intros Hroom. apply exec_skip. normal.
                 apply (insert_put_correct sh N lss x a l).
                 --- assumption.
                 --- assumption.
                 --- assumption.
                 --- assumption.
                 --- lia.
                 --- tmp.
                 --- tmp.
                 --- tmp.
           ++ (* no literal to decide on: its encoding -1 is negative *)
              unfold enc_lit in Hsome. lia.
Qed.

Lemma heap_insert_fun: FunAt _heap_insert f_heap_insert.
Proof. apply find_fun. reflexivity. Qed.
