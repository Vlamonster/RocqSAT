(* reinsert puts the atoms of a range of the trail back in the heap (reinsert). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Heur Propagate Analysis Step.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep RepHeur HeapInsert.
Import ListNotations.

(* Reinserting from q > j on is inserting the atom at q - 1 and reinserting from q - 1
   on. *)
Lemma reinsert_last: forall (h: Heur) (tr: Table Lit) (n j q: nat), (j < q)%nat ->
  reinsert (heap_insert h n (extract (tget tr (q - 1)))) tr n j (q - 1) (q - 1 - j)
  = reinsert h tr n j q (q - j).
Proof.
  intros h tr n j q Hjq. replace (q - j)%nat with (Datatypes.S (q - 1 - j)) by lia.
  reflexivity.
Qed.

(* The invariant of the loop of reinsert at q, for the memory m of the call and the
   result res of the model: the temporaries hold s, j and q, q is between j and the end
   of the trail, the memory represents x with a heuristic h that reinserting from q on
   turns into res, and only the heuristic is written. *)
Record ReinsertInv {lt: list Lit} (m: mem) (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (j: nat) (res: Heur) (q: nat) (le: temp_env) (m1: mem):
  Prop := {
  ri_s: le ! _s = Some (sptr S);
  ri_j: le ! _j = Some (vint (Z.of_nat j));
  ri_q: le ! _q = Some (vint (Z.of_nat q));
  ri_range: (j <= q <= tlen x)%nat;
  ri_heur: exists (h: Heur), reinsert h (tr x) N j q (q - j) = res /\
    RepL m1 S N lss (with_heur x h) lims lt;
  ri_frame: Mem.unchanged_on (HeurFrame S) m m1;
}.

(* reinsert inserts the atoms of the trail from position q - 1 down to j into the heap.
   Writing res for reinsert (hr x) (tr x) N j q0 (q0 - j), for the q0 of the call:

     {{ RepL m S N lss x lims lt /\ j <= q0 <= tlen x }}
       (q = q0)
     {{ ReinsertInv res q0 }}
       while (q > j) {
     {{ ReinsertInv res q /\ q > j }}
         heap_insert(s, s->tr[q - 1] >> 1);                         (heap_insert_correct)
         q--;
     {{ ReinsertInv res (q - 1) }}                                     (reinsert_last)
       }
     {{ ReinsertInv res j: the heuristic is res }}

   The loop ends: q decreases. *)
Lemma reinsert_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (j q: nat),
  {{ m | RepL m S N lss x lims lt /\ (j <= q <= tlen x)%nat }}
    f_reinsert(sptr S, vint (Z.of_nat j), vint (Z.of_nat q))
  {{ m', v | RepL m' S N lss (with_heur x (reinsert (hr x) (tr x) N j q (q - j)))
               lims lt /\
             Mem.unchanged_on (HeurFrame S) m m' }}.
Proof.
  intros S N lss x lims j q0 m [HRep Hq0].
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_tlen_le _ _ _ _ _ _ _ HRep) as Ht.
  set (res := reinsert (hr x) (tr x) N j q0 (q0 - j)).
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_reinsert. cbn [fn_body fn_return]. unfold Swhile.
    apply exec_loop with (R := Peano.lt)
      (I := @ReinsertInv lt m S N lss x lims j res) (a := q0).
    + apply lt_wf.
    + intros q le1 m1 HI. destruct HI as [Hs Hj Hq Hjq (h & Hres & HRep1) Hframe].
      pose proof (r_nodup _ _ _ _ _ _ _ HRep1) as Hnd.
      pose proof (r_tr_atoms _ _ _ _ _ _ _ HRep1) as Hatoms.
      pose proof (r_tr _ _ _ _ _ _ _ HRep1) as Ftr.
      pose proof (a_tr _ _ _ _ _ _ _ HRep1) as Atr.
      cbn [with_heur tr tlen] in Hatoms, Atr.
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
        -- (* q = j: break; the heuristic is res *)
           replace (zcmp Cgt (Z.of_nat j) (Z.of_nat j)) with false
             by (simpl; symmetry; apply Z.ltb_irrefl).
           apply exec_break. abrupt. apply loopk_break. exists Vundef. split.
           ++ reflexivity.
           ++ rewrite Nat.sub_diag in Hres. cbn [reinsert] in Hres. rewrite <- Hres.
              split.
              ** apply HRep1.
              ** assumption.
        -- (* q > j: insert the atom at q - 1 *)
           replace (zcmp Cgt (Z.of_nat q) (Z.of_nat j)) with true
             by (simpl; symmetry; apply Z.ltb_lt; lia).
           assert (Hsub: Int.sub (Int.repr (Z.of_nat q)) (Int.repr 1)
                         = Int.repr (Z.of_nat (q - 1))).
           { rewrite sub_repr. f_equal. lia. }
           assert (Hl: (extract (tget (tr x) (q - 1)) < N)%nat).
           { apply Hatoms. lia. }
           pose proof (key_small _ N Hl HN) as Hkey.
           assert (Hshr: Int.shr (Int.repr (key (tget (tr x) (q - 1)))) (Int.repr 1)
                         = Int.repr (Z.of_nat (extract (tget (tr x) (q - 1))))).
           { apply shr_key. lia. }
           (* heap_insert(s, s->tr[q - 1] >> 1); *)
           cbv beta iota. run. call heap_insert_fun. cbn [cast_int_int]. rewrite Hshr.
           eapply call_weaken.
           { apply (heap_insert_correct (lt := lt) S N lss (with_heur x h) lims _).
             split.
             - assumption.
             - assumption. }
           intros m2 v2 [HRep2 Hun2]. normal. keep_mem m2.
           (* q--; and the loop goes on *)
           run. ints. apply loopk_next with (q - 1)%nat.
           ++ lia.
           ++ constructor.
              ** tmp.
              ** tmp.
              ** tmp.
              ** lia.
              ** exists (heap_insert h N (extract (tget (tr x) (q - 1)))). split.
                 --- rewrite reinsert_last by lia. assumption.
                 --- apply HRep2.
              ** apply (Mem.unchanged_on_trans _ m m1 m2).
                 --- assumption.
                 --- assumption.
    + (* The invariant holds at q0. *)
      constructor.
      * tmp.
      * tmp.
      * tmp.
      * lia.
      * exists (hr x). split.
        -- reflexivity.
        -- destruct x. apply HRep.
      * apply Mem.unchanged_on_refl.
Qed.

Lemma reinsert_fun: exists (b: block),
  Genv.find_symbol ge _reinsert = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_reinsert).
Proof. apply find_fun. reflexivity. Qed.
