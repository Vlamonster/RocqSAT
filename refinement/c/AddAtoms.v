(* add_atoms adds the literals to decide on: the first literal of each atom in the list
   of all literals, with an activity by its position, and puts the atom in the heap
   (add_atoms). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Heur Propagate Analysis Step.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep RepHeur HeapInsert.
Import ListNotations.

(* Adding from k < nl on is looking at the literal at k and adding from k + 1 on. *)
Lemma add_atoms_next: forall (h: Heur) (alls: Table Lit) (n nl k: nat), (k < nl)%nat ->
  add_atoms h alls n nl k (nl - k) =
  let l := tget alls k in
  let b := extract l in
  match tget (dlit h) b with
  | None   =>
    add_atoms (heap_insert (set_act (set_dlit h b (Some l)) b (Z.of_nat (nl - k))) n b)
      alls n nl (Datatypes.S k) (nl - Datatypes.S k)
  | Some _ => add_atoms h alls n nl (Datatypes.S k) (nl - Datatypes.S k)
  end.
Proof.
  intros h alls n nl k Hk.
  assert (Hk2: (nl - k = Datatypes.S (nl - Datatypes.S k))%nat) by lia.
  rewrite Hk2 at 1. reflexivity.
Qed.

(* The invariant of the loop of add_atoms at k, for the memory m of the call and the
   result res of the model: the temporaries hold s, the number of literals and k, k is
   at most that number, the memory represents x with a heuristic h that adding from k
   on turns into res, and only the heuristic is written. *)
Record AddInv {lt: list Lit} (m: mem) (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (res: Heur) (k: nat) (le: temp_env) (m1: mem): Prop := {
  ai_s: le ! _s = Some (sptr S);
  ai_n: le ! _n = Some (vint (Z.of_nat (nlits x)));
  ai_k: le ! _k = Some (vint (Z.of_nat k));
  ai_le: (k <= nlits x)%nat;
  ai_heur: exists (h: Heur), add_atoms h (alls x) N (nlits x) k (nlits x - k) = res /\
    RepL m1 S N lss (with_heur x h) lims lt;
  ai_frame: Mem.unchanged_on (HeurFrame S) m m1;
}.

(* The state of the loop of add_atoms after looking at the literal at k, before k++:
   as the invariant at k + 1, but for the temporary k. *)
Record AddMid {lt: list Lit} (m: mem) (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (res: Heur) (k: nat) (le: temp_env) (m1: mem): Prop := {
  am_s: le ! _s = Some (sptr S);
  am_n: le ! _n = Some (vint (Z.of_nat (nlits x)));
  am_k: le ! _k = Some (vint (Z.of_nat k));
  am_heur: exists (h: Heur),
    add_atoms h (alls x) N (nlits x) (Datatypes.S k) (nlits x - Datatypes.S k) = res /\
    RepL m1 S N lss (with_heur x h) lims lt;
  am_frame: Mem.unchanged_on (HeurFrame S) m m1;
}.

(* The statements of add_atoms for the first literal l of an atom b, in its loop. *)
Definition add_new: statement := then_stmt (drop_stmts 2 (first_stmt
  (drop_stmts 3 (loop_body (drop_stmts 2 (fn_body f_add_atoms)))))).

(* Adding the literal l at k of alls, the first of its atom b = extract l, to the
   heuristic h. Writing nl for nlits x and h' for
   set_act (set_dlit h b (Some l)) b (nl - k):

     {{ RepL m1 S N lss (with_heur x h) lims lt /\ b < N }}
       s->dlit[b] = l;                                                 (rep_store_dlit)
     {{ RepL m2 S N lss (with_heur x (set_dlit h b (Some l))) lims lt }}
       s->act[b] = n - k;                                               (rep_store_act)
     {{ RepL m3 S N lss (with_heur x h') lims lt }}
       heap_insert(s, b);                                         (heap_insert_correct)
     {{ RepL m4 S N lss (with_heur x (heap_insert h' N b)) lims lt }}

   and adding from k + 1 on to heap_insert h' N b gives res: AddMid res k. *)
Lemma add_new_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (res h: Heur) (k: nat) (l: Lit) (le: temp_env) (m m1: mem),
  RepL m1 S N lss (with_heur x h) lims lt -> (extract l < N)%nat -> (k < nlits x)%nat ->
  add_atoms (heap_insert (set_act (set_dlit h (extract l) (Some l)) (extract l)
      (Z.of_nat (nlits x - k))) N (extract l))
    (alls x) N (nlits x) (Datatypes.S k) (nlits x - Datatypes.S k) = res ->
  Mem.unchanged_on (HeurFrame S) m m1 ->
  le ! _s = Some (sptr S) -> le ! _n = Some (vint (Z.of_nat (nlits x))) ->
  le ! _k = Some (vint (Z.of_nat k)) -> le ! _l = Some (vint (key l)) ->
  le ! _b = Some (vint (Z.of_nat (extract l))) ->
  Exec ge le m1 add_new (fun (le': temp_env) (m': mem) (out: outcome) =>
    out = Out_normal /\ @AddMid lt m S N lss x lims res k le' m').
Proof.
  intros S N lss x lims res h k l le m m1 HRep1 Hb Hk Hres Hframe Hs Hn Hk' Hl Hb'.
  pose proof (r_n _ _ _ _ _ _ _ HRep1) as HN.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep1) as Hnd.
  pose proof (r_nlits_le _ _ _ _ _ _ _ HRep1) as Hnl. cbn [with_heur nlits] in Hnl.
  pose proof (r_dlit _ _ _ _ _ _ _ HRep1) as Fdlit.
  pose proof (a_dlit _ _ _ _ _ _ _ HRep1) as Adlit.
  assert (Hlim: act_lim = 1073741824) by reflexivity.
  assert (Hsub: Int.sub (Int.repr (Z.of_nat (nlits x))) (Int.repr (Z.of_nat k))
                = Int.repr (Z.of_nat (nlits x - k))).
  { rewrite sub_repr. f_equal. lia. }
  unfold add_new, f_add_atoms.
  cbn [fn_body drop_stmts first_stmt then_stmt loop_body Swhile].
  (* s->dlit[b] = l; *)
  run. eapply exec_store.
  - evl.
  - ev.
  - reflexivity.
  - reflexivity.
  - ofs. bound.
  - ofs. cbn [cast_int_int].
    destruct (arr_storable m1 (b_dlit S) N (extract l) _ (key l) Adlit Hb) as [m2 Hst2].
    exists m2. split.
    + apply Hst2.
    + normal.
      assert (HRep2: RepL m2 S N lss (with_heur x (set_dlit h (extract l) (Some l)))
                       lims lt).
      { apply (rep_store_dlit m1 m2 S N lss (with_heur x h) lims (extract l) (Some l)
                 HRep1 Hb).
        - intros l0 Hl0. injection Hl0 as <-. assumption.
        - apply Hst2. }
      keep_mem m2.
      pose proof (r_act _ _ _ _ _ _ _ HRep2) as Fact.
      pose proof (a_act _ _ _ _ _ _ _ HRep2) as Aact.
      (* s->act[b] = n - k; *)
      run. eapply exec_store.
      * evl.
      * ev.
      * reflexivity.
      * reflexivity.
      * ofs. bound.
      * ofs. cbn [cast_int_int].
        destruct (arr_storable m2 (b_act S) N (extract l) _ (Z.of_nat (nlits x - k)) Aact
                    Hb) as [m3 Hst3].
        exists m3. split.
        -- apply Hst3.
        -- normal.
           set (h' := set_act (set_dlit h (extract l) (Some l)) (extract l)
                        (Z.of_nat (nlits x - k))).
           assert (HRep3: RepL m3 S N lss (with_heur x h') lims lt).
           { apply (rep_store_act m2 m3 S N lss
                      (with_heur x (set_dlit h (extract l) (Some l))) lims (extract l) _
                      HRep2 Hb).
             - lia.
             - apply Hst3. }
           keep_mem m3.
           (* heap_insert(s, b); *)
           call heap_insert_fun. eapply call_weaken.
           { apply (heap_insert_correct (lt := lt) S N lss (with_heur x h') lims
                      (extract l)).
             split.
             - assumption.
             - assumption. }
           intros m4 v4 [HRep4 Hun4]. split.
           ++ reflexivity.
           ++ constructor.
              ** tmp.
              ** tmp.
              ** tmp.
              ** exists (heap_insert h' N (extract l)). split.
                 --- apply Hres.
                 --- apply HRep4.
              ** apply (Mem.unchanged_on_trans _ m m3 m4).
                 --- apply (store_unchanged _ m m2 m3 Mint32 (b_act S)
                              (4 * Z.of_nat (extract l))
                              (vint (Z.of_nat (nlits x - k)))).
                     +++ apply (store_unchanged _ m m1 m2 Mint32 (b_dlit S)
                                  (4 * Z.of_nat (extract l)) (vint (key l))).
                         *** assumption.
                         *** assumption.
                         *** intros i (_ & _ & _ & Hne & _). now apply Hne.
                     +++ assumption.
                     +++ intros i [Hne _]. now apply Hne.
                 --- assumption.
Qed.

(* add_atoms looks at the literals of alls in order; the first one of each atom becomes
   its literal to decide on. Writing nl for nlits x, res for
   add_atoms (hr x) (alls x) N nl 0 nl, and h for the heuristic of the invariant:

     {{ RepL m S N lss x lims lt }}
       int n = s->nlits;
       int k = 0;
     {{ AddInv res 0 }}
       while (k < n) {
     {{ AddInv res k /\ k < n }}
         int l = s->alls[k];
         int b = l >> 1;
         if (s->dlit[b] < 0) {
     {{ AddInv res k /\ dlit h b = None }}
           s->dlit[b] = l;                                             (rep_store_dlit)
           s->act[b] = n - k;                                           (rep_store_act)
           heap_insert(s, b);                                     (heap_insert_correct)
         }
         k++;
     {{ AddInv res (k + 1) }}                                         (add_atoms_next)
       }
     {{ AddInv res nl: the heuristic is res }}

   The loop ends: nl - k decreases. *)
Lemma add_atoms_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat),
  {{ m | RepL m S N lss x lims lt }}
    f_add_atoms(sptr S)
  {{ m', v | RepL m' S N lss
               (with_heur x (add_atoms (hr x) (alls x) N (nlits x) 0 (nlits x)))
               lims lt /\
             Mem.unchanged_on (HeurFrame S) m m' }}.
Proof.
  intros S N lss x lims m HRep.
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_nlits_le _ _ _ _ _ _ _ HRep) as Hnl.
  pose proof (r_nlits _ _ _ _ _ _ _ HRep) as Fnlits.
  pose proof (r_alls_atoms _ _ _ _ _ _ _ HRep) as Hatoms.
  set (res := add_atoms (hr x) (alls x) N (nlits x) 0 (nlits x)).
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_add_atoms. cbn [fn_body fn_return].
    (* int n = s->nlits; int k = 0; *)
    run. clear Fnlits. unfold Swhile.
    apply exec_loop with (R := ltof nat (fun (k: nat) => nlits x - k)%nat)
      (I := @AddInv lt m S N lss x lims res) (a := 0%nat).
    + apply well_founded_ltof.
    + intros k le1 m1 HI. destruct HI as [Hs Hn Hk Hkn (h & Hres & HRep1) Hframe].
      pose proof (r_nodup _ _ _ _ _ _ _ HRep1) as Hnd.
      apply exec_seq.
      (* if (k < n) ... else break; *)
      eapply (exec_if_cmp _ _ _ Clt).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * destruct (Nat.lt_ge_cases k (nlits x)) as [Hlt | Hge].
        -- (* k < n: look at the literal at k *)
           replace (zcmp Clt (Z.of_nat k) (Z.of_nat (nlits x))) with true
             by (symmetry; cbn [zcmp]; apply Z.ltb_lt; lia).
           rewrite (add_atoms_next h (alls x) N (nlits x) k Hlt) in Hres.
           cbv zeta in Hres.
           set (l := tget (alls x) k) in *.
           assert (Hb: (extract l < N)%nat).
           { apply Hatoms. lia. }
           pose proof (key_small l N Hb HN) as Hkey.
           assert (Hshr: Int.shr (Int.repr (key l)) (Int.repr 1)
                         = Int.repr (Z.of_nat (extract l))).
           { apply shr_key. lia. }
           pose proof (r_alls _ _ _ _ _ _ _ HRep1) as Falls.
           pose proof (a_alls _ _ _ _ _ _ _ HRep1) as (ta & Aalls & Hta).
           pose proof (r_dlit _ _ _ _ _ _ _ HRep1) as Fdlit.
           pose proof (a_dlit _ _ _ _ _ _ _ HRep1) as Adlit.
           cbn [with_heur hr nlits alls] in Hta, Adlit.
           (* int l = s->alls[k]; int b = l >> 1; *)
           cbv beta iota. run. rewrite (Hta k) by lia. fold l. run.
           pose proof (ho_dlit _ _ (r_heur _ _ _ _ _ _ _ HRep1) (extract l) ) as Hdl.
           cbn [with_heur hr] in Hdl.
           assert (Hadd: Int.add (Int.repr (Z.of_nat k)) (Int.repr 1)
                         = Int.repr (Z.of_nat (Datatypes.S k))).
           { rewrite add_repr. f_equal. lia. }
           (* if (s->dlit[b] < 0) { ... }, joined in AddMid *)
           apply exec_weaken with (Q := fun (le': temp_env) (m': mem) (out: outcome) =>
             out = Out_normal /\ @AddMid lt m S N lss x lims res k le' m').
           ++ destruct (tget (dlit h) (extract l)) as [l'|] eqn:Hd.
              ** (* the atom has a literal: nothing to do *)
                 assert (Hl': (extract l' < N)%nat).
                 { apply (Hdl l' Hb). reflexivity. }
                 pose proof (key_small l' N Hl' HN) as Hkey'.
                 cbn [enc_lit]. eapply (exec_if_cmp _ _ _ Clt).
                 --- ev.
                 --- ev.
                 --- reflexivity.
                 --- reflexivity.
                 --- unfold Small. lia.
                 --- unfold Small. lia.
                 --- replace (zcmp Clt (key l') 0) with false
                       by (symmetry; cbn [zcmp]; apply Z.ltb_ge; lia).
                     cbv beta iota. apply exec_skip. split.
                     +++ reflexivity.
                     +++ constructor.
                         *** tmp.
                         *** tmp.
                         *** tmp.
                         *** exists h. split.
                             ---- apply Hres.
                             ---- apply HRep1.
                         *** assumption.
              ** (* the first literal of the atom: add it (add_new_correct) *)
                 cbn [enc_lit]. eapply (exec_if_cmp _ _ _ Clt).
                 --- ev.
                 --- ev.
                 --- reflexivity.
                 --- reflexivity.
                 --- unfold Small. lia.
                 --- unfold Small. lia.
                 --- replace (zcmp Clt (-1) 0) with true by reflexivity.
                     cbv beta iota. rewrite Hshr.
                     apply (add_new_correct (lt := lt) S N lss x lims res h k l _ m m1).
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
           ++ (* k++; and the loop goes on *)
              intros le' m' out [-> HM]. destruct HM as [Hs' Hn' Hk' Hheur' Hframe'].
              apply seqk_normal. run. ints. apply loopk_next with (Datatypes.S k).
              ** unfold ltof. lia.
              ** constructor.
                 --- tmp.
                 --- tmp.
                 --- tmp.
                 --- lia.
                 --- assumption.
                 --- assumption.
        -- (* k >= n: break; the heuristic is res *)
           replace (zcmp Clt (Z.of_nat k) (Z.of_nat (nlits x))) with false
             by (symmetry; cbn [zcmp]; apply Z.ltb_ge; lia).
           cbv beta iota. apply exec_break. abrupt. apply loopk_break. exists Vundef.
           split.
           ++ reflexivity.
           ++ replace (nlits x - k)%nat with 0%nat in Hres by lia.
              cbn [add_atoms] in Hres. rewrite <- Hres. split.
              ** apply HRep1.
              ** assumption.
    + (* The invariant holds at 0. *)
      constructor.
      * tmp.
      * tmp.
      * tmp.
      * lia.
      * exists (hr x). split.
        -- rewrite Nat.sub_0_r. reflexivity.
        -- destruct x. apply HRep.
      * apply Mem.unchanged_on_refl.
Qed.

Lemma add_atoms_fun: exists (b: block),
  Genv.find_symbol ge _add_atoms = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_add_atoms).
Proof. apply find_fun. reflexivity. Qed.
