(* add_atoms adds the literals to decide on: the first literal of each atom in the list
   of all literals, with an activity by its position, and puts the atom in the heap
   (add_atoms). *)
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
From RocqSAT.refinement.c Require Import HeapInsert.

(* Adding from k < nl on is looking at the literal at k and adding from k + 1 on. *)
Lemma add_atoms_next: forall (h: Heur) (alls: Table Lit) (n nl k: nat), (k < nl)%nat ->
  add_atoms h alls n nl k (nl - k) =
  let l := tget alls k in
  let b := extract l in
  match tget (dlit h) b with
  | None   =>
    add_atoms (heap_insert (set_act (set_dlit h b (Some l)) b (Z.of_nat (nl - k))) n b)
      alls n nl (S k) (nl - S k)
  | Some _ => add_atoms h alls n nl (S k) (nl - S k)
  end.
Proof.
  intros h alls n nl k Hk.
  assert (Hk2: (nl - k = S (nl - S k))%nat) by lia.
  rewrite Hk2 at 1. reflexivity.
Qed.

(* The state of the loop of add_atoms at k, with the temporary k holding kt, for the
   memory m of the call and the result res of the model: the temporaries hold s and the
   number of literals, k is at most that number, the memory represents x with a heuristic
   h that adding from k on turns into res, and only the heuristic is written. The loop
   invariant is AtomsInv m sh N lss x res k k; after the literal at k, before k++, it is
   AtomsInv m sh N lss x res k (k + 1). *)
Record AtomsInv {m: mem} {sh: Shape} {N: nat} {lss: list (list Lit)}
  {x: Ctx} {res: Heur} {kt k: nat} {le: temp_env} {m1: mem}: Prop := {
  ai_s: le ! _s = Some (sptr sh);
  ai_n: le ! _n = Some (vnat (nlits x));
  ai_k: le ! _k = Some (vnat kt);
  ai_le: (k <= nlits x)%nat;
  ai_heur: exists (h: Heur), add_atoms h (alls x) N (nlits x) k (nlits x - k) = res /\
    RepL m1 sh N lss (x <| hr := h |>);
  ai_frame: Mem.unchanged_on (HeurFrame sh) m m1;
}.
Arguments AtomsInv : clear implicits.

(* The statements of add_atoms for the first literal l of an atom b, in its loop. *)
Definition add_new: statement := then_stmt (drop_stmts 2 (first_stmt
  (drop_stmts 3 (loop_body (drop_stmts 2 (fn_body f_add_atoms)))))).

(* Adding the literal l at k of alls, the first of its atom b = extract l, to the
   heuristic h. Writing nl for nlits x and h' for
   set_act (set_dlit h b (Some l)) b (nl - k):

     {{ RepL m1 sh N lss (x <| hr := h |>) /\ b < N }}
       s->dlit[b] = l;                                                 (rep_store_dlit)
     {{ RepL m2 sh N lss (x <| hr := set_dlit h b (Some l) |>) }}
       s->act[b] = n - k;                                               (rep_store_act)
     {{ RepL m3 sh N lss (x <| hr := h' |>) }}
       heap_insert(s, b);                                         (heap_insert_correct)
     {{ RepL m4 sh N lss (x <| hr := heap_insert h' N b |>) }}

   and adding from k + 1 on to heap_insert h' N b gives res: AtomsInv res k (k + 1). *)
Lemma add_new_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (res h: Heur) (k: nat) (l: Lit) (le: temp_env) (m m1: mem),
  RepL m1 sh N lss (x <| hr := h |>) -> (extract l < N)%nat -> (k < nlits x)%nat ->
  add_atoms (heap_insert (set_act (set_dlit h (extract l) (Some l)) (extract l)
      (Z.of_nat (nlits x - k))) N (extract l))
    (alls x) N (nlits x) (S k) (nlits x - S k) = res ->
  Mem.unchanged_on (HeurFrame sh) m m1 ->
  le ! _s = Some (sptr sh) -> le ! _n = Some (vnat (nlits x)) ->
  le ! _k = Some (vnat k) -> le ! _l = Some (vint (key l)) ->
  le ! _b = Some (vnat (extract l)) ->
  Exec ge le m1 add_new (fun (le': temp_env) (m': mem) (out: outcome) =>
    out = Out_normal /\ AtomsInv m sh N lss x res k (S k) le' m').
Proof.
  intros sh N lss x res h k l le m m1 HRep1 Hb Hk Hres Hframe Hs Hn Hk' Hl Hb'.
  pose proof (r_n HRep1) as HN.
  pose proof (r_nodup HRep1) as Hnd.
  pose proof (r_nlits_le HRep1) as Hnl. cbn [set_hr nlits] in Hnl.
  pose proof (r_dlit HRep1) as Fdlit.
  pose proof (a_dlit HRep1) as Adlit.
  assert (Hlim: act_lim = small_bound) by reflexivity.
  assert (Hsub: Int.sub (Int.repr (Z.of_nat (nlits x))) (Int.repr (Z.of_nat k))
                = Int.repr (Z.of_nat (nlits x - k))).
  { rewrite sub_repr. f_equal. lia. }
  unfold add_new, f_add_atoms.
  cbn [fn_body drop_stmts first_stmt then_stmt loop_body Swhile].
  (* s->dlit[b] = l; *)
  run. store Adlit Hb as m2 Hst2.
  assert (HRep2: RepL m2 sh N lss (x <| hr := set_dlit h (extract l) (Some l) |>)).
  { apply (rep_store_dlit m1 m2 (extract l) (Some l)
             HRep1 Hb).
    - intros l0 Hl0. injection Hl0 as <-. assumption.
    - apply Hst2. }
  keep_mem m2.
  pose proof (r_act HRep2) as Fact.
  pose proof (a_act HRep2) as Aact.
  (* s->act[b] = n - k; *)
  run. store Aact Hb as m3 Hst3.
  cbn [cast_int_int] in Hst3. rewrite Hsub in Hst3. normal.
  set (h' := set_act (set_dlit h (extract l) (Some l)) (extract l)
               (Z.of_nat (nlits x - k))).
  assert (HRep3: RepL m3 sh N lss (x <| hr := h' |>)).
  { apply (rep_store_act m2 m3 (extract l) _
             HRep2 Hb).
    - lia.
    - apply Hst3. }
  keep_mem m3.
  (* heap_insert(s, b); *)
  call heap_insert_fun (heap_insert_correct sh N lss (x <| hr := h' |>) (extract l)).
  - split.
    + apply HRep3.
    + apply Hb.
  - intros m4 v4 [HRep4 Hun4]. split.
    + reflexivity.
    + constructor.
      * tmp.
      * tmp.
      * tmp.
      * lia.
      * exists (heap_insert h' N (extract l)). split.
        -- apply Hres.
        -- apply HRep4.
      * frame.
Qed.

(* add_atoms looks at the literals of alls in order; the first one of each atom becomes
   its literal to decide on. Writing nl for nlits x, res for
   add_atoms (hr x) (alls x) N nl 0 nl, and h for the heuristic of the invariant:

     {{ RepL m sh N lss x }}
       int n = s->nlits;
       int k = 0;
     {{ AtomsInv res 0 0 }}
       while (k < n) {
     {{ AtomsInv res k k /\ k < n }}
         int l = s->alls[k];
         int b = l >> 1;
         if (s->dlit[b] < 0) {
     {{ AtomsInv res k k /\ dlit h b = None }}
           s->dlit[b] = l;                                             (rep_store_dlit)
           s->act[b] = n - k;                                           (rep_store_act)
           heap_insert(s, b);                                     (heap_insert_correct)
         }
     {{ AtomsInv res k (k + 1) }}                                       (add_atoms_next)
         k++;
     {{ AtomsInv res (k + 1) (k + 1) }}
       }
     {{ AtomsInv res nl nl: the heuristic is res }}

   The loop ends: nl - k decreases. *)
Lemma add_atoms_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx),
  {{ m | RepL m sh N lss x }}
    f_add_atoms(sptr sh)
  {{ m', v | RepL m' sh N lss
               (x <| hr := add_atoms (hr x) (alls x) N (nlits x) 0 (nlits x) |>) /\
             Mem.unchanged_on (HeurFrame sh) m m' }}.
Proof.
  intros sh N lss x m HRep.
  pose proof (r_n HRep) as HN.
  pose proof (r_nlits_le HRep) as Hnl.
  pose proof (r_nlits HRep) as Fnlits.
  pose proof (r_alls_atoms HRep) as Hatoms.
  set (res := add_atoms (hr x) (alls x) N (nlits x) 0 (nlits x)).
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_add_atoms. cbn [fn_body fn_return].
    (* int n = s->nlits; int k = 0; *)
    run. clear Fnlits. unfold Swhile.
    apply exec_loop with (R := ltof nat (fun (k: nat) => nlits x - k)%nat)
      (I := fun (k: nat) => AtomsInv m sh N lss x res k k) (a := 0%nat).
    + apply well_founded_ltof.
    + intros k le1 m1 HI. destruct HI as [Hs Hn Hk Hkn (h & Hres & HRep1) Hframe].
      pose proof (r_nodup HRep1) as Hnd.
      apply exec_seq.
      (* if (k < n) ... else break; *)
      branch.
      * (* k < n: look at the literal at k *)
        intros Hlt_z. assert (Hlt: (k < nlits x)%nat) by lia.
        rewrite (add_atoms_next h (alls x) N (nlits x) k Hlt) in Hres.
        cbv zeta in Hres.
        set (l := tget (alls x) k) in *.
        assert (Hb: (extract l < N)%nat).
        { apply Hatoms. lia. }
        pose proof (key_small l N Hb HN) as Hkey.
        assert (Hshr: Int.shr (Int.repr (key l)) (Int.repr 1)
                      = Int.repr (Z.of_nat (extract l))).
        { apply shr_key. lia. }
        pose proof (r_alls HRep1) as Falls.
        pose proof (a_alls HRep1) as (ta & Aalls & Hta).
        pose proof (r_dlit HRep1) as Fdlit.
        pose proof (a_dlit HRep1) as Adlit.
        cbn [set_hr hr nlits alls] in Hta, Adlit.
        (* int l = s->alls[k]; int b = l >> 1; *)
        run. rewrite (Hta k) by lia. fold l. run.
        pose proof (ho_dlit (r_heur HRep1) (extract l) ) as Hdl.
        cbn [set_hr hr] in Hdl.
        assert (Hadd: Int.add (Int.repr (Z.of_nat k)) (Int.repr 1)
                      = Int.repr (Z.of_nat (S k))).
        { rewrite add_repr. f_equal. lia. }
        (* if (s->dlit[b] < 0) { ... }, joined in AtomsInv res k (k + 1) *)
        apply exec_weaken with (Q := fun (le': temp_env) (m': mem) (out: outcome) =>
          out = Out_normal /\ AtomsInv m sh N lss x res k (S k) le' m').
        -- destruct (tget (dlit h) (extract l)) as [l'|] eqn:Hd.
           ++ (* the atom has a literal: nothing to do *)
              assert (Hl': (extract l' < N)%nat).
              { apply (Hdl l' Hb). reflexivity. }
              pose proof (key_small l' N Hl' HN) as Hkey'.
              cbn [enc_lit]. branch.
              ** (* key l' < 0 is impossible *)
                 intros Hneg. lia.
              ** intros _. apply exec_skip. split.
                 --- reflexivity.
                 --- constructor.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
                     +++ lia.
                     +++ exists h. split.
                         *** apply Hres.
                         *** apply HRep1.
                     +++ assumption.
           ++ (* the first literal of the atom: add it (add_new_correct) *)
              cbn [enc_lit]. branch.
              ** intros _. rewrite Hshr.
                 apply (add_new_correct sh N lss x res h k l _ m m1).
                 --- assumption.
                 --- assumption.
                 --- assumption.
                 --- assumption.
                 --- assumption.
                 --- tmp.
                 --- tmp.
                 --- tmp.
                 --- tmp.
                 --- tmp.
              ** (* 0 <= -1 is impossible *)
                 intros Hnonneg. lia.
        -- (* k++; and the loop goes on *)
           intros le' m' out [-> HM]. destruct HM as [Hs' Hn' Hk' _ Hheur' Hframe'].
           apply seqk_normal. run. ints. apply loopk_next with (S k).
           ++ unfold ltof. lia.
           ++ constructor.
              ** tmp.
              ** tmp.
              ** tmp.
              ** lia.
              ** assumption.
              ** assumption.
      * (* k >= n: break; the heuristic is res *)
        intros Hge.
        apply exec_break. abrupt. apply loopk_break. exists Vundef.
        split.
        -- reflexivity.
        -- replace (nlits x - k)%nat with 0%nat in Hres by lia.
           cbn [add_atoms] in Hres. rewrite <- Hres. split.
           ++ apply HRep1.
           ++ assumption.
    + (* The invariant holds at 0. *)
      constructor.
      * tmp.
      * tmp.
      * tmp.
      * lia.
      * exists (hr x). split.
        -- rewrite Nat.sub_0_r. reflexivity.
        -- destruct x. apply HRep.
      * frame.
Qed.

Lemma add_atoms_fun: FunAt _add_atoms f_add_atoms.
Proof. apply find_fun. reflexivity. Qed.
