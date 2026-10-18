(* visit visits the watchers of a false literal (visit), or gives up.

   The loop of visit runs over the watch list ws of p. Each watcher (i, b) at position k
   is kept at once when its blocker b is true; otherwise its clause i is looked at: the
   watcher is kept with a new blocker, moved to the watch list of another literal, or
   dropped, and on a conflict keep_rest keeps the rest of ws as it is. VisitTemps and
   VisitMem (KeepRest.v) say what the temporaries and the memory hold at position k, and
   each part of the loop body has a lemma of its own. *)
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
From RocqSAT.refinement Require Import Tactics.
From RocqSAT.refinement Require Import Table.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement Require Import Analysis.
From RocqSAT.refinement.c Require Import Arrays.
From RocqSAT.refinement.c Require Import Logic.
From RocqSAT.refinement.c Require Import Common.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Rep.
From RocqSAT.refinement.c Require Import LitValue.
From RocqSAT.refinement.c Require Import Wpush.
From RocqSAT.refinement.c Require Import Assign.
From RocqSAT.refinement.c Require Import FindWatch.
From RocqSAT.refinement.c Require Import KeepRest.

(* Whether a visit found a conflict, as C returns it: i + 1 for a conflict on clause i,
   0 for none. *)
Definition enc_conf (r: option nat): Z :=
match r with
| Some i => Z.of_nat i + 1
| None   => 0
end.

(* What visit, propagate and check_shorts return for the result res of their model: -1
   when out of room, or the encoded conflict of res, with the memory representing its
   context; a conflict is on one of the clauses lss (Peano.lt i (length lss) is
   (i < length lss)%nat, without parsing lss in nat_scope). *)
Abbreviation ConfOut sh N lss res m' v :=
  (v = vint (-1) \/
   (v = vint (enc_conf (snd res)) /\ Rep m' sh N lss (fst res) /\
    forall (i: nat), snd res = Some i -> Peano.lt i (length lss))).

(* What the loops of propagate and check_shorts end in, for the result res of their
   model: they end without a conflict, or return what ConfOut allows. *)
Definition LoopOut (sh: Shape) (N: nat) (lss: list (list Lit)) (res: Ctx * option nat)
  (le: temp_env) (m: mem) (out: outcome): Prop :=
  (out = Out_normal /\ snd res = None /\ Rep m sh N lss (fst res)) \/
  exists (z: Z), out = ret_int z /\
    ConfOut sh N lss res m (vint z).

(* C computes the result i + 1 of a conflict on clause i. *)
Lemma enc_conf_some: forall (i: nat),
  Int.add (Int.repr (Z.of_nat i)) (Int.repr 1) = Int.repr (enc_conf (Some i)).
Proof. intros i. apply add_repr. Qed.

(* Replacing an entry of a list past its first. *)
Lemma set_nth_cons: forall (d: nat) (y a: Lit) (ls: list Lit),
  set_nth (S d) y (a :: ls) = a :: set_nth d y ls.
Proof. intros d y a ls. reflexivity. Qed.

(* swap_watch finds the first entry d that is not false, and puts p in its place. *)
Lemma swap_watch_at: forall (v: Values) (p: Lit) (ls: list Lit) (d: nat),
  (d < length ls)%nat -> ~ LitFalse v ls d ->
  (forall (d': nat), (d' < d)%nat -> LitFalse v ls d') ->
  swap_watch v p ls = Some (nth d ls (Pos 0%nat), set_nth d p ls).
Proof.
  intros v p ls. induction ls as [|y ls IH]; intros d Hd Hnf Hbefore; simpl in Hd.
  - lia.
  - destruct d as [|d].
    + simpl. unfold not_false. cbn [nth] in Hnf.
      destruct (lookup v y) as [[|]|]; try contradiction; reflexivity.
    + assert (Hy: lookup v y = Some false) by (apply (Hbefore 0%nat); lia).
      simpl. unfold not_false. rewrite Hy. cbn [nth] in Hnf |- *. rewrite (IH d).
      * reflexivity.
      * lia.
      * assumption.
      * intros d' Hd'. apply (Hbefore (S d')). lia.
Qed.

(* The new clause after the watch moves from p, second, to r, at position d >= 2. *)
Lemma set_nth_move: forall (d: nat) (o r p: Lit) (ls: list Lit), (2 <= d)%nat ->
  set_nth d p (o :: r :: ls) = o :: r :: set_nth (d - 2) p ls.
Proof.
  intros [|[|d]] o r p ls Hd.
  - lia.
  - lia.
  - rewrite !set_nth_cons. replace (S (S d) - 2)%nat with d by lia.
    reflexivity.
Qed.

(* The length e - b of a clause, as C computes it from its range. *)
Lemma eval_clause_len: forall (le: temp_env) (m: mem) (b e: nat),
  le ! _b = Some (vnat b) -> le ! _e = Some (vnat e) ->
    (b <= e)%nat ->
  eval_expr ge empty_env le m (Ebinop Osub (Etempvar _e tint) (Etempvar _b tint) tint)
    (vnat (e - b)).
Proof.
  intros le m b e Hb He Hbe. eapply eval_Ebinop.
  - apply eval_Etempvar. apply He.
  - apply eval_Etempvar. apply Hb.
  - unfold vint. cbn. unfold sem_binarith, sem_cast, tint. cbn. cbv [Archi.ptr64]. cbn.
    rewrite sub_repr. do 3 f_equal. lia.
Qed.

(* The parts of visit proved in lemmas of their own: the loop and the end after it; in
   the loop body the slow path past a true blocker, the test of the length of the clause,
   the tail that keeps the watcher and k++; for a clause watching p, the test of its
   other watch o, the search for a new watch, and what follows when one is found or
   not. *)
Definition visit_loop: statement := first_stmt (drop_stmts 4 (fn_body f_visit)).
Definition visit_end: statement := drop_stmts 5 (fn_body f_visit).
Definition visit_body: statement := drop_stmts 1 (loop_body visit_loop).
Definition visit_slow: statement := drop_stmts 3 visit_body.
Definition visit_len: statement := first_stmt (drop_stmts 3 visit_slow).
Definition visit_tail: statement := drop_stmts 4 visit_slow.
Definition visit_keep: statement := first_stmt visit_tail.
Definition visit_incr: statement := drop_stmts 1 visit_tail.
Definition visit_watch: statement := then_stmt (else_stmt visit_len).
Definition visit_test: statement := then_stmt (drop_stmts 4 visit_watch).
Definition visit_search: statement := else_stmt (drop_stmts 1 visit_test).
Definition visit_move: statement := then_stmt (drop_stmts 1 visit_search).
Definition visit_unit: statement := else_stmt (drop_stmts 1 visit_search).

(* Keeping watcher (i, kb), which C does in two places, with the temporaries tw1 and tw2
   for s->wpool, followed by rest:
     s->wpool[base + 2 * j] = i; s->wpool[base + 2 * j + 1] = kb; rest *)
Definition keep_stmt (tw1 tw2: ident) (rest: statement): statement :=
  Ssequence
    (Ssequence
      (Sset tw1
        (Efield (Ederef (Etempvar _s (tptr (Tstruct _solver noattr)))
                   (Tstruct _solver noattr)) _wpool (tptr tint)))
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar tw1 (tptr tint))
            (Ebinop Oadd (Etempvar _base tint)
              (Ebinop Omul (Econst_int (Int.repr 2) tint) (Etempvar _j tint) tint) tint)
            (tptr tint)) tint) (Etempvar _i tint)))
    (Ssequence
      (Ssequence
        (Sset tw2
          (Efield (Ederef (Etempvar _s (tptr (Tstruct _solver noattr)))
                     (Tstruct _solver noattr)) _wpool (tptr tint)))
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar tw2 (tptr tint))
              (Ebinop Oadd
                (Ebinop Oadd (Etempvar _base tint)
                  (Ebinop Omul (Econst_int (Int.repr 2) tint) (Etempvar _j tint) tint)
                  tint)
                (Econst_int (Int.repr 1) tint) tint) (tptr tint)) tint)
          (Etempvar _kb tint)))
      rest).

(* The two places C keeps a watcher, with the temporaries tw1 and tw2 for s->wpool: when
   its blocker is true, and after its clause. *)
Definition KeepTemps (tw1 tw2: ident): Prop :=
  (tw1 = _t'24 /\ tw2 = _t'23) \/ (tw1 = _t'9 /\ tw2 = _t'8).

Section Visit.
  Variables (sh: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx) (p: Lit).

  (* The watch list of p, and what visit gives on it. *)
  Abbreviation ws := (watching (wls x) p).
  Abbreviation res := (visit p ws [] x).

  (* In this section, VisitTemps and VisitMem (KeepRest.v) are those of this visit. *)
  Abbreviation VisitTemps j k le := (VisitTemps sh x p j k le).
  Abbreviation VisitMem k kept xc t m := (VisitMem sh N lss x p k kept xc t m).

  (* What visit returns. *)
  Definition VisitPost (m': mem) (v: val): Prop := ConfOut sh N lss res m' v.

  (* The temporaries at the watcher of clause i at position k, with j watchers kept: kb
     holds z. *)
  Record WatcherTemps {j k i: nat} {z: Z} {le: temp_env}: Prop := {
    wt_visit: VisitTemps j k le;
    wt_i: le ! _i = Some (vnat i);
    wt_kb: le ! _kb = Some (vint z)
  }.
  Arguments WatcherTemps : clear implicits.

  (* The invariant of the loop at position k: the watchers before k are visited, and what
     remains of visit is the visit of those from k on. After the body for position k,
     before k++, the same holds for k + 1 with k in the temporaries. *)
  Definition visit_at (k kt: nat) (le: temp_env) (m: mem): Prop :=
    exists (kept: list Watcher) (xc: Ctx) (t: nat -> Z),
    VisitTemps (length kept) kt le /\ VisitMem k kept xc t m /\
    res = visit p (skipn k ws) kept xc.

  (* The invariant at the test of the loop at position k. *)
  Definition visit_inv (k: nat) (le: temp_env) (m: mem): Prop :=
    visit_at k k le m.

  (* The watcher at position k is done, before k++. *)
  Definition visit_done (k: nat) (le: temp_env) (m: mem): Prop :=
    visit_at (S k) k le m.

  (* The loop ends: the number n - k of watchers left decreases. *)
  Definition visit_variant: nat -> nat -> Prop :=
    ltof nat (fun (k: nat) => length ws - k)%nat.

  (* After the clause of the watcher at position k is looked at: the context is xc, the
     temporary kb holds the blocker to keep the watcher with, or -1 to drop it, and
     visit goes on from k + 1. *)
  Definition visit_chosen (k: nat) (le: temp_env) (m: mem): Prop :=
    exists (kept: list Watcher) (xc: Ctx) (t: nat -> Z) (i: nat) (ob: option Lit),
    WatcherTemps (length kept) k i (enc_lit ob) le /\ VisitMem k kept xc t m /\
    (k < length ws)%nat /\ (i < length lss)%nat /\
    (forall (b: Lit), ob = Some b -> (extract b < N)%nat) /\
    res =
      visit p (skipn (S k) ws)
        (match ob with Some b => (i, b) :: kept | None => kept end) xc.

  (* What must hold after the loop body at position k: the loop goes on (visit_inv), or
     visit returns. *)
  Definition VisitK (k: nat): temp_env -> mem -> outcome -> Prop :=
    LoopK visit_variant visit_inv (SeqK ge visit_end (Returns f_visit VisitPost)) k.

  (* The end of the loop body:

       {{ visit_done k }}  k++;  {{ visit_inv (k + 1) }}                               *)
  Lemma visit_incr_correct: forall (k: nat) (le: temp_env) (m: mem),
    visit_done k le m ->
    Exec ge le m visit_incr (VisitK k).
  Proof.
    intros k le m (kept & xc & t & HT & HM & Hvisit).
    pose proof (visit_room sh N lss x p _ kept xc t m HM) as (Hcap & Hroom & Hsmall).
    pose proof (vm_le HM) as Hle.
    pose proof HT as [Hs Hp Hbase Hn Hj Hk].
    assert (Hk1: Int.add (Int.repr (Z.of_nat k)) (Int.repr 1)
                 = Int.repr (Z.of_nat (S k))).
    { apply incr_nat. lia. }
    unfold visit_incr, visit_tail, visit_slow, visit_body, visit_loop, f_visit.
    cbn [fn_body drop_stmts first_stmt loop_body Swhile].
    run. ints. apply loopk_next with (S k).
    - unfold visit_variant, ltof. lia.
    - exists kept, xc, t. split.
      + constructor; tmp.
      + split; assumption.
  Qed.

  (* Keeping the watcher (i, b) at position k, with the temporaries tw1 and tw2 for
     s->wpool, and going on with rest:

       {{ VisitMem k kept xc /\ i, kb = b in the temporaries }}
         s->wpool[base + 2 * j] = i;                                     (visit_mem_keep)
         s->wpool[base + 2 * j + 1] = kb;
       {{ VisitMem (k + 1) ((i, b) :: kept) xc }}
         rest *)
  Lemma visit_keep_correct: forall (k: nat) (kept: list Watcher) (xc: Ctx) (t: nat -> Z)
    (i: nat) (b: Lit) (tw1 tw2: ident) (rest: statement) (le: temp_env) (m: mem)
    (Q: temp_env -> mem -> outcome -> Prop),
    KeepTemps tw1 tw2 -> WatcherTemps (length kept) k i (key b) le ->
    VisitMem k kept xc t m ->
    (k < length ws)%nat -> (i < length lss)%nat -> (extract b < N)%nat ->
    (forall (le': temp_env) (m': mem),
       WatcherTemps (length kept) k i (key b) le' ->
       VisitMem (S k) ((i, b) :: kept) xc
         (set_watcher t (offs sh (lit_key p) + length kept) (i, b)) m' ->
       Exec ge le' m' rest Q) ->
    Exec ge le m (keep_stmt tw1 tw2 rest) Q.
  Proof.
    intros k kept xc t i b tw1 tw2 rest le m Q Htw [HT Hi Hkb] HM Hkn Hi_lt Hb Hrest.
    pose proof (visit_room sh N lss x p k kept xc t m HM) as (Hcap & Hroom & Hsmall).
    pose proof HM as [_ Hle HRep _ Apool _ _ _ _ _].
    pose proof (key_small b N Hb (r_n HRep)) as Hkey.
    pose proof (r_wpool HRep) as Fwpool.
    destruct (watcher_entry (offs sh (lit_key p)) (length kept) ltac:(lia))
      as [Hej Hej1].
    assert (Hlt0: (2 * (offs sh (lit_key p) + length kept) < 2 * npool sh)%nat) by lia.
    assert (Hlt: (2 * (offs sh (lit_key p) + length kept) + 1 < 2 * npool sh)%nat)
      by lia.
    unfold keep_stmt. pose proof HT as [Hs Hpk Hbase Hn Hj Hk].
    (* tw1 and tw2 are none of the temporaries that VisitTemps describes, nor i and kb *)
    set (le1 := PTree.set tw1 (Vptr (b_wpool sh) Ptrofs.zero) le).
    set (le2 := PTree.set tw2 (Vptr (b_wpool sh) Ptrofs.zero) le1).
    assert (HW1: WatcherTemps (length kept) k i (key b) le1).
    { subst le1. destruct Htw as [[-> ->] | [-> ->]]; constructor; try tmp; constructor;
        tmp. }
    assert (HW2: WatcherTemps (length kept) k i (key b) le2).
    { subst le2 le1. destruct Htw as [[-> ->] | [-> ->]]; constructor; try tmp;
        constructor; tmp. }
    assert (Htw1: le1 ! tw1 = Some (Vptr (b_wpool sh) Ptrofs.zero)).
    { subst le1. apply PTree.gss. }
    assert (Htw2: le2 ! tw2 = Some (Vptr (b_wpool sh) Ptrofs.zero)).
    { subst le2. apply PTree.gss. }
    pose proof HW1 as [[Hs1 Hpk1 Hbase1 Hn1 Hj1 Hk1] Hi1 Hkb1].
    (* s->wpool[base + 2 * j] = i; *)
    run. fold le1. store Apool Hlt0 as m1 Hst1.
    pose proof (arr_store Apool Hlt0 Hst1) as Apool1.
    pose proof (rep_store_pool m m1 _ _ HRep Hst1) as HRep1.
    pose proof (Rep.r_wpool HRep1) as Fwpool1.
    pose proof HW2 as [[Hs2 Hpk2 Hbase2 Hn2 Hj2 Hk2] Hi2 Hkb2].
    (* s->wpool[base + 2 * j + 1] = kb; *)
    run. fold le2. store Apool1 Hlt as m2 Hst2.
    apply Hrest.
    - assumption.
    - apply (visit_mem_keep sh N lss x p k kept xc t (i, b) m m1 m2); assumption.
  Qed.

  (* The tail of the loop body, after the clause of the watcher at position k:

       {{ visit_chosen k: kb is the blocker to keep it with, or -1 }}
         if (kb >= 0) { s->wpool[base + 2 * j] = i;
                        s->wpool[base + 2 * j + 1] = kb; j++; }    (visit_keep_correct)
       {{ visit_done k }}
         k++;                                                     (visit_incr_correct) *)
  Lemma visit_tail_correct: forall (k: nat) (le: temp_env) (m: mem),
    visit_chosen k le m ->
    Exec ge le m visit_tail (VisitK k).
  Proof.
    intros k le m
      (kept & xc & t & i & ob & HW & HM & Hkn & Hi_lt & Hob & Hvisit).
    pose proof HW as [HT Hi Hkb].
    pose proof (visit_room sh N lss x p k kept xc t m HM) as (Hcap & Hroom & Hsmall).
    pose proof (vm_le HM) as Hle.
    pose proof HM as [_ _ HRep _ _ _ _ _ _ _].
    change visit_tail with (Ssequence visit_keep visit_incr). apply exec_seq.
    unfold visit_keep, visit_tail, visit_slow, visit_body, visit_loop, f_visit.
    cbn [fn_body drop_stmts first_stmt loop_body Swhile].
    destruct ob as [b|].
    - (* keep the watcher with blocker b *)
      pose proof (Hob b eq_refl) as Hb.
      pose proof (key_small b N Hb (r_n HRep)) as Hkey.
      branch (key b) 0.
      + intros Hge. apply (visit_keep_correct k kept xc t i b _t'9 _t'8).
        * right. split; reflexivity.
        * assumption.
        * assumption.
        * assumption.
        * assumption.
        * assumption.
        * intros le' m' HW' HM'. pose proof HW' as [[Hs Hpk Hbase Hn Hj Hk] Hi' Hkb'].
          assert (Hj_incr: Int.add (Int.repr (Z.of_nat (length kept))) (Int.repr 1)
                           = Int.repr (Z.of_nat (length ((i, b) :: kept)))).
          { apply incr_nat. lia. }
          (* j++; *)
          run. ints. apply visit_incr_correct.
          exists ((i, b) :: kept), xc. eexists. splits.
          -- constructor; tmp.
          -- apply HM'.
          -- assumption.
      + intros Hlt. lia.
    - (* drop the watcher: kb = -1 *)
      branch (-1) 0.
      + intros Hge. lia.
      + intros Hlt. apply exec_skip. normal.
        apply visit_incr_correct. exists kept, xc, t. splits.
        * apply HW.
        * apply (visit_mem_next sh N lss x p k kept xc t m); assumption.
        * assumption.
  Qed.

  (* The state of the loop body at the watcher (i, b) at position k, past its blocker, at
     its clause i in the context xc: the temporaries hold i, kb = -1 and the range b .. e
     of the clause. *)
  Record ClauseAt {k: nat} {kept: list Watcher} {xc: Ctx} {t: nat -> Z} {i: nat}
    {le: temp_env} {m: mem}: Prop := {
    ca_temps: WatcherTemps (length kept) k i (-1) le;
    ca_b: le ! _b = Some (vnat (starts sh i));
    ca_e: le ! _e = Some (vnat (starts sh (S i)));
    ca_mem: VisitMem k kept xc t m;
    ca_k: (k < length ws)%nat;
    ca_cls: (i < length lss)%nat
  }.
  Arguments ClauseAt : clear implicits.

  (* What visit does with the watcher of clause i at position k of ws once the clause is
     o :: p :: ls in x1: keep it with blocker o if o is true, move the watch from p to a
     literal of ls that is not false, propagate o, or stop at a conflict. *)
  Definition visit_rest (k: nat) (kept: list Watcher) (x1: Ctx) (i: nat) (o: Lit)
    (ls: list Lit): Ctx * option nat :=
    if lookup_true (vals x1) o then visit p (skipn (S k) ws) ((i, o) :: kept) x1
    else
    match swap_watch (vals x1) p ls with
    | Some (r, ls') => visit p (skipn (S k) ws) kept
      (move_watch x1 i (o :: r :: ls') r o)
    | None          =>
      if lookup_undef (vals x1) o
      then visit p (skipn (S k) ws) ((i, o) :: kept)
        (assign x1 o (input i))
      else (set_watching x1 p (rev_append kept (skipn k ws)), Some i)
    end.

  (* The other watch o of the clause o :: p :: ls has no literal of ls to take the place
     of p:

       {{ ClauseAt k kept x1 /\ o in the temporaries }}
         if (lit_value(s, o) == 0) {                                (lit_value_correct)
           if (!assign(s, o, i + 1)) return -1;                        (assign_correct)
       {{ result = -1 (out of room) }}
           kb = o;
       {{ visit_chosen k with assign x1 o (input i), kb = o }}
         } else {
           keep_rest(s, p, j, k, n);                                (keep_rest_correct)
           return i + 1;
       {{ result = i + 1 /\ VisitPost }}
         }                                                   *)
  Lemma visit_unit_correct: forall (k: nat) (kept: list Watcher) (x1: Ctx) (t: nat -> Z)
    (i: nat) (o: Lit) (le: temp_env) (m: mem),
    ClauseAt k kept x1 t i le m -> le ! _o = Some (vint (key o)) ->
    (extract o < N)%nat ->
    res =
      (if lookup_undef (vals x1) o
       then visit p (skipn (S k) ws) ((i, o) :: kept)
              (assign x1 o (input i))
       else (set_watching x1 p (rev_append kept (skipn k ws)), Some i)) ->
    Exec ge le m visit_unit (SeqK ge visit_tail (VisitK k)).
  Proof.
    intros k kept x1 t i o le m [[HT Hi Hkb] Hb He HM Hkn Hi_lt] Ho Ho_lt
      Hvisit.
    pose proof HM as [_ _ HRep _ Apool _ _ _ _ _].
    pose proof (key_small o N Ho_lt (r_n HRep)) as Hko.
    pose proof HT as [Hs Hpk Hbase Hn Hj Hk].
    unfold visit_unit, visit_search, visit_test, visit_watch, visit_len, visit_slow,
      visit_body, visit_loop, f_visit.
    cbn [fn_body drop_stmts first_stmt loop_body then_stmt else_stmt Swhile].
    (* if (lit_value(s, o) == 0) *)
    run. call lit_value_fun (lit_value_correct sh N lss x1 o).
    - split; assumption.
    - intros m' v [-> ->]. normal. eapply (exec_if_eq _ 0).
      + ev.
      + ev.
      + reflexivity.
      + split.
        * apply enc_small.
        * lia.
      + (* o is unassigned: if (!assign(s, o, i + 1)) return -1; *)
        intros Hzero. apply Z.eqb_eq in Hzero. rewrite enc_undef in Hzero.
        rewrite Hzero in Hvisit. run.
        eapply (exec_call_triple assign_fun
                  (assign_correct sh N lss x1 o (input i) t)).
        * reflexivity.
        * (* the reason is input i, encoded as i + 1 *)
          cbn [enc_reason]. unfold vint. rewrite <- add_repr. evs.
        * split.
          -- assumption.
          -- split.
             ++ assumption.
             ++ split; assumption.
        * intros m1 v Hv. normal. destruct Hv as [-> | (-> & HRep1 & Apool1)].
          -- (* out of room *)
             branch 1.
             ++ intros _. return_int.
                left. reflexivity.
             ++ intros Hone_zero. lia.
          -- (* kb = o: keep the watcher with blocker o *)
             branch 0.
             ++ intros Hzero_nonzero. lia.
             ++ intros _. apply exec_skip. normal. run. apply visit_tail_correct.
                exists kept, (assign x1 o (input i)), t, i, (Some o). splits.
                ** constructor; try tmp.
                   constructor; tmp.
                ** apply (visit_mem_ctx sh N lss x p k kept x1 _ t m
                     m1).
                   --- assumption.
                   --- assumption.
                   --- assumption.
                   --- reflexivity.
                   --- reflexivity.
                ** assumption.
                ** assumption.
                ** intros b' Heq. injection Heq as <-.
                   assumption.
                ** assumption.
      + (* o is false: a conflict, keep_rest(s, p, j, k, n); return i + 1; *)
        intros Hnonzero. apply Z.eqb_neq in Hnonzero. rewrite enc_undef in Hnonzero.
        rewrite Hnonzero in Hvisit. run.
        call keep_rest_fun (keep_rest_correct sh N lss x p k kept x1 t).
        * assumption.
        * intros m' v HRep'. normal. eapply exec_return.
          -- ev.
          -- ret. cbn [cast_int_int]. rewrite enc_conf_some.
             exists (vint (enc_conf (Some i))). split.
             ++ apply result_int.
             ++ right. rewrite Hvisit. cbn [fst snd]. splits.
                ** reflexivity.
                ** assumption.
                ** intros i' Heq. injection Heq as <-. assumption.
  Qed.

  (* Moving the watch p of the clause o :: p :: ls to r, its literal d >= 2, which
     find_watch found at q:

       {{ ClauseAt k kept x1 /\ o and q = starts i + d in the temporaries }}
         int r = s->clits[q];
         s->clits[b + 1] = r; s->clits[q] = p;                         (rep_store_clits)
       {{ the clause is o :: r :: ls' in x2, ls' being ls with p in place of r }}
         if (!wpush(s, r, i, o)) return -1;                              (wpush_correct)
       {{ result = -1 (out of room) }}
       {{ visit_chosen k with move_watch x1 i (o :: r :: ls') r o, kb = -1 }}
                                                                      (visit_mem_push) *)
  Lemma visit_move_correct: forall (k: nat) (kept: list Watcher) (x1: Ctx) (t: nat -> Z)
    (i: nat) (o: Lit) (ls: list Lit) (d: nat) (le: temp_env) (m: mem),
    ClauseAt k kept x1 t i le m -> le ! _o = Some (vint (key o)) ->
    le ! _q = Some (vnat (starts sh i + d)) ->
    tget (cmap x1) i = Some (o :: p :: ls) -> (2 <= d < length (o :: p :: ls))%nat ->
    (extract o < N)%nat ->
    res =
      visit p (skipn (S k) ws) kept
        (move_watch x1 i (o :: nth (d - 2) ls (Pos 0%nat) :: set_nth (d - 2) p ls)
           (nth (d - 2) ls (Pos 0%nat)) o) ->
    Exec ge le m visit_move (SeqK ge visit_tail (VisitK k)).
  Proof.
    intros k kept x1 t i o ls d le m [[HT Hi Hkb] Hb He HM Hkn Hi_lt] Ho Hq
      Hcls Hd Ho_lt Hvisit.
    pose proof HM as [Hp _ HRep _ Apool Hpool _ _ [extra Hext] _].
    pose proof (r_n HRep) as HN.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (key_small p N Hp HN) as Hkp.
    pose proof (key_small o N Ho_lt HN) as Hko.
    pose proof (r_clits HRep) as Fclits.
    pose proof (r_nclits_small HRep) as Hnclits.
    pose proof (a_lits HRep) as (tl & Alits & Hclauses).
    destruct (r_starts HRep i Hi_lt) as [Hsi Hsn].
    (* r, literal d of the clause, is literal d - 2 of ls *)
    set (r := nth (d - 2) ls (Pos 0%nat)) in *.
    assert (Hr_nth: nth d (o :: p :: ls) (Pos 0%nat) = r).
    { subst r. destruct d as [|[|d']].
      - lia.
      - lia.
      - cbn [nth]. replace (S (S d') - 2)%nat with d' by lia.
        reflexivity. }
    destruct (clause_lit m sh N lss x1 tl i d (o :: p :: ls) HRep Hclauses Hi_lt Hcls)
      as (Hpos & Htl & Hr_lt).
    { lia. }
    rewrite Hr_nth in Htl, Hr_lt.
    pose proof (key_small r N Hr_lt HN) as Hkr.
    pose proof HT as [Hs Hpk Hbase Hn Hj Hk].
    assert (Hb1: Int.add (Int.repr (Z.of_nat (starts sh i))) (Int.repr 1)
                 = Int.repr (Z.of_nat (starts sh i + 1))).
    { rewrite add_repr. f_equal. lia. }
    assert (Hb1_lt: (starts sh i + 1 < nclits sh)%nat) by lia.
    assert (Hq_lt: (starts sh i + d < nclits sh)%nat) by lia.
    unfold visit_move, visit_search, visit_test, visit_watch, visit_len, visit_slow,
      visit_body, visit_loop, f_visit.
    cbn [fn_body drop_stmts first_stmt loop_body then_stmt else_stmt Swhile].
    (* int r = s->clits[q]; s->clits[b + 1] = r; *)
    run. rewrite Htl. store Alits Hb1_lt as m1 Hst1.
    pose proof
      (rep_store_clits m m1 i 1 (o :: p :: ls) r HRep Hi_lt Hcls
                  ltac:(cbn [length]; lia) Hr_lt Hst1) as HRep1.
    cbn [set_nth firstn skipn app] in HRep1.
    pose proof (arr_store_other Apool Hst1 ltac:(neq Hnd)) as Apool1.
    pose proof (Rep.r_clits HRep1) as Fclits1.
    pose proof (Rep.a_lits HRep1) as (tl1 & Alits1 & _).
    keep_mem m1.
    (* s->clits[q] = p; *)
    run. store Alits1 Hq_lt as m2 Hst2.
    pose proof
      (rep_store_clits m1 m2 i
                  d (o :: r :: ls) p HRep1 Hi_lt (tget_tset_same _ _ _)
                  ltac:(cbn [length] in *; lia) Hp Hst2) as HRep2.
    apply rep_clause_twice in HRep2. rewrite set_nth_move in HRep2 by lia.
    set (x2 := set_clause x1 i (o :: r :: set_nth (d - 2) p ls)) in *.
    pose proof
      (arr_store_other Apool1 Hst2 ltac:(neq Hnd)) as Apool2.
    assert (HM2: VisitMem k kept x2 t m2).
    { apply (visit_mem_ctx sh N lss x p k kept x1 x2 t m m2).
      - assumption.
      - assumption.
      - assumption.
      - reflexivity.
      - reflexivity. }
    keep_mem m2.
    (* if (!wpush(s, r, i, o)) return -1; *)
    run. call wpush_fun
      (wpush_correct sh N lss x2 r i o t (SkipP (lit_key p) (length ws))).
    - split.
      + assumption.
      + split.
        * assumption.
        * split.
          -- apply HM2.
          -- split.
             ++ (* the skipped watchers are within ws, which the list of p
                   starts with *)
                intros q' [Heq Hq']. unfold watching.
                cbn [set_clause wls x2].
                rewrite Heq. fold (watching (wls x1) p).
                rewrite Hext, length_app.
                lia.
             ++ split.
                ** assumption.
                ** split; assumption.
    - intros m3 v Hv. normal.
      destruct Hv as [-> | (-> & HRep3 & Apool3 & Hpool3 & _)].
      + (* out of room *)
        branch 1.
        * intros _. return_int.
          left. reflexivity.
        * intros Hone_zero. lia.
      + (* the watch moved: drop the watcher, kb = -1 *)
        branch 0.
        * intros Hzero_nonzero. lia.
        * intros _. apply exec_skip. normal. apply visit_tail_correct.
          exists kept, (move_watch x1 i (o :: r :: set_nth (d - 2) p ls) r o).
          eexists. exists i, None. splits.
          -- constructor; try tmp.
             constructor; tmp.
          -- rewrite move_watch_split.
             apply (visit_mem_push sh N lss x p k kept x2 t i r o
                      m2 m3); assumption.
          -- assumption.
          -- assumption.
          -- intros b' Heq. discriminate.
          -- assumption.
  Qed.

  (* The other watch o of the clause o :: p :: ls is not true: search ls for a new watch.

       {{ ClauseAt k kept x1 /\ o in the temporaries /\ o is not true }}
         int q = find_watch(s, b + 2, e);                            (find_watch_correct)
         if (q >= 0) ...                                             (visit_move_correct)
         else ...                                                    (visit_unit_correct)
  *)
  Lemma visit_search_correct: forall (k: nat) (kept: list Watcher) (x1: Ctx)
    (t: nat -> Z) (i: nat) (o: Lit) (ls: list Lit) (le: temp_env) (m: mem),
    ClauseAt k kept x1 t i le m -> le ! _o = Some (vint (key o)) ->
    tget (cmap x1) i = Some (o :: p :: ls) -> (extract o < N)%nat ->
    lookup_true (vals x1) o = false ->
    res = visit_rest k kept x1 i o ls ->
    Exec ge le m visit_search (SeqK ge visit_tail (VisitK k)).
  Proof.
    intros k kept x1 t i o ls le m HC Ho Hcls Ho_lt Hnt Hvisit.
    pose proof HC as [[HT Hi Hkb] Hb He HM Hkn Hi_lt].
    pose proof HM as [_ _ HRep _ _ _ _ _ _ _].
    pose proof (r_nclits_small HRep) as Hnclits.
    destruct (r_starts HRep i Hi_lt) as [Hsi Hsn].
    pose proof (a_lits HRep) as (tl & _ & Hclauses).
    pose proof
      (clause_length sh N lss x1 tl i (o :: p :: ls) Hclauses Hi_lt Hcls)
      as Hlen.
    pose proof HT as [Hs Hpk Hbase Hn Hj Hk].
    unfold visit_rest in Hvisit. rewrite Hnt in Hvisit.
    assert (Hb2: Int.add (Int.repr (Z.of_nat (starts sh i))) (Int.repr 2)
                 = Int.repr (Z.of_nat (starts sh i + 2))).
    { rewrite add_repr. f_equal. lia. }
    unfold visit_search, visit_test, visit_watch, visit_len, visit_slow, visit_body,
      visit_loop, f_visit.
    cbn [fn_body drop_stmts first_stmt loop_body then_stmt else_stmt Swhile].
    (* int q = find_watch(s, b + 2, e); *)
    apply exec_seq. run.
    eapply (exec_call_triple find_watch_fun
              (find_watch_correct sh N lss x1 i 2 (o :: p :: ls))).
    - reflexivity.
    - (* the search starts at b + 2 *)
      unfold vint. rewrite <- Hb2. evs.
    - splits.
      + assumption.
      + assumption.
      + assumption.
      + cbn [length]. lia.
    - intros m' v [-> Hfound]. normal. run.
      destruct Hfound as [[-> Hall] | (d & Hd & -> & Hnf & Hbefore)].
      + (* no literal of ls is not false: q = -1 *)
        assert (Hnone: swap_watch (vals x1) p ls = None).
        { apply swap_watch_all_false. intros d Hd.
          apply (Hall (S (S d))). cbn [length]. lia. }
        rewrite Hnone in Hvisit.
        branch (-1) 0.
        * intros Hge. lia.
        * intros Hlt. apply (visit_unit_correct k kept x1 t i o).
          -- constructor; try tmp.
             ++ constructor; try tmp.
                constructor; tmp.
             ++ assumption.
             ++ assumption.
             ++ assumption.
          -- tmp.
          -- assumption.
          -- assumption.
      + (* literal d >= 2 is not false: q = starts i + d *)
        assert (Hsome: swap_watch (vals x1) p ls =
                       Some (nth (d - 2) ls (Pos 0%nat), set_nth (d - 2) p ls)).
        { apply swap_watch_at.
          - cbn [length] in Hd. lia.
          - destruct d as [|[|d']].
            + lia.
            + lia.
            + cbn [nth] in Hnf.
              replace (S (S d') - 2)%nat with d' by lia.
              assumption.
          - intros d' Hd'. apply (Hbefore (S (S d'))). lia. }
        rewrite Hsome in Hvisit.
        branch (Z.of_nat (starts sh i + d)) 0.
        * intros Hge. apply (visit_move_correct k kept x1 t i o ls d).
          -- constructor; try tmp.
             ++ constructor; try tmp.
                constructor; tmp.
             ++ assumption.
             ++ assumption.
             ++ assumption.
          -- tmp.
          -- tmp.
          -- assumption.
          -- assumption.
          -- assumption.
          -- assumption.
        * intros Hlt. lia.
  Qed.

  (* The clause of the watcher at position k is o :: p :: ls in x1:

       {{ ClauseAt k kept x1 /\ o in the temporaries }}
         if (lit_value(s, o) == 1) kb = o;                            (lit_value_correct)
       {{ visit_chosen k with kb = o }}
         else ...                                               (visit_search_correct) *)
  Lemma visit_test_correct: forall (k: nat) (kept: list Watcher) (x1: Ctx) (t: nat -> Z)
    (i: nat) (o: Lit) (ls: list Lit) (le: temp_env) (m: mem),
    ClauseAt k kept x1 t i le m -> le ! _o = Some (vint (key o)) ->
    tget (cmap x1) i = Some (o :: p :: ls) -> (extract o < N)%nat ->
    res = visit_rest k kept x1 i o ls ->
    Exec ge le m visit_test (SeqK ge visit_tail (VisitK k)).
  Proof.
    intros k kept x1 t i o ls le m HC Ho Hcls Ho_lt Hvisit.
    pose proof HC as [[HT Hi Hkb] Hb He HM Hkn Hi_lt].
    pose proof HM as [_ _ HRep _ _ _ _ _ _ _].
    pose proof (key_small o N Ho_lt (r_n HRep)) as Hko.
    pose proof HT as [Hs Hpk Hbase Hn Hj Hk].
    unfold visit_test, visit_watch, visit_len, visit_slow, visit_body, visit_loop,
      f_visit.
    cbn [fn_body drop_stmts first_stmt loop_body then_stmt else_stmt Swhile].
    (* if (lit_value(s, o) == 1) *)
    run. call lit_value_fun (lit_value_correct sh N lss x1 o).
    - split; assumption.
    - intros m' v [-> ->]. normal. eapply (exec_if_eq _ 1).
      + ev.
      + ev.
      + reflexivity.
      + split.
        * apply enc_small.
        * lia.
      + (* o is true: kb = o, keep the watcher with blocker o *)
        intros Htrue. apply Z.eqb_eq in Htrue. rewrite enc_true in Htrue.
        run. apply visit_tail_correct.
        exists kept, x1, t, i, (Some o). splits.
        * constructor; try tmp.
          constructor; tmp.
        * assumption.
        * assumption.
        * assumption.
        * intros b' Heq. injection Heq as <-. assumption.
        * unfold visit_rest in Hvisit. rewrite Htrue in Hvisit.
          assumption.
      + (* look for a new watch *)
        intros Hnot_true. apply Z.eqb_neq in Hnot_true. rewrite enc_true in Hnot_true.
        apply (visit_search_correct k kept x1 t i o ls).
        * constructor; try tmp.
          -- constructor; try tmp.
             constructor; tmp.
          -- assumption.
          -- assumption.
          -- assumption.
        * tmp.
        * assumption.
        * assumption.
        * assumption.
        * assumption.
  Qed.

  (* The clause c0 :: c1 :: ls of the watcher at position k, with two literals or more:

       {{ ClauseAt k kept xc }}
         int o = s->clits[b];
         if (o == p) { o = s->clits[b + 1];
                       s->clits[b] = o; s->clits[b + 1] = p; }         (rep_store_clits)
         if (s->clits[b + 1] == p) ...                               (visit_test_correct)
       {{ visit_chosen k, dropped: the clause does not watch p }}

     When the clause watches p, it is o :: p :: ls in memory, o its other watch (when c1
     is p, the clause is already in that form: rep_clause_same). *)
  Lemma visit_watch_correct: forall (k: nat) (kept: list Watcher) (xc: Ctx) (t: nat -> Z)
    (i: nat) (c0 c1: Lit) (ls: list Lit) (le: temp_env) (m: mem),
    ClauseAt k kept xc t i le m ->
      tget (cmap xc) i = Some (c0 :: c1 :: ls) ->
    res =
      (let o := if c0 =? p then c1 else c0 in
       if (c0 =? p) || (c1 =? p)
       then visit_rest k kept (set_clause xc i (o :: p :: ls)) i o ls
       else visit p (skipn (S k) ws) kept xc) ->
    Exec ge le m visit_watch (SeqK ge visit_tail (VisitK k)).
  Proof.
    intros k kept xc t i c0 c1 ls le m HC Hcls Hvisit.
    pose proof HC as [[HT Hi Hkb] Hb He HM Hkn Hi_lt].
    pose proof HM as [Hp _ HRep _ Apool _ _ _ _ _].
    pose proof (r_n HRep) as HN.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (r_nclits_small HRep) as Hnclits.
    pose proof (key_small p N Hp HN) as Hkp.
    pose proof (r_clits HRep) as Fclits.
    pose proof (a_lits HRep) as (tl & Alits & Hclauses).
    (* The first two literals of the clause, at b and b + 1 *)
    destruct (clause_lit m sh N lss xc tl i 0 (c0 :: c1 :: ls) HRep Hclauses Hi_lt Hcls)
      as (Hpos0 & Htl0 & Hc0).
    { cbn [length]. lia. }
    destruct (clause_lit m sh N lss xc tl i 1 (c0 :: c1 :: ls) HRep Hclauses Hi_lt Hcls)
      as (Hpos1 & Htl1 & Hc1).
    { cbn [length]. lia. }
    cbn [nth] in Htl0, Hc0, Htl1, Hc1. rewrite Nat.add_0_r in Htl0, Hpos0.
    pose proof (key_small c0 N Hc0 HN) as Hkc0.
    pose proof (key_small c1 N Hc1 HN) as Hkc1.
    pose proof HT as [Hs Hpk Hbase Hn Hj Hk].
    assert (Hb1: Int.add (Int.repr (Z.of_nat (starts sh i))) (Int.repr 1)
                 = Int.repr (Z.of_nat (starts sh i + 1))).
    { rewrite add_repr. f_equal. lia. }
    unfold visit_watch, visit_len, visit_slow, visit_body, visit_loop, f_visit.
    cbn [fn_body drop_stmts first_stmt loop_body then_stmt else_stmt Swhile].
    (* int o = s->clits[b]; if (o == p) *)
    run. rewrite Htl0. branch.
    - (* p is first: o = s->clits[b + 1]; s->clits[b] = o; s->clits[b + 1] = p; *)
      intros Hc0p. apply Z.eqb_eq in Hc0p. rewrite key_eqb in Hc0p.
      rewrite Hc0p in Hvisit. apply Lit.eqb_eq in Hc0p as Hc0p'. subst c0.
      run. rewrite Htl1. store Alits Hpos0 as m1 Hst1.
      rewrite <- (Nat.add_0_r (starts sh i)) in Hst1.
      pose proof
        (rep_store_clits m m1 i 0 (p :: c1 :: ls) c1 HRep Hi_lt
                    Hcls ltac:(cbn [length]; lia) Hc1 Hst1) as HRep1.
      cbn [set_nth firstn skipn app] in HRep1.
      pose proof
        (arr_store_other Apool Hst1 ltac:(neq Hnd)) as Apool1.
      pose proof (Rep.r_clits HRep1) as Fclits1.
      pose proof (Rep.a_lits HRep1) as (tl1 & Alits1 & _).
      keep_mem m1.
      run. store Alits1 Hpos1 as m2 Hst2.
      pose proof
        (rep_store_clits m1 m2 i 1 (c1 :: c1 :: ls) p HRep1 Hi_lt
                      (tget_tset_same _ _ _)
                    ltac:(cbn [length]; lia) Hp Hst2) as HRep2.
      apply rep_clause_twice in HRep2. cbn [set_nth firstn skipn app] in HRep2.
      set (x1 := set_clause xc i (c1 :: p :: ls)) in *.
      pose proof (arr_store_other Apool1 Hst2 ltac:(neq Hnd))
        as Apool2.
      assert (HM2: VisitMem k kept x1 t m2).
      { apply (visit_mem_ctx sh N lss x p k kept xc x1 t m m2).
        - assumption.
        - assumption.
        - assumption.
        - reflexivity.
        - reflexivity. }
      assert (Hcls2: tget (cmap x1) i = Some (c1 :: p :: ls)) by apply
        tget_tset_same.
      pose proof (Rep.r_clits HRep2) as Fclits2.
      pose proof (Rep.a_lits HRep2)
        as (tl2 & Alits2 & Hclauses2).
      destruct (clause_lit m2 sh N lss x1 tl2 i 1
        (c1 :: p :: ls) HRep2 Hclauses2
                  Hi_lt Hcls2) as (_ & Htl2 & _).
      { cbn [length]. lia. }
      cbn [nth] in Htl2. keep_mem m2.
      (* if (s->clits[b + 1] == p): it is *)
      run. rewrite Htl2. branch.
      + intros _. cbn [orb] in Hvisit.
        apply (visit_test_correct k kept x1 t i c1 ls).
        * constructor; try tmp.
          -- constructor; try tmp.
             constructor; tmp.
          -- assumption.
          -- assumption.
          -- assumption.
        * tmp.
        * assumption.
        * assumption.
        * assumption.
      + intros Hne. lia.
    - (* p is not first *)
      intros Hc0p. apply Z.eqb_neq in Hc0p. rewrite key_eqb in Hc0p.
      rewrite Hc0p in Hvisit. apply exec_skip. normal.
      run. rewrite Htl1. branch.
      + (* p is second: the clause is c0 :: p :: ls already *)
        intros Hc1p. apply Z.eqb_eq in Hc1p. rewrite key_eqb in Hc1p.
        rewrite Hc1p in Hvisit. apply Lit.eqb_eq in Hc1p as Hc1p'. subst c1.
        cbn [orb] in Hvisit.
        apply (visit_test_correct k kept
          (set_clause xc i (c0 :: p :: ls))
                 t i c0 ls).
        * constructor; try tmp.
          -- constructor; try tmp.
             constructor; tmp.
          -- apply (visit_mem_ctx sh N lss x p k kept xc _ t m m).
             ++ assumption.
             ++ apply rep_clause_same; assumption.
             ++ assumption.
             ++ reflexivity.
             ++ reflexivity.
          -- assumption.
          -- assumption.
        * tmp.
        * apply tget_tset_same.
        * assumption.
        * assumption.
      + (* the clause does not watch p: drop the watcher, kb = -1 *)
        intros Hc1p. apply Z.eqb_neq in Hc1p. rewrite key_eqb in Hc1p.
        rewrite Hc1p in Hvisit. apply exec_skip. normal. apply visit_tail_correct.
        exists kept, xc, t, i, None. splits.
        * constructor; try tmp.
          constructor; tmp.
        * assumption.
        * assumption.
        * assumption.
        * intros b' Heq. discriminate.
        * rewrite Hvisit. reflexivity.
  Qed.

  (* The watcher (i, b) at position k, whose blocker is not true: its clause by its
     length.

       {{ visit_inv k /\ ws[k] = (i, b) /\ b is not true }}
         kb = -1; int b = s->cstart[i]; int e = s->cstart[i + 1];
       {{ ClauseAt k kept xc }}
         if (e - b == 1) {
           if (s->clits[b] == p) {
             keep_rest(s, p, j, k, n);                              (keep_rest_correct)
             return i + 1;
       {{ result = i + 1 /\ VisitPost: the unit clause [p] is false }}
           }
         } else if (e - b >= 2) ...                                (visit_watch_correct)
       {{ visit_chosen k, dropped: a short clause that does not watch p }}
         if (kb >= 0) ...; k++;                                   (visit_tail_correct) *)
  Lemma visit_slow_correct: forall (k: nat) (kept: list Watcher) (xc: Ctx) (t: nat -> Z)
    (i: nat) (b: Lit) (le: temp_env) (m: mem),
    VisitTemps (length kept) k le -> le ! _i = Some (vnat i) ->
    VisitMem k kept xc t m -> (k < length ws)%nat ->
    watcher_at ws k = (i, b) ->
    lookup_true (vals xc) b = false -> (i < length lss)%nat ->
    res = visit p
      (skipn k ws) kept xc ->
    Exec ge le m visit_slow (VisitK k).
  Proof.
    intros k kept xc t i b le m HT Hi HM Hkn Hnth Hnt Hi_lt Hvisit.
    pose proof HM as [Hp _ HRep _ _ _ _ _ _ _].
    pose proof (r_n HRep) as HN.
    pose proof (r_lss_small HRep) as Hlss.
    pose proof (r_nclits_small HRep) as Hnclits.
    pose proof (key_small p N Hp HN) as Hkp.
    pose proof (r_cstart HRep) as Fcstart.
    pose proof (a_starts HRep) as Astarts.
    pose proof (a_lits HRep) as (tl & Alits & Hclauses).
    destruct (r_starts HRep i Hi_lt) as [Hsi Hsn].
    pose proof (proj2 Hclauses i Hi_lt) as Hcls.
    set (cls := map (fun (q: nat) => lit_of (tl q))
                  (seq (starts sh i) (starts sh (S i) - starts sh i))) in Hcls.
    pose proof (clause_length sh N lss xc tl i cls Hclauses Hi_lt Hcls) as Hlen.
    (* The model: the blocker is not true, so visit looks at the clause *)
    rewrite (skipn_nth ws (0%nat, Pos 0%nat) k Hkn), Hnth in Hvisit.
    cbn [visit] in Hvisit. rewrite Hnt, Hcls in Hvisit.
    rewrite <- Hnth, <- (skipn_nth ws (0%nat, Pos 0%nat) k Hkn) in Hvisit.
    pose proof HT as [Hs Hpk Hbase Hn Hj Hk].
    assert (Hi1: Int.add (Int.repr (Z.of_nat i)) (Int.repr 1)
                 = Int.repr (Z.of_nat (S i))).
    { apply incr_nat. lia. }
    assert (Hsub: Int.sub (Int.repr (Z.of_nat (starts sh (S i))))
                    (Int.repr (Z.of_nat (starts sh i)))
                  = Int.repr (Z.of_nat (length cls))).
    { rewrite sub_repr. f_equal. lia. }
    unfold visit_slow, visit_body, visit_loop, f_visit.
    cbn [fn_body drop_stmts first_stmt loop_body Swhile].
    (* kb = -1; int b = s->cstart[i]; int e = s->cstart[i + 1]; *)
    run. clear Fcstart Astarts.
    (* if (e - b == 1) *)
    ints. eapply (exec_if_eq (Z.of_nat (length cls)) 1).
    - rewrite Hlen. apply eval_clause_len.
      + tmp.
      + tmp.
      + lia.
    - ev.
    - reflexivity.
    - lia.
    - intros Hone. destruct cls as [|c0 [|c1 ls]] eqn:Hc.
      + (* the empty clause has length 0 *)
        cbn [length] in Hone. lia.
      + (* a unit clause [c0]: false if c0 is p *)
        destruct (clause_lit m sh N lss xc tl i 0 [c0] HRep Hclauses Hi_lt Hcls)
          as (Hpos0 & Htl0 & Hc0).
        { cbn [length]. lia. }
        cbn [nth] in Htl0, Hc0. rewrite Nat.add_0_r in Htl0, Hpos0.
        pose proof (key_small c0 N Hc0 HN) as Hkc0.
        pose proof (r_clits HRep) as Fclits.
        run. rewrite Htl0. branch.
        * (* a conflict: keep_rest(s, p, j, k, n); return i + 1; *)
          intros Hc0p. apply Z.eqb_eq in Hc0p. rewrite key_eqb in Hc0p.
          rewrite Hc0p in Hvisit. run.
          call keep_rest_fun (keep_rest_correct sh N lss x p k kept xc t).
          -- assumption.
          -- intros m' v HRep'. normal. eapply exec_return.
             ++ ev.
             ++ ret. cbn [cast_int_int]. rewrite enc_conf_some.
                exists (vint (enc_conf (Some i))). split.
                ** apply result_int.
                ** right. rewrite Hvisit. cbn [fst snd]. splits.
                   --- reflexivity.
                   --- assumption.
                   --- intros i' Heq. injection Heq as <-. assumption.
        * (* [c0] does not watch p: dropped *)
          intros Hc0p. apply Z.eqb_neq in Hc0p. rewrite key_eqb in Hc0p.
          rewrite Hc0p in Hvisit. apply exec_skip. normal. apply visit_tail_correct.
          exists kept, xc, t, i, None. splits.
          -- constructor; try tmp.
             constructor; tmp.
          -- assumption.
          -- assumption.
          -- assumption.
          -- intros b' Heq. discriminate.
          -- assumption.
      + (* a clause of two literals or more has length 2 or more *)
        cbn [length] in Hone. lia.
    - intros Hnot_one. destruct cls as [|c0 [|c1 ls]] eqn:Hc.
      + (* the empty clause watches nothing: dropped *)
        eapply (exec_if_ge (Z.of_nat (length [])) 2).
        * rewrite Hlen. apply eval_clause_len.
          -- tmp.
          -- tmp.
          -- lia.
        * ev.
        * reflexivity.
        * cbn [length]. lia.
        * intros Hge. cbn [length] in Hge. lia.
        * intros Hlt. apply exec_skip. normal. apply visit_tail_correct.
          exists kept, xc, t, i, None. splits.
          -- constructor; try tmp.
             constructor; tmp.
          -- assumption.
          -- assumption.
          -- assumption.
          -- intros b' Heq. discriminate.
          -- assumption.
      + (* the unit clause has length 1 *)
        cbn [length] in Hnot_one. lia.
      + (* two literals or more *)
        eapply (exec_if_ge (Z.of_nat (length (c0 :: c1 :: ls))) 2).
        * rewrite Hlen. apply eval_clause_len.
          -- tmp.
          -- tmp.
          -- lia.
        * ev.
        * reflexivity.
        * lia.
        * intros Hge. apply (visit_watch_correct k kept xc t i c0 c1 ls).
          -- constructor; try tmp.
             ++ constructor; try tmp.
                constructor; tmp.
             ++ assumption.
             ++ assumption.
             ++ assumption.
          -- assumption.
          -- assumption.
        * intros Hlt. cbn [length] in Hlt. lia.
  Qed.

  (* The loop body at position k < n:

       {{ visit_inv k /\ k < n }}
         int i = s->wpool[base + 2 * k]; int kb = s->wpool[base + 2 * k + 1];
       {{ (i, kb) = ws[k] }}
         if (lit_value(s, kb) == 1) {                               (lit_value_correct)
           s->wpool[base + 2 * j] = i; s->wpool[base + 2 * j + 1] = kb;
                                                                   (visit_keep_correct)
           j++; k++; continue;
       {{ visit_inv (k + 1): the watcher is kept, as the blocker is true }}
         }
         ...                                                      (visit_slow_correct) *)
  Lemma visit_body_correct: forall (k: nat) (le: temp_env) (m: mem),
    visit_inv k le m -> (k < length ws)%nat ->
    Exec ge le m visit_body (VisitK k).
  Proof.
    intros k le m (kept & xc & t & HT & HM & Hvisit) Hkn.
    pose proof (visit_room sh N lss x p k kept xc t m HM) as (Hcap & Hroom & Hsmall).
    pose proof (vm_le HM) as Hle.
    pose proof HM as [Hp _ HRep _ Apool _ _ Hback _ _].
    pose proof (r_n HRep) as HN.
    pose proof (r_wpool HRep) as Fwpool.
    destruct (visit_watcher sh N lss x p k kept xc t m k HM Hkn) as [Hi_lt Hb_lt].
    destruct (Hback k) as [Hk1 Hk2].
    { lia. }
    destruct (watcher_at ws k) as [i b] eqn:Hnth.
    cbn [fst snd] in Hi_lt, Hb_lt, Hk1, Hk2.
    pose proof (key_small b N Hb_lt HN) as Hkb.
    destruct (watcher_entry (offs sh (lit_key p)) k ltac:(lia)) as [Hek Hek1].
    pose proof HT as [Hs Hpk Hbase Hn Hj Hk].
    unfold visit_body, visit_loop, f_visit.
    cbn [fn_body drop_stmts first_stmt loop_body Swhile].
    (* int i = s->wpool[base + 2 * k]; int kb = s->wpool[base + 2 * k + 1]; *)
    run. rewrite Hk1. run. rewrite Hk2.
    (* if (lit_value(s, kb) == 1) *)
    call lit_value_fun (lit_value_correct sh N lss xc b).
    - split; assumption.
    - intros m' v [-> ->]. normal. eapply (exec_if_eq _ 1).
      + ev.
      + ev.
      + reflexivity.
      + split.
        * apply enc_small.
        * lia.
      + (* the blocker is true: keep the watcher; j++; k++; continue; *)
        intros Htrue. apply Z.eqb_eq in Htrue. rewrite enc_true in Htrue.
        apply (visit_keep_correct k kept xc t i b _t'24 _t'23).
        * left. split; reflexivity.
        * constructor; try tmp.
          constructor; tmp.
        * assumption.
        * assumption.
        * assumption.
        * assumption.
        * intros le' m1 HW' HM'.
          pose proof HW' as [[Hs' Hpk' Hbase' Hn' Hj' Hk'] Hi' Hkb'].
          assert (Hj_incr: Int.add (Int.repr (Z.of_nat (length kept))) (Int.repr 1)
                           = Int.repr (Z.of_nat (length ((i, b) :: kept)))).
          { apply incr_nat. lia. }
          assert (Hk_incr: Int.add (Int.repr (Z.of_nat k)) (Int.repr 1)
                           = Int.repr (Z.of_nat (S k))).
          { apply incr_nat. lia. }
          run. apply exec_continue. abrupt. ints.
          apply loopk_continue with (S k).
          -- unfold visit_variant, ltof. lia.
          -- exists ((i, b) :: kept), xc. eexists. splits.
             ++ constructor; tmp.
             ++ apply HM'.
             ++ rewrite Hvisit,
                  (skipn_nth ws (0%nat, Pos 0%nat) k Hkn),
                  Hnth.
                cbn [visit]. rewrite Htrue. reflexivity.
      + (* look at the clause *)
        intros Hnot_true. apply Z.eqb_neq in Hnot_true. rewrite enc_true in Hnot_true.
        apply exec_skip. normal. apply (visit_slow_correct k kept xc t i b).
        * constructor; tmp.
        * tmp.
        * assumption.
        * assumption.
        * assumption.
        * assumption.
        * assumption.
        * assumption.
  Qed.

  (* The loop of visit, over the watch list ws of p:

       {{ visit_inv 0 }}
         while (k < n) { ... }              (invariant visit_inv; visit_body_correct)
       {{ visit_inv n }}
         s->wlen[p] = j; return 0;                                   (visit_mem_finish)
       {{ VisitPost }}                                                                *)
  Lemma visit_loop_correct: forall (le: temp_env) (m: mem),
    visit_inv 0 le m ->
    Exec ge le m visit_loop
      (SeqK ge visit_end (Returns f_visit (VisitPost))).
  Proof.
    intros le m Hinv.
    unfold visit_loop, f_visit. cbn [fn_body drop_stmts first_stmt]. unfold Swhile.
    apply exec_loop with (R := visit_variant) (I := visit_inv)
      (a := 0%nat).
    - apply well_founded_ltof.
    - intros k le1 m1 Hinv1.
      pose proof Hinv1 as (kept & xc & t & HT & HM & Hvisit).
      pose proof (visit_room sh N lss x p k kept xc t m1 HM)
        as (Hcap & Hroom & Hsmall).
      pose proof (vm_le HM) as Hle.
      pose proof HT as [Hs Hpk Hbase Hn Hj Hk].
      (* while (k < n) *)
      apply exec_seq. branch.
      + (* the body *)
        intros Hlt. apply exec_skip. normal. apply visit_body_correct.
        * assumption.
        * lia.
      + (* the end: s->wlen[p] = j; return 0; *)
        intros Hge. apply exec_break. abrupt. apply loopk_break. normal.
        pose proof HM as [Hp _ HRep _ _ _ _ _ _ _].
        pose proof (lit_key_lt p N Hp) as HP.
        pose proof (key_small p N Hp (r_n HRep)) as Hkp.
        pose proof Hkp as Hkp'. unfold key in Hkp'.
        pose proof (r_wlen HRep) as Fwlen.
        pose proof (a_wlen HRep) as Awlen.
        unfold visit_end, f_visit. cbn [fn_body drop_stmts].
        run. store Awlen HP as m2 Hst.
        return_int.
        right. rewrite Hvisit, skipn_all2 by lia.
        cbn [visit fst snd enc_conf].
        splits.
        * reflexivity.
        * apply (visit_mem_finish sh N lss x p k kept xc t m1 m2); assumption.
        * intros i Heq. discriminate.
    - assumption.
  Qed.

  (* visit visits the watchers of the false literal p (visit):

       {{ Rep x /\ extract p < N }}
         int base = 2 * s->woff[p]; int n = s->wlen[p]; int j = 0; int k = 0;
       {{ visit_inv 0 }}
         while (k < n) { ... }                                     (visit_loop_correct)
         s->wlen[p] = j; return 0;
       {{ ConfOut res: -1, or enc_conf r /\ Rep x' /\ (r = Some i -> i < length lss),
          where visit gives res = (x', r) }}                                          *)
  Lemma visit_correct:
    {{ m | Rep m sh N lss x /\ (extract p < N)%nat }}
      f_visit(sptr sh, vint (key p))
    {{ m', v | ConfOut sh N lss res m' v }}.
  Proof.
    intros m [[HRep [Hlower (t0 & Apool0 & Hpool0)]] Hp].
    pose proof (key_small p N Hp (r_n HRep)) as Hkp.
    pose proof (lit_key_lt p N Hp) as HP.
    eapply call_simple.
    - reflexivity.
    - reflexivity.
    - unfold f_visit. cbn [fn_body fn_return].
      pose proof (r_woff HRep) as Fwoff.
      pose proof (r_wlen HRep) as Fwlen.
      pose proof (a_woff HRep) as Awoff.
      pose proof (a_wlen HRep) as Awlen.
      assert (Hbase: Int.mul (Int.repr 2) (Int.repr (Z.of_nat (offs sh (lit_key p))))
                     = Int.repr (Z.of_nat (2 * offs sh (lit_key p)))).
      { rewrite mul_repr. f_equal. lia. }
      (* int base = 2 * s->woff[p]; int n = s->wlen[p]; int j = 0; int k = 0; *)
      run. clear Fwoff Fwlen Awoff Awlen. ints.
      apply visit_loop_correct. exists [], x, t0. splits.
      + constructor; tmp.
      + (* nothing kept yet, and the pool holds all of ws *)
        constructor; try assumption.
        * cbn [length]. lia.
        * intros k q Hk Hq _. apply Hpool0.
          -- assumption.
          -- assumption.
          -- intros [].
        * intros q Hq. cbn [length] in Hq. lia.
        * intros q Hq. apply Hpool0.
          -- assumption.
          -- unfold watching in Hq. lia.
          -- intros [].
        * exists []. rewrite app_nil_r. reflexivity.
        * intros i b [].
      + reflexivity.
  Qed.

End Visit.

Lemma visit_fun: FunAt _visit f_visit.
Proof. apply find_fun. reflexivity. Qed.
