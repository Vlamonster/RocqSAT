(* visit visits the watchers of a false literal (visit_t), or gives up.

   The loop of visit runs over the watch list ws of p. Each watcher (i, b) at position k
   is kept at once when its blocker b is true; otherwise its clause i is looked at: the
   watcher is kept with a new blocker, moved to the watch list of another literal, or
   dropped, and on a conflict keep_rest keeps the rest of ws as it is. VisitTemps and
   VisitMem (KeepRest.v) say what the temporaries and the memory hold at position k, and
   each part of the loop body has a lemma of its own. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs Ctypes
  Ctypesdefs Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Propagate CStep.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep LitValue Wpush Assign
  FindWatch KeepRest.
Import ListNotations.

(* Whether a visit found a conflict, as C returns it. *)
Definition enc_conf (r: option nat): Z :=
match r with
| Some _ => 1
| None   => 0
end.

(* Moving a watch is setting the clause, then appending to the watch list of the new
   watch. *)
Lemma move_watch_split: forall (x: Ctx) (i: nat) (ls: list Lit) (l b: Lit),
  move_watch x i ls l b =
    set_watching (set_clause x i ls) l (watching (wls (set_clause x i ls)) l ++ [(i, b)]).
Proof. reflexivity. Qed.

Section Lists.
  (* Replacing an entry of a list past its first. *)
  Lemma set_nth_cons: forall (d: nat) (y a: Lit) (ls: list Lit),
    set_nth (Datatypes.S d) y (a :: ls) = a :: set_nth d y ls.
  Proof. intros d y a ls. reflexivity. Qed.

  (* swap_watch finds the first entry d that is not false, and puts p in its place. *)
  Lemma swap_watch_at: forall (v: Values) (p: Lit) (ls: list Lit) (d: nat),
    (d < length ls)%nat -> lookup v (nth d ls (Pos 0%nat)) <> Some false ->
    (forall (d': nat), (d' < d)%nat -> lookup v (nth d' ls (Pos 0%nat)) = Some false) ->
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
        * intros d' Hd'. apply (Hbefore (Datatypes.S d')). lia.
  Qed.

  Lemma swap_watch_all_false: forall (v: Values) (p: Lit) (ls: list Lit),
    (forall (d: nat), (d < length ls)%nat ->
      lookup v (nth d ls (Pos 0%nat)) = Some false) ->
    swap_watch v p ls = None.
  Proof.
    intros v p ls. induction ls as [|y ls IH]; intros Hall; simpl.
    - reflexivity.
    - assert (Hy: lookup v y = Some false) by (apply (Hall 0%nat); simpl; lia).
      unfold not_false. rewrite Hy, IH.
      + reflexivity.
      + intros d Hd. apply (Hall (Datatypes.S d)). simpl. lia.
  Qed.
End Lists.

(* What visit returns: -1 when out of room, or what visit_t computes on the watch list
   of p, 1 on a conflict or 0, with the memory representing the context it reaches. *)
Definition VisitPost (S: Shape) (N: nat) (lss: list (list Lit)) (lims: list nat)
  (x: Ctx) (p: Lit) (m': mem) (v: val): Prop :=
  v = vint (-1) \/
  (v = vint (enc_conf (snd (visit_t p (watching (wls x) p) [] x))) /\
   Rep m' S N lss (fst (visit_t p (watching (wls x) p) [] x)) lims).

(* The invariant of the loop at position k: the watchers before k are visited, and what
   remains of visit_t is the visit of those from k on. After the body for position k,
   before k++, the same holds for k + 1 with k in the temporaries. *)
Definition visit_at (S: Shape) (N: nat) (lss: list (list Lit)) (lims: list nat) (x: Ctx)
  (p: Lit) (k kt: nat) (le: temp_env) (m: mem): Prop :=
  exists (kept: list Watcher) (xc: Ctx) (t: nat -> Z),
  VisitTemps S x p (length kept) kt le /\ VisitMem S N lss lims x p k kept xc t m /\
  visit_t p (watching (wls x) p) [] x = visit_t p (skipn k (watching (wls x) p)) kept xc.

Definition visit_inv (S: Shape) (N: nat) (lss: list (list Lit)) (lims: list nat)
  (x: Ctx) (p: Lit) (k: nat) (le: temp_env) (m: mem): Prop :=
  visit_at S N lss lims x p k k le m.

Definition visit_done (S: Shape) (N: nat) (lss: list (list Lit)) (lims: list nat)
  (x: Ctx) (p: Lit) (k: nat) (le: temp_env) (m: mem): Prop :=
  visit_at S N lss lims x p (Datatypes.S k) k le m.

Definition visit_variant (x: Ctx) (p: Lit): nat -> nat -> Prop :=
  ltof nat (fun (k: nat) => length (watching (wls x) p) - k)%nat.

(* After the clause of the watcher at position k is looked at: the context is xc, the
   temporary kb holds the blocker to keep the watcher with, or -1 to drop it, and
   visit_t goes on from k + 1. *)
Definition visit_chosen (S: Shape) (N: nat) (lss: list (list Lit)) (lims: list nat)
  (x: Ctx) (p: Lit) (k: nat) (le: temp_env) (m: mem): Prop :=
  exists (kept: list Watcher) (xc: Ctx) (t: nat -> Z) (i: nat) (ob: option Lit),
  VisitTemps S x p (length kept) k le /\ le ! _i = Some (vint (Z.of_nat i)) /\
  le ! _kb = Some (vint (enc_lit ob)) /\ VisitMem S N lss lims x p k kept xc t m /\
  (k < length (watching (wls x) p))%nat /\ (i < length lss)%nat /\
  (forall (b: Lit), ob = Some b -> (extract b < N)%nat) /\
  visit_t p (watching (wls x) p) [] x =
    visit_t p (skipn (Datatypes.S k) (watching (wls x) p))
      (match ob with Some b => (i, b) :: kept | None => kept end) xc.

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

(* What must hold after the loop body at position k: the loop goes on (visit_inv), or
   visit returns. *)
Definition VisitK (S: Shape) (N: nat) (lss: list (list Lit)) (lims: list nat) (x: Ctx)
  (p: Lit) (k: nat): temp_env -> mem -> outcome -> Prop :=
  LoopK (visit_variant x p) (visit_inv S N lss lims x p)
    (SeqK ge visit_end (Returns f_visit (VisitPost S N lss lims x p))) k.

(* The end of the loop body:

     {{ visit_done k }}  k++;  {{ visit_inv (k + 1) }}                               *)
Lemma visit_incr_correct: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (lims: list nat) (x: Ctx) (p: Lit) (k: nat) (le: temp_env) (m: mem),
  visit_done S N lss lims x p k le m ->
  Exec ge le m visit_incr (VisitK S N lss lims x p k).
Proof.
  intros S N lss lims x p k le m (kept & xc & t & HT & HM & Hvisit).
  pose proof (visit_room S N lss lims x p _ kept xc t m HM) as (Hcap & Hroom & Hsmall).
  pose proof (vm_le _ _ _ _ _ _ _ _ _ _ _ HM) as Hle.
  pose proof HT as [Hs Hp Hbase Hn Hj Hk].
  assert (Hk1: Int.add (Int.repr (Z.of_nat k)) (Int.repr 1)
               = Int.repr (Z.of_nat (Datatypes.S k))).
  { apply incr_nat. lia. }
  unfold visit_incr, visit_tail, visit_slow, visit_body, visit_loop, f_visit.
  cbn [fn_body drop_stmts first_stmt loop_body Swhile].
  run. ints. apply loopk_next with (Datatypes.S k).
  - unfold visit_variant, ltof. lia.
  - exists kept, xc, t. split.
    + constructor; tmp.
    + split.
      * assumption.
      * assumption.
Qed.

(* Keeping the watcher (i, b) at position k, with the temporaries tw1 and tw2 for
   s->wpool, and going on with rest:

     {{ VisitMem k kept xc /\ i, kb = b in the temporaries }}
       s->wpool[base + 2 * j] = i;                                       (visit_mem_keep)
       s->wpool[base + 2 * j + 1] = kb;
     {{ VisitMem (k + 1) ((i, b) :: kept) xc }}
       rest *)
Lemma visit_keep_correct: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (lims: list nat) (x: Ctx) (p: Lit) (k: nat) (kept: list Watcher) (xc: Ctx) (t: nat -> Z)
  (i: nat) (b: Lit) (tw1 tw2: ident) (rest: statement) (le: temp_env) (m: mem)
  (Q: temp_env -> mem -> outcome -> Prop),
  (tw1 = _t'26 /\ tw2 = _t'25) \/ (tw1 = _t'11 /\ tw2 = _t'10) ->
  VisitTemps S x p (length kept) k le -> le ! _i = Some (vint (Z.of_nat i)) ->
  le ! _kb = Some (vint (key b)) -> VisitMem S N lss lims x p k kept xc t m ->
  (k < length (watching (wls x) p))%nat -> (i < length lss)%nat -> (extract b < N)%nat ->
  (forall (le': temp_env) (m': mem),
     VisitTemps S x p (length kept) k le' -> le' ! _i = Some (vint (Z.of_nat i)) ->
     le' ! _kb = Some (vint (key b)) ->
     VisitMem S N lss lims x p (Datatypes.S k) ((i, b) :: kept) xc
       (set_watcher t (offs S (lit_key p) + length kept) (i, b)) m' ->
     Exec ge le' m' rest Q) ->
  Exec ge le m (keep_stmt tw1 tw2 rest) Q.
Proof.
  intros S N lss lims x p k kept xc t i b tw1 tw2 rest le m Q Htw HT Hi Hkb HM Hkn Hi_lt
    Hb Hrest.
  pose proof (visit_room S N lss lims x p k kept xc t m HM) as (Hcap & Hroom & Hsmall).
  pose proof HM as [_ Hle HRep Apool _ _ _ _ _].
  pose proof (key_small b N Hb (r_n _ _ _ _ _ _ HRep)) as Hkey.
  pose proof (r_wpool _ _ _ _ _ _ HRep) as Fwpool.
  destruct (watcher_entry (offs S (lit_key p)) (length kept) ltac:(lia)) as [Hej Hej1].
  assert (Hlt: (2 * (offs S (lit_key p) + length kept) + 1 < 2 * npool S)%nat) by lia.
  unfold keep_stmt. pose proof HT as [Hs Hpk Hbase Hn Hj Hk].
  (* tw1 and tw2 are none of the temporaries that VisitTemps describes, nor i and kb *)
  set (le1 := PTree.set tw1 (Vptr (b_wpool S) Ptrofs.zero) le).
  set (le2 := PTree.set tw2 (Vptr (b_wpool S) Ptrofs.zero) le1).
  assert (HT1: VisitTemps S x p (length kept) k le1).
  { subst le1. destruct Htw as [[-> ->] | [-> ->]]; constructor; tmp. }
  assert (Hi1: le1 ! _i = Some (vint (Z.of_nat i))).
  { subst le1. destruct Htw as [[-> ->] | [-> ->]]; tmp. }
  assert (HT2: VisitTemps S x p (length kept) k le2).
  { subst le2 le1. destruct Htw as [[-> ->] | [-> ->]]; constructor; tmp. }
  assert (Hi2: le2 ! _i = Some (vint (Z.of_nat i))).
  { subst le2 le1. destruct Htw as [[-> ->] | [-> ->]]; tmp. }
  assert (Hkb2: le2 ! _kb = Some (vint (key b))).
  { subst le2 le1. destruct Htw as [[-> ->] | [-> ->]]; tmp. }
  assert (Htw1: le1 ! tw1 = Some (Vptr (b_wpool S) Ptrofs.zero)).
  { subst le1. apply PTree.gss. }
  assert (Htw2: le2 ! tw2 = Some (Vptr (b_wpool S) Ptrofs.zero)).
  { subst le2. apply PTree.gss. }
  pose proof HT1 as [Hs1 Hpk1 Hbase1 Hn1 Hj1 Hk1].
  (* s->wpool[base + 2 * j] = i; *)
  run. fold le1. eapply exec_store.
  - evl.
  - ev.
  - reflexivity.
  - reflexivity.
  - ofs. bound.
  - ofs. cbn [cast_int_int]. ints.
    destruct (arr_storable m (b_wpool S) (2 * npool S)
                (2 * (offs S (lit_key p) + length kept)) t (Z.of_nat i) Apool ltac:(lia))
      as [m1 Hst1].
    exists m1. split.
    + apply Hst1.
    + normal.
      pose proof (arr_store _ _ _ _ (2 * (offs S (lit_key p) + length kept)) _ _ Apool
                    ltac:(lia) Hst1) as Apool1.
      pose proof (rep_store_pool m m1 S N lss xc lims _ _ HRep Hst1) as HRep1.
      pose proof (Rep.r_wpool _ _ _ _ _ _ HRep1) as Fwpool1.
      pose proof HT2 as [Hs2 Hpk2 Hbase2 Hn2 Hj2 Hk2].
      (* s->wpool[base + 2 * j + 1] = kb; *)
      run. fold le2. eapply exec_store.
      * evl.
      * ev.
      * reflexivity.
      * reflexivity.
      * ofs. bound.
      * ofs. cbn [cast_int_int]. ints.
        destruct (arr_storable m1 (b_wpool S) (2 * npool S)
                    (2 * (offs S (lit_key p) + length kept) + 1) _ (key b) Apool1 Hlt)
          as [m2 Hst2].
        exists m2. split.
        -- apply Hst2.
        -- normal. apply Hrest.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ apply (visit_mem_keep S N lss lims x p k kept xc t (i, b) m m1 m2).
              ** assumption.
              ** assumption.
              ** assumption.
              ** assumption.
              ** assumption.
              ** assumption.
Qed.

(* The tail of the loop body, after the clause of the watcher at position k:

     {{ visit_chosen k: kb is the blocker to keep it with, or -1 }}
       if (kb >= 0) { s->wpool[base + 2 * j] = i;
                      s->wpool[base + 2 * j + 1] = kb; j++; }    (visit_keep_correct)
     {{ visit_done k }}
       k++;                                                     (visit_incr_correct) *)
Lemma visit_tail_correct: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (lims: list nat) (x: Ctx) (p: Lit) (k: nat) (le: temp_env) (m: mem),
  visit_chosen S N lss lims x p k le m ->
  Exec ge le m visit_tail (VisitK S N lss lims x p k).
Proof.
  intros S N lss lims x p k le m
    (kept & xc & t & i & ob & HT & Hi & Hkb & HM & Hkn & Hi_lt & Hob & Hvisit).
  pose proof (visit_room S N lss lims x p k kept xc t m HM) as (Hcap & Hroom & Hsmall).
  pose proof (vm_le _ _ _ _ _ _ _ _ _ _ _ HM) as Hle.
  pose proof HM as [_ _ HRep _ _ _ _ _ _].
  change visit_tail with (Ssequence visit_keep visit_incr). apply exec_seq.
  unfold visit_keep, visit_tail, visit_slow, visit_body, visit_loop, f_visit.
  cbn [fn_body drop_stmts first_stmt loop_body Swhile].
  destruct ob as [b|].
  - (* keep the watcher with blocker b *)
    pose proof (Hob b eq_refl) as Hb.
    pose proof (key_small b N Hb (r_n _ _ _ _ _ _ HRep)) as Hkey.
    eapply (exec_if_cmp _ _ _ Cge _ _ (key b) 0).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + unfold Small. lia.
    + unfold Small. lia.
    + replace (zcmp Cge (key b) 0) with true by
        (symmetry; cbn [zcmp]; apply Z.leb_le; lia).
      cbv beta iota.
      apply (visit_keep_correct S N lss lims x p k kept xc t i b _t'11 _t'10).
      * right. split.
        -- reflexivity.
        -- reflexivity.
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * intros le' m' HT' Hi' Hkb' HM'. pose proof HT' as [Hs Hpk Hbase Hn Hj Hk].
        assert (Hj_incr: Int.add (Int.repr (Z.of_nat (length kept))) (Int.repr 1)
                         = Int.repr (Z.of_nat (length ((i, b) :: kept)))).
        { apply incr_nat. lia. }
        (* j++; *)
        run. ints. apply visit_incr_correct.
        exists ((i, b) :: kept), xc. eexists. split.
        -- constructor; tmp.
        -- split.
           ++ apply HM'.
           ++ assumption.
  - (* drop the watcher: kb = -1 *)
    eapply (exec_if_cmp _ _ _ Cge _ _ (-1) 0).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + unfold Small. lia.
    + unfold Small. lia.
    + change (zcmp Cge (-1) 0) with false. cbv beta iota. apply exec_skip. normal.
      apply visit_incr_correct. exists kept, xc, t. split.
      * assumption.
      * split.
        -- apply (visit_mem_next S N lss lims x p k kept xc t m).
           ++ assumption.
           ++ assumption.
        -- assumption.
Qed.

(* The state of the loop body at the watcher (i, b) at position k, past its blocker, at
   its clause i in the context xc: the temporaries hold i, kb = -1 and the range b .. e
   of the clause, and the memory represents xc. *)
Record ClauseAt (S: Shape) (N: nat) (lss: list (list Lit)) (lims: list nat) (x: Ctx)
  (p: Lit) (k: nat) (kept: list Watcher) (xc: Ctx) (t: nat -> Z) (i: nat)
  (le: temp_env) (m: mem): Prop := {
  ca_temps: VisitTemps S x p (length kept) k le;
  ca_i: le ! _i = Some (vint (Z.of_nat i));
  ca_kb: le ! _kb = Some (vint (-1));
  ca_b: le ! _b = Some (vint (Z.of_nat (starts S i)));
  ca_e: le ! _e = Some (vint (Z.of_nat (starts S (Datatypes.S i))));
  ca_mem: VisitMem S N lss lims x p k kept xc t m;
  ca_k: (k < length (watching (wls x) p))%nat;
  ca_cls: (i < length lss)%nat
}.

(* What visit_t does with the watcher of clause i at position k of ws once the clause is
   o :: p :: ls in x1: keep it with blocker o if o is true, move the watch from p to a
   literal of ls that is not false, propagate o, or stop at a conflict. *)
Definition visit_rest (p: Lit) (ws: list Watcher) (k: nat) (kept: list Watcher) (x1: Ctx)
  (i: nat) (o: Lit) (ls: list Lit): Ctx * option nat :=
  if lookup_true (vals x1) o then visit_t p (skipn (Datatypes.S k) ws) ((i, o) :: kept) x1
  else
  match swap_watch (vals x1) p ls with
  | Some (r, ls') => visit_t p (skipn (Datatypes.S k) ws) kept
    (move_watch x1 i (o :: r :: ls') r o)
  | None          =>
    if lookup_undef (vals x1) o
    then visit_t p (skipn (Datatypes.S k) ws) ((i, o) :: kept)
      (assign x1 o (Datatypes.S i))
    else (set_watching x1 p (rev_append kept (skipn k ws)), Some i)
  end.

(* The other watch o of the clause o :: p :: ls has no literal of ls to take the place of
   p:

     {{ ClauseAt k kept x1 /\ o in the temporaries }}
       if (lit_value(s, o) == 0) {                                (lit_value_correct)
         if (!assign(s, o)) return -1;                               (assign_correct)
     {{ result = -1 (out of room) }}
         kb = o;
     {{ visit_chosen k with assign x1 o (i + 1), kb = o }}
       } else return keep_rest(s, p, j, k, n);                    (keep_rest_correct)
     {{ result = 1 /\ VisitPost }}                                                   *)
Lemma visit_unit_correct: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (lims: list nat) (x: Ctx) (p: Lit) (k: nat) (kept: list Watcher) (x1: Ctx) (t: nat -> Z)
  (i: nat) (o: Lit) (le: temp_env) (m: mem),
  ClauseAt S N lss lims x p k kept x1 t i le m -> le ! _o = Some (vint (key o)) ->
  (extract o < N)%nat ->
  visit_t p (watching (wls x) p) [] x =
    (if lookup_undef (vals x1) o
     then visit_t p (skipn (Datatypes.S k) (watching (wls x) p)) ((i, o) :: kept)
            (assign x1 o (Datatypes.S i))
     else (set_watching x1 p (rev_append kept (skipn k (watching (wls x) p))), Some i)) ->
  Exec ge le m visit_unit (SeqK ge visit_tail (VisitK S N lss lims x p k)).
Proof.
  intros S N lss lims x p k kept x1 t i o le m [HT Hi Hkb Hb He HM Hkn Hi_lt] Ho Ho_lt
    Hvisit.
  pose proof HM as [_ _ HRep Apool _ _ _ _ _].
  pose proof (key_small o N Ho_lt (r_n _ _ _ _ _ _ HRep)) as Hko.
  pose proof HT as [Hs Hpk Hbase Hn Hj Hk].
  unfold visit_unit, visit_search, visit_test, visit_watch, visit_len, visit_slow,
    visit_body, visit_loop, f_visit.
  cbn [fn_body drop_stmts first_stmt loop_body then_stmt else_stmt Swhile].
  (* if (lit_value(s, o) == 0) *)
  run. call lit_value_fun. eapply call_weaken.
  - apply (lit_value_correct S N lss x1 lims o m). split.
    + assumption.
    + assumption.
  - intros m' v [-> ->]. normal. eapply (exec_if_cmp _ _ _ Ceq _ _ _ 0).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + apply enc_small.
    + unfold Small. lia.
    + cbn [zcmp]. rewrite enc_undef. destruct (lookup_undef (vals x1) o) eqn:Hundef.
      * (* o is unassigned: if (!assign(s, o)) return -1; *)
        cbv beta iota. run. call assign_fun. eapply call_weaken.
        -- apply (assign_correct S N lss x1 lims o (Datatypes.S i) t m). split.
           ++ assumption.
           ++ split.
              ** assumption.
              ** assumption.
        -- intros m1 v Hv. normal. destruct Hv as [-> | (-> & HRep1 & Apool1)].
           ++ (* out of room *)
              eapply (exec_if_int _ _ _ _ 1).
              ** ev.
              ** reflexivity.
              ** unfold Small. lia.
              ** change (negb (Z.eqb 1 0)) with true. cbv beta iota. eapply exec_return.
                 --- ev.
                 --- ret. exists (vint (-1)). split.
                     +++ apply result_int.
                     +++ left. reflexivity.
           ++ (* kb = o: keep the watcher with blocker o *)
              eapply (exec_if_int _ _ _ _ 0).
              ** ev.
              ** reflexivity.
              ** unfold Small. lia.
              ** change (negb (Z.eqb 0 0)) with false. cbv beta iota. apply exec_skip.
                 normal. run. apply visit_tail_correct.
                 exists kept, (assign x1 o (Datatypes.S i)), t, i, (Some o). split.
                 --- constructor; tmp.
                 --- split.
                     +++ tmp.
                     +++ split.
                         *** tmp.
                         *** split.
                             ---- apply (visit_mem_ctx S N lss lims x p k kept x1 _ t m
                                    m1).
                                  ++++ assumption.
                                  ++++ assumption.
                                  ++++ assumption.
                                  ++++ reflexivity.
                             ---- split.
                                  ++++ assumption.
                                  ++++ split.
                                       **** assumption.
                                       **** split.
                                            ----- intros b' Heq. injection Heq as <-.
                                                  assumption.
                                            ----- assumption.
      * (* o is false: a conflict, return keep_rest(s, p, j, k, n); *)
        cbv beta iota. run. call keep_rest_fun. eapply call_weaken.
        -- apply (keep_rest_correct S N lss lims x p k kept x1 t m). assumption.
        -- intros m' v [-> HRep']. normal. eapply exec_return.
           ++ ev.
           ++ ret. exists (vint 1). split.
              ** apply result_int.
              ** right. rewrite Hvisit. cbn [fst snd enc_conf]. split.
                 --- reflexivity.
                 --- assumption.
Qed.

(* The new clause after the watch moves from p, second, to r, at position d >= 2. *)
Lemma set_nth_move: forall (d: nat) (o r p: Lit) (ls: list Lit), (2 <= d)%nat ->
  set_nth d p (o :: r :: ls) = o :: r :: set_nth (d - 2) p ls.
Proof.
  intros [|[|d]] o r p ls Hd.
  - lia.
  - lia.
  - rewrite !set_nth_cons. replace (Datatypes.S (Datatypes.S d) - 2)%nat with d by lia.
    reflexivity.
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
Lemma visit_move_correct: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (lims: list nat) (x: Ctx) (p: Lit) (k: nat) (kept: list Watcher) (x1: Ctx) (t: nat -> Z)
  (i: nat) (o: Lit) (ls: list Lit) (d: nat) (le: temp_env) (m: mem),
  ClauseAt S N lss lims x p k kept x1 t i le m -> le ! _o = Some (vint (key o)) ->
  le ! _q = Some (vint (Z.of_nat (starts S i + d))) ->
  tget (cmap x1) i = Some (o :: p :: ls) -> (2 <= d < length (o :: p :: ls))%nat ->
  (extract o < N)%nat ->
  visit_t p (watching (wls x) p) [] x =
    visit_t p (skipn (Datatypes.S k) (watching (wls x) p)) kept
      (move_watch x1 i (o :: nth (d - 2) ls (Pos 0%nat) :: set_nth (d - 2) p ls)
         (nth (d - 2) ls (Pos 0%nat)) o) ->
  Exec ge le m visit_move (SeqK ge visit_tail (VisitK S N lss lims x p k)).
Proof.
  intros S N lss lims x p k kept x1 t i o ls d le m [HT Hi Hkb Hb He HM Hkn Hi_lt] Ho Hq
    Hcls Hd Ho_lt Hvisit.
  pose proof HM as [Hp _ HRep Apool Hpool _ _ [extra Hext] _].
  pose proof (r_n _ _ _ _ _ _ HRep) as HN.
  pose proof (r_nodup _ _ _ _ _ _ HRep) as Hnd.
  pose proof (key_small p N Hp HN) as Hkp.
  pose proof (key_small o N Ho_lt HN) as Hko.
  pose proof (r_clits _ _ _ _ _ _ HRep) as Fclits.
  pose proof (r_nclits_small _ _ _ _ _ _ HRep) as Hnclits.
  pose proof (a_lits _ _ _ _ _ _ HRep) as (tl & Alits & Hclauses).
  destruct (r_starts _ _ _ _ _ _ HRep i Hi_lt) as [Hsi Hsn].
  (* r, literal d of the clause, is literal d - 2 of ls *)
  set (r := nth (d - 2) ls (Pos 0%nat)) in *.
  assert (Hr_nth: nth d (o :: p :: ls) (Pos 0%nat) = r).
  { subst r. destruct d as [|[|d']].
    - lia.
    - lia.
    - cbn [nth]. replace (Datatypes.S (Datatypes.S d') - 2)%nat with d' by lia.
      reflexivity. }
  destruct (clause_lit m S N lss x1 lims tl i d (o :: p :: ls) HRep Hclauses Hi_lt Hcls)
    as (Hpos & Htl & Hr_lt).
  { lia. }
  rewrite Hr_nth in Htl, Hr_lt.
  pose proof (key_small r N Hr_lt HN) as Hkr.
  pose proof HT as [Hs Hpk Hbase Hn Hj Hk].
  assert (Hb1: Int.add (Int.repr (Z.of_nat (starts S i))) (Int.repr 1)
               = Int.repr (Z.of_nat (starts S i + 1))).
  { rewrite add_repr. f_equal. lia. }
  unfold visit_move, visit_search, visit_test, visit_watch, visit_len, visit_slow,
    visit_body, visit_loop, f_visit.
  cbn [fn_body drop_stmts first_stmt loop_body then_stmt else_stmt Swhile].
  (* int r = s->clits[q]; s->clits[b + 1] = r; *)
  run. rewrite Htl. eapply exec_store.
  - evl.
  - ev.
  - reflexivity.
  - reflexivity.
  - ofs. bound.
  - ofs. cbn [cast_int_int].
    destruct (arr_storable m (b_clits S) (nclits S) (starts S i + 1) tl (key r) Alits
                ltac:(lia)) as [m1 Hst1].
    exists m1. split.
    + apply Hst1.
    + normal.
      pose proof
        (rep_store_clits m m1 S N lss x1 lims i 1 (o :: p :: ls) r HRep Hi_lt Hcls
                    ltac:(cbn [length]; lia) Hr_lt Hst1) as HRep1.
      cbn [set_nth firstn skipn app] in HRep1.
      pose proof (arr_store_other _ _ _ _ _ _ _ _ _ Apool Hst1 ltac:(neq Hnd)) as Apool1.
      pose proof (Rep.r_clits _ _ _ _ _ _ HRep1) as Fclits1.
      pose proof (Rep.a_lits _ _ _ _ _ _ HRep1) as (tl1 & Alits1 & _).
      keep_mem m1.
      (* s->clits[q] = p; *)
      run. eapply exec_store.
      * evl.
      * ev.
      * reflexivity.
      * reflexivity.
      * ofs. bound.
      * ofs. cbn [cast_int_int].
        destruct (arr_storable m1 (b_clits S) (nclits S) (starts S i + d) tl1
          (key p) Alits1
                    ltac:(lia)) as [m2 Hst2].
        exists m2. split.
        -- apply Hst2.
        -- normal.
           pose proof
             (rep_store_clits m1 m2 S N lss (set_clause x1 i (o :: r :: ls)) lims i
                         d (o :: r :: ls) p HRep1 Hi_lt (tget_tset_same _ _ _)
                         ltac:(cbn [length] in *; lia) Hp Hst2) as HRep2.
           apply rep_clause_twice in HRep2. rewrite set_nth_move in HRep2 by lia.
           set (x2 := set_clause x1 i (o :: r :: set_nth (d - 2) p ls)) in *.
           pose proof
             (arr_store_other _ _ _ _ _ _ _ _ _ Apool1 Hst2 ltac:(neq Hnd)) as Apool2.
           assert (HM2: VisitMem S N lss lims x p k kept x2 t m2).
           { apply (visit_mem_ctx S N lss lims x p k kept x1 x2 t m m2).
             - assumption.
             - assumption.
             - assumption.
             - reflexivity. }
           keep_mem m2.
           (* if (!wpush(s, r, i, o)) return -1; *)
           run. call wpush_fun. eapply call_weaken.
           ++ apply (wpush_correct S N lss x2 lims r i o t
                       (SkipP (lit_key p) (length (watching (wls x) p))) m2).
              split.
              ** assumption.
              ** split.
                 --- assumption.
                 --- split.
                     +++ apply HM2.
                     +++ split.
                         *** (* the skipped watchers are within ws, which the list of p
                                starts with *)
                             intros q' [Heq Hq']. unfold watching.
                             cbn [set_clause wls x2].
                             rewrite Heq. fold (watching (wls x1) p).
                             rewrite Hext, length_app.
                             lia.
                         *** split.
                             ---- assumption.
                             ---- split.
                                  ++++ assumption.
                                  ++++ assumption.
           ++ intros m3 v Hv. normal.
              destruct Hv as [-> | (-> & HRep3 & Apool3 & Hpool3 & _)].
              ** (* out of room *)
                 eapply (exec_if_int _ _ _ _ 1).
                 --- ev.
                 --- reflexivity.
                 --- unfold Small. lia.
                 --- change (negb (Z.eqb 1 0)) with true. cbv beta iota.
                     eapply exec_return.
                     +++ ev.
                     +++ ret. exists (vint (-1)). split.
                         *** apply result_int.
                         *** left. reflexivity.
              ** (* the watch moved: drop the watcher, kb = -1 *)
                 eapply (exec_if_int _ _ _ _ 0).
                 --- ev.
                 --- reflexivity.
                 --- unfold Small. lia.
                 --- change (negb (Z.eqb 0 0)) with false. cbv beta iota. apply exec_skip.
                     normal. apply visit_tail_correct.
                     exists kept, (move_watch x1 i (o :: r :: set_nth (d - 2) p ls) r o).
                     eexists. exists i, None. split.
                     +++ constructor; tmp.
                     +++ split.
                         *** tmp.
                         *** split.
                             ---- tmp.
                             ---- split.
                                  ++++ rewrite move_watch_split.
                                       apply (visit_mem_push S N lss lims x p k kept x2 t
                                         i r o
                                                m2 m3).
                                       **** assumption.
                                       **** assumption.
                                       **** assumption.
                                       **** assumption.
                                       **** assumption.
                                  ++++ split.
                                       **** assumption.
                                       **** split.
                                            ----- assumption.
                                            ----- split.
                                                  +++++ intros b' Heq. discriminate.
                                                  +++++ assumption.
Qed.

(* The other watch o of the clause o :: p :: ls is not true: search ls for a new watch.

     {{ ClauseAt k kept x1 /\ o in the temporaries /\ o is not true }}
       int q = find_watch(s, b + 2, e);                             (find_watch_correct)
       if (q >= 0) ...                                              (visit_move_correct)
       else ...                                                    (visit_unit_correct) *)
Lemma visit_search_correct: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (lims: list nat) (x: Ctx) (p: Lit) (k: nat) (kept: list Watcher) (x1: Ctx) (t: nat -> Z)
  (i: nat) (o: Lit) (ls: list Lit) (le: temp_env) (m: mem),
  ClauseAt S N lss lims x p k kept x1 t i le m -> le ! _o = Some (vint (key o)) ->
  tget (cmap x1) i = Some (o :: p :: ls) -> (extract o < N)%nat ->
  lookup_true (vals x1) o = false ->
  visit_t p (watching (wls x) p) [] x = visit_rest p
    (watching (wls x) p) k kept x1 i o ls ->
  Exec ge le m visit_search (SeqK ge visit_tail (VisitK S N lss lims x p k)).
Proof.
  intros S N lss lims x p k kept x1 t i o ls le m HC Ho Hcls Ho_lt Hnt Hvisit.
  pose proof HC as [HT Hi Hkb Hb He HM Hkn Hi_lt].
  pose proof HM as [_ _ HRep _ _ _ _ _ _].
  pose proof (r_nclits_small _ _ _ _ _ _ HRep) as Hnclits.
  destruct (r_starts _ _ _ _ _ _ HRep i Hi_lt) as [Hsi Hsn].
  pose proof (a_lits _ _ _ _ _ _ HRep) as (tl & _ & Hclauses).
  pose proof
    (clause_length m S N lss x1 lims tl i (o :: p :: ls) Hclauses Hi_lt Hcls) as Hlen.
  pose proof HT as [Hs Hpk Hbase Hn Hj Hk].
  unfold visit_rest in Hvisit. rewrite Hnt in Hvisit.
  assert (Hb2: Int.add (Int.repr (Z.of_nat (starts S i))) (Int.repr 2)
               = Int.repr (Z.of_nat (starts S i + 2))).
  { rewrite add_repr. f_equal. lia. }
  unfold visit_search, visit_test, visit_watch, visit_len, visit_slow, visit_body,
    visit_loop, f_visit.
  cbn [fn_body drop_stmts first_stmt loop_body then_stmt else_stmt Swhile].
  (* int q = find_watch(s, b + 2, e); *)
  apply exec_seq. run. call find_watch_fun. cbn [cast_int_int]. ints. eapply call_weaken.
  - apply (find_watch_correct S N lss x1 lims i 2 (o :: p :: ls) m). split.
    + assumption.
    + split.
      * assumption.
      * split.
        -- assumption.
        -- cbn [length]. lia.
  - intros m' v [-> Hfound]. normal. run.
    destruct Hfound as [[-> Hall] | (d & Hd & -> & Hnf & Hbefore)].
    + (* no literal of ls is not false: q = -1 *)
      assert (Hnone: swap_watch (vals x1) p ls = None).
      { apply swap_watch_all_false. intros d Hd.
        apply (Hall (Datatypes.S (Datatypes.S d))). cbn [length]. lia. }
      rewrite Hnone in Hvisit.
      eapply (exec_if_cmp _ _ _ Cge _ _ (-1) 0).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * change (zcmp Cge (-1) 0) with false. cbv beta iota.
        apply (visit_unit_correct S N lss lims x p k kept x1 t i o).
        -- constructor; try tmp.
           ++ constructor; tmp.
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
            replace (Datatypes.S (Datatypes.S d') - 2)%nat with d' by lia.
            assumption.
        - intros d' Hd'. apply (Hbefore (Datatypes.S (Datatypes.S d'))). lia. }
      rewrite Hsome in Hvisit.
      eapply (exec_if_cmp _ _ _ Cge _ _ (Z.of_nat (starts S i + d)) 0).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * replace (zcmp Cge (Z.of_nat (starts S i + d)) 0) with true
          by (symmetry; cbn [zcmp]; apply Z.leb_le; lia).
        cbv beta iota.
        apply (visit_move_correct S N lss lims x p k kept x1 t i o ls d).
        -- constructor; try tmp.
           ++ constructor; tmp.
           ++ assumption.
           ++ assumption.
           ++ assumption.
        -- tmp.
        -- tmp.
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
Qed.

(* The clause of the watcher at position k is o :: p :: ls in x1:

     {{ ClauseAt k kept x1 /\ o in the temporaries }}
       if (lit_value(s, o) == 1) kb = o;                             (lit_value_correct)
     {{ visit_chosen k with kb = o }}
       else ...                                                  (visit_search_correct) *)
Lemma visit_test_correct: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (lims: list nat) (x: Ctx) (p: Lit) (k: nat) (kept: list Watcher) (x1: Ctx) (t: nat -> Z)
  (i: nat) (o: Lit) (ls: list Lit) (le: temp_env) (m: mem),
  ClauseAt S N lss lims x p k kept x1 t i le m -> le ! _o = Some (vint (key o)) ->
  tget (cmap x1) i = Some (o :: p :: ls) -> (extract o < N)%nat ->
  visit_t p (watching (wls x) p) [] x = visit_rest p
    (watching (wls x) p) k kept x1 i o ls ->
  Exec ge le m visit_test (SeqK ge visit_tail (VisitK S N lss lims x p k)).
Proof.
  intros S N lss lims x p k kept x1 t i o ls le m HC Ho Hcls Ho_lt Hvisit.
  pose proof HC as [HT Hi Hkb Hb He HM Hkn Hi_lt].
  pose proof HM as [_ _ HRep _ _ _ _ _ _].
  pose proof (key_small o N Ho_lt (r_n _ _ _ _ _ _ HRep)) as Hko.
  pose proof HT as [Hs Hpk Hbase Hn Hj Hk].
  unfold visit_test, visit_watch, visit_len, visit_slow, visit_body, visit_loop, f_visit.
  cbn [fn_body drop_stmts first_stmt loop_body then_stmt else_stmt Swhile].
  (* if (lit_value(s, o) == 1) *)
  run. call lit_value_fun. eapply call_weaken.
  - apply (lit_value_correct S N lss x1 lims o m). split.
    + assumption.
    + assumption.
  - intros m' v [-> ->]. normal. eapply (exec_if_cmp _ _ _ Ceq _ _ _ 1).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + apply enc_small.
    + unfold Small. lia.
    + cbn [zcmp]. rewrite enc_true. destruct (lookup_true (vals x1) o) eqn:Htrue.
      * (* o is true: kb = o, keep the watcher with blocker o *)
        cbv beta iota. run. apply visit_tail_correct.
        exists kept, x1, t, i, (Some o). split.
        -- constructor; tmp.
        -- split.
           ++ tmp.
           ++ split.
              ** tmp.
              ** split.
                 --- assumption.
                 --- split.
                     +++ assumption.
                     +++ split.
                         *** assumption.
                         *** split.
                             ---- intros b' Heq. injection Heq as <-. assumption.
                             ---- unfold visit_rest in Hvisit. rewrite Htrue in Hvisit.
                                  assumption.
      * (* look for a new watch *)
        cbv beta iota. apply (visit_search_correct S N lss lims x p k kept x1 t i o ls).
        -- constructor; try tmp.
           ++ constructor; tmp.
           ++ assumption.
           ++ assumption.
           ++ assumption.
        -- tmp.
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
Qed.

(* The clause c0 :: c1 :: ls of the watcher at position k, with two literals or more:

     {{ ClauseAt k kept xc }}
       int o = s->clits[b];
       if (o == p) { o = s->clits[b + 1];
                     s->clits[b] = o; s->clits[b + 1] = p; }         (rep_store_clits)
       if (s->clits[b + 1] == p) ...                                (visit_test_correct)
     {{ visit_chosen k, dropped: the clause does not watch p }}

   When the clause watches p, it is o :: p :: ls in memory, o its other watch (when c1 is
   p, the clause is already in that form: rep_clause_same). *)
Lemma visit_watch_correct: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (lims: list nat) (x: Ctx) (p: Lit) (k: nat) (kept: list Watcher) (xc: Ctx) (t: nat -> Z)
  (i: nat) (c0 c1: Lit) (ls: list Lit) (le: temp_env) (m: mem),
  ClauseAt S N lss lims x p k kept xc t i le m ->
    tget (cmap xc) i = Some (c0 :: c1 :: ls) ->
  visit_t p (watching (wls x) p) [] x =
    (if (c0 =? p) || (c1 =? p)
     then visit_rest p (watching (wls x) p) k kept
            (set_clause xc i ((if c0 =? p then c1 else c0) :: p :: ls)) i
            (if c0 =? p then c1 else c0) ls
     else visit_t p (skipn (Datatypes.S k) (watching (wls x) p)) kept xc) ->
  Exec ge le m visit_watch (SeqK ge visit_tail (VisitK S N lss lims x p k)).
Proof.
  intros S N lss lims x p k kept xc t i c0 c1 ls le m HC Hcls Hvisit.
  pose proof HC as [HT Hi Hkb Hb He HM Hkn Hi_lt].
  pose proof HM as [Hp _ HRep Apool _ _ _ _ _].
  pose proof (r_n _ _ _ _ _ _ HRep) as HN.
  pose proof (r_nodup _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_nclits_small _ _ _ _ _ _ HRep) as Hnclits.
  pose proof (key_small p N Hp HN) as Hkp.
  pose proof (r_clits _ _ _ _ _ _ HRep) as Fclits.
  pose proof (a_lits _ _ _ _ _ _ HRep) as (tl & Alits & Hclauses).
  (* The first two literals of the clause, at b and b + 1 *)
  destruct (clause_lit m S N lss xc lims tl i 0 (c0 :: c1 :: ls) HRep Hclauses Hi_lt Hcls)
    as (Hpos0 & Htl0 & Hc0).
  { cbn [length]. lia. }
  destruct (clause_lit m S N lss xc lims tl i 1 (c0 :: c1 :: ls) HRep Hclauses Hi_lt Hcls)
    as (Hpos1 & Htl1 & Hc1).
  { cbn [length]. lia. }
  cbn [nth] in Htl0, Hc0, Htl1, Hc1. rewrite Nat.add_0_r in Htl0, Hpos0.
  pose proof (key_small c0 N Hc0 HN) as Hkc0.
  pose proof (key_small c1 N Hc1 HN) as Hkc1.
  pose proof HT as [Hs Hpk Hbase Hn Hj Hk].
  assert (Hb1: Int.add (Int.repr (Z.of_nat (starts S i))) (Int.repr 1)
               = Int.repr (Z.of_nat (starts S i + 1))).
  { rewrite add_repr. f_equal. lia. }
  unfold visit_watch, visit_len, visit_slow, visit_body, visit_loop, f_visit.
  cbn [fn_body drop_stmts first_stmt loop_body then_stmt else_stmt Swhile].
  (* int o = s->clits[b]; if (o == p) *)
  run. rewrite Htl0. eapply (exec_if_cmp _ _ _ Ceq).
  - ev.
  - ev.
  - reflexivity.
  - reflexivity.
  - unfold Small. lia.
  - unfold Small. lia.
  - cbn [zcmp]. rewrite key_eqb. destruct (c0 =? p) eqn:Hc0p.
    + (* p is first: o = s->clits[b + 1]; s->clits[b] = o; s->clits[b + 1] = p; *)
      apply Lit.eqb_eq in Hc0p as Hc0p'. subst c0.
      cbv beta iota. run. rewrite Htl1. eapply exec_store.
      * evl.
      * ev.
      * reflexivity.
      * reflexivity.
      * ofs. bound.
      * ofs. cbn [cast_int_int].
        destruct (arr_storable m (b_clits S) (nclits S) (starts S i) tl
          (key c1) Alits Hpos0)
          as [m1 Hst1].
        exists m1. split.
        -- apply Hst1.
        -- normal.
           rewrite <- (Nat.add_0_r (starts S i)) in Hst1.
           pose proof
             (rep_store_clits m m1 S N lss xc lims i 0 (p :: c1 :: ls) c1 HRep Hi_lt
                         Hcls ltac:(cbn [length]; lia) Hc1 Hst1) as HRep1.
           cbn [set_nth firstn skipn app] in HRep1.
           pose proof
             (arr_store_other _ _ _ _ _ _ _ _ _ Apool Hst1 ltac:(neq Hnd)) as Apool1.
           pose proof (Rep.r_clits _ _ _ _ _ _ HRep1) as Fclits1.
           pose proof (Rep.a_lits _ _ _ _ _ _ HRep1) as (tl1 & Alits1 & _).
           keep_mem m1.
           run. eapply exec_store.
           ++ evl.
           ++ ev.
           ++ reflexivity.
           ++ reflexivity.
           ++ ofs. bound.
           ++ ofs. cbn [cast_int_int].
              destruct (arr_storable m1 (b_clits S) (nclits S) (starts S i + 1) tl1
                (key p)
                          Alits1 Hpos1) as [m2 Hst2].
              exists m2. split.
              ** apply Hst2.
              ** normal.
                 pose proof
                   (rep_store_clits m1 m2 S N lss (set_clause xc i (c1 :: c1 :: ls))
                               lims i 1 (c1 :: c1 :: ls) p HRep1 Hi_lt
                                 (tget_tset_same _ _ _)
                               ltac:(cbn [length]; lia) Hp Hst2) as HRep2.
                 apply rep_clause_twice in HRep2. cbn [set_nth firstn skipn app] in HRep2.
                 set (x1 := set_clause xc i (c1 :: p :: ls)) in *.
                 pose proof (arr_store_other _ _ _ _ _ _ _ _ _ Apool1 Hst2 ltac:(neq Hnd))
                   as Apool2.
                 assert (HM2: VisitMem S N lss lims x p k kept x1 t m2).
                 { apply (visit_mem_ctx S N lss lims x p k kept xc x1 t m m2).
                   - assumption.
                   - assumption.
                   - assumption.
                   - reflexivity. }
                 assert (Hcls2: tget (cmap x1) i = Some (c1 :: p :: ls)) by apply
                   tget_tset_same.
                 pose proof (Rep.r_clits _ _ _ _ _ _ HRep2) as Fclits2.
                 pose proof (Rep.a_lits _ _ _ _ _ _ HRep2) as (tl2 & Alits2 & Hclauses2).
                 destruct (clause_lit m2 S N lss x1 lims tl2 i 1
                   (c1 :: p :: ls) HRep2 Hclauses2
                             Hi_lt Hcls2) as (_ & Htl2 & _).
                 { cbn [length]. lia. }
                 cbn [nth] in Htl2. keep_mem m2.
                 (* if (s->clits[b + 1] == p): it is *)
                 run. rewrite Htl2. eapply (exec_if_cmp _ _ _ Ceq).
                 --- ev.
                 --- ev.
                 --- reflexivity.
                 --- reflexivity.
                 --- unfold Small. lia.
                 --- unfold Small. lia.
                 --- cbn [zcmp]. rewrite Z.eqb_refl. cbv beta iota.
                     cbn [orb] in Hvisit.
                     apply (visit_test_correct S N lss lims x p k kept x1 t i c1 ls).
                     +++ constructor; try tmp.
                         *** constructor; tmp.
                         *** assumption.
                         *** assumption.
                         *** assumption.
                     +++ tmp.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
    + (* p is not first *)
      cbv beta iota. apply exec_skip. normal.
      run. rewrite Htl1. eapply (exec_if_cmp _ _ _ Ceq).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * cbn [zcmp]. rewrite key_eqb. destruct (c1 =? p) eqn:Hc1p.
        -- (* p is second: the clause is c0 :: p :: ls already *)
           apply Lit.eqb_eq in Hc1p as Hc1p'. subst c1.
           cbv beta iota. cbn [orb] in Hvisit.
           apply (visit_test_correct S N lss lims x p k kept
             (set_clause xc i (c0 :: p :: ls))
                    t i c0 ls).
           ++ constructor; try tmp.
              ** constructor; tmp.
              ** apply (visit_mem_ctx S N lss lims x p k kept xc _ t m m).
                 --- assumption.
                 --- apply rep_clause_same.
                     +++ assumption.
                     +++ assumption.
                 --- assumption.
                 --- reflexivity.
              ** assumption.
              ** assumption.
           ++ tmp.
           ++ apply tget_tset_same.
           ++ assumption.
           ++ assumption.
        -- (* the clause does not watch p: drop the watcher, kb = -1 *)
           cbv beta iota. apply exec_skip. normal. apply visit_tail_correct.
           exists kept, xc, t, i, None. split.
           ++ constructor; tmp.
           ++ split.
              ** tmp.
              ** split.
                 --- tmp.
                 --- split.
                     +++ assumption.
                     +++ split.
                         *** assumption.
                         *** split.
                             ---- assumption.
                             ---- split.
                                  ++++ intros b' Heq. discriminate.
                                  ++++ rewrite Hvisit. reflexivity.
Qed.

(* The length e - b of a clause, as C computes it from its range. *)
Lemma eval_clause_len: forall (le: temp_env) (m: mem) (b e: nat),
  le ! _b = Some (vint (Z.of_nat b)) -> le ! _e = Some (vint (Z.of_nat e)) ->
    (b <= e)%nat ->
  eval_expr ge empty_env le m (Ebinop Osub (Etempvar _e tint) (Etempvar _b tint) tint)
    (vint (Z.of_nat (e - b))).
Proof.
  intros le m b e Hb He Hbe. eapply eval_Ebinop.
  - apply eval_Etempvar. apply He.
  - apply eval_Etempvar. apply Hb.
  - unfold vint. cbn. unfold sem_binarith, sem_cast, tint. cbn. cbv [Archi.ptr64]. cbn.
    rewrite sub_repr. do 3 f_equal. lia.
Qed.

(* The watcher (i, b) at position k, whose blocker is not true: its clause by its
   length.

     {{ visit_inv k /\ ws[k] = (i, b) /\ b is not true }}
       kb = -1; int b = s->cstart[i]; int e = s->cstart[i + 1];
     {{ ClauseAt k kept xc }}
       if (e - b == 1) {
         if (s->clits[b] == p) return keep_rest(s, p, j, k, n);   (keep_rest_correct)
     {{ result = 1 /\ VisitPost: the unit clause [p] is false }}
       } else if (e - b >= 2) ...                                (visit_watch_correct)
     {{ visit_chosen k, dropped: a short clause that does not watch p }}
       if (kb >= 0) ...; k++;                                    (visit_tail_correct) *)
Lemma visit_slow_correct: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (lims: list nat) (x: Ctx) (p: Lit) (k: nat) (kept: list Watcher) (xc: Ctx) (t: nat -> Z)
  (i: nat) (b: Lit) (le: temp_env) (m: mem),
  VisitTemps S x p (length kept) k le -> le ! _i = Some (vint (Z.of_nat i)) ->
  VisitMem S N lss lims x p k kept xc t m -> (k < length (watching (wls x) p))%nat ->
  nth k (watching (wls x) p) (0%nat, Pos 0%nat) = (i, b) ->
  lookup_true (vals xc) b = false -> (i < length lss)%nat ->
  visit_t p (watching (wls x) p) [] x = visit_t p
    (skipn k (watching (wls x) p)) kept xc ->
  Exec ge le m visit_slow (VisitK S N lss lims x p k).
Proof.
  intros S N lss lims x p k kept xc t i b le m HT Hi HM Hkn Hnth Hnt Hi_lt Hvisit.
  pose proof HM as [Hp _ HRep _ _ _ _ _ _].
  pose proof (r_n _ _ _ _ _ _ HRep) as HN.
  pose proof (r_lss_small _ _ _ _ _ _ HRep) as Hlss.
  pose proof (r_nclits_small _ _ _ _ _ _ HRep) as Hnclits.
  pose proof (key_small p N Hp HN) as Hkp.
  pose proof (r_cstart _ _ _ _ _ _ HRep) as Fcstart.
  pose proof (a_starts _ _ _ _ _ _ HRep) as Astarts.
  pose proof (a_lits _ _ _ _ _ _ HRep) as (tl & Alits & Hclauses).
  destruct (r_starts _ _ _ _ _ _ HRep i Hi_lt) as [Hsi Hsn].
  pose proof (proj2 Hclauses i Hi_lt) as Hcls.
  set (cls := map (fun (q: nat) => lit_of (tl q))
                (seq (starts S i) (starts S (Datatypes.S i) - starts S i))) in Hcls.
  pose proof (clause_length m S N lss xc lims tl i cls Hclauses Hi_lt Hcls) as Hlen.
  (* The model: the blocker is not true, so visit_t looks at the clause *)
  rewrite (skipn_nth (watching (wls x) p) (0%nat, Pos 0%nat) k Hkn), Hnth in Hvisit.
  cbn [visit_t] in Hvisit. rewrite Hnt, Hcls in Hvisit.
  rewrite <- Hnth, <- (skipn_nth (watching (wls x) p) (0%nat, Pos 0%nat) k Hkn) in Hvisit.
  pose proof HT as [Hs Hpk Hbase Hn Hj Hk].
  assert (Hi1: Int.add (Int.repr (Z.of_nat i)) (Int.repr 1)
               = Int.repr (Z.of_nat (Datatypes.S i))).
  { apply incr_nat. lia. }
  assert (Hsub: Int.sub (Int.repr (Z.of_nat (starts S (Datatypes.S i))))
                  (Int.repr (Z.of_nat (starts S i)))
                = Int.repr (Z.of_nat (length cls))).
  { rewrite sub_repr. f_equal. lia. }
  unfold visit_slow, visit_body, visit_loop, f_visit.
  cbn [fn_body drop_stmts first_stmt loop_body Swhile].
  (* kb = -1; int b = s->cstart[i]; int e = s->cstart[i + 1]; *)
  run. clear Fcstart Astarts.
  assert (HC: forall (le': temp_env),
    le' ! _s = Some (sptr S) -> le' ! _p = Some (vint (key p)) ->
    le' ! _base = Some (vint (Z.of_nat (2 * offs S (lit_key p)))) ->
    le' ! _n = Some (vint (Z.of_nat (length (watching (wls x) p)))) ->
    le' ! _j = Some (vint (Z.of_nat (length kept))) ->
      le' ! _k = Some (vint (Z.of_nat k)) ->
    le' ! _i = Some (vint (Z.of_nat i)) -> le' ! _kb = Some (vint (-1)) ->
    le' ! _b = Some (vint (Z.of_nat (starts S i))) ->
    le' ! _e = Some (vint (Z.of_nat (starts S (Datatypes.S i)))) ->
    ClauseAt S N lss lims x p k kept xc t i le' m).
  { intros le' Hs' Hp' Hbase' Hn' Hj' Hk' Hi' Hkb' Hb' He'. constructor.
    - constructor; assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption. }
  (* if (e - b == 1) *)
  ints. eapply (exec_if_cmp _ _ _ Ceq _ _ (Z.of_nat (length cls)) 1).
  - rewrite Hlen. apply eval_clause_len.
    + tmp.
    + tmp.
    + lia.
  - ev.
  - reflexivity.
  - reflexivity.
  - unfold Small. lia.
  - unfold Small. lia.
  - destruct cls as [|c0 [|c1 ls]] eqn:Hc.
    + (* the empty clause watches nothing: dropped *)
      change (zcmp Ceq (Z.of_nat (length [])) 1) with false. cbv beta iota.
      eapply (exec_if_cmp _ _ _ Cge _ _ (Z.of_nat (length [])) 2).
      * rewrite Hlen. apply eval_clause_len.
        -- tmp.
        -- tmp.
        -- lia.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. cbn [length]. lia.
      * unfold Small. lia.
      * change (zcmp Cge (Z.of_nat (length [])) 2) with false. cbv beta iota.
        apply exec_skip. normal. apply visit_tail_correct.
        exists kept, xc, t, i, None. split.
        -- constructor; tmp.
        -- split.
           ++ tmp.
           ++ split.
              ** tmp.
              ** split.
                 --- assumption.
                 --- split.
                     +++ assumption.
                     +++ split.
                         *** assumption.
                         *** split.
                             ---- intros b' Heq. discriminate.
                             ---- assumption.
    + (* a unit clause [c0]: false if c0 is p *)
      change (zcmp Ceq (Z.of_nat (length [c0])) 1) with true. cbv beta iota.
      destruct (clause_lit m S N lss xc lims tl i 0 [c0] HRep Hclauses Hi_lt Hcls)
        as (Hpos0 & Htl0 & Hc0).
      { cbn [length]. lia. }
      cbn [nth] in Htl0, Hc0. rewrite Nat.add_0_r in Htl0, Hpos0.
      pose proof (key_small c0 N Hc0 HN) as Hkc0.
      pose proof (r_clits _ _ _ _ _ _ HRep) as Fclits.
      run. rewrite Htl0. eapply (exec_if_cmp _ _ _ Ceq).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * cbn [zcmp]. rewrite key_eqb. destruct (c0 =? p) eqn:Hc0p.
        -- (* a conflict: return keep_rest(s, p, j, k, n); *)
           cbv beta iota. run. call keep_rest_fun. eapply call_weaken.
           ++ apply (keep_rest_correct S N lss lims x p k kept xc t m). assumption.
           ++ intros m' v [-> HRep']. normal. eapply exec_return.
              ** ev.
              ** ret. exists (vint 1). split.
                 --- apply result_int.
                 --- right. rewrite Hvisit. cbn [fst snd enc_conf]. split.
                     +++ reflexivity.
                     +++ assumption.
        -- (* [c0] does not watch p: dropped *)
           cbv beta iota. apply exec_skip. normal. apply visit_tail_correct.
           exists kept, xc, t, i, None. split.
           ++ constructor; tmp.
           ++ split.
              ** tmp.
              ** split.
                 --- tmp.
                 --- split.
                     +++ assumption.
                     +++ split.
                         *** assumption.
                         *** split.
                             ---- assumption.
                             ---- split.
                                  ++++ intros b' Heq. discriminate.
                                  ++++ assumption.
    + (* two literals or more *)
      replace (zcmp Ceq (Z.of_nat (length (c0 :: c1 :: ls))) 1) with false
        by (symmetry; cbn [zcmp length]; apply Z.eqb_neq; lia).
      cbv beta iota.
      eapply (exec_if_cmp _ _ _ Cge _ _ (Z.of_nat (length (c0 :: c1 :: ls))) 2).
      * rewrite Hlen. apply eval_clause_len.
        -- tmp.
        -- tmp.
        -- lia.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * replace (zcmp Cge (Z.of_nat (length (c0 :: c1 :: ls))) 2) with true
          by (symmetry; cbn [zcmp length]; apply Z.leb_le; lia).
        cbv beta iota.
        apply (visit_watch_correct S N lss lims x p k kept xc t i c0 c1 ls).
        -- apply HC; tmp.
        -- assumption.
        -- assumption.
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
       ...                                                       (visit_slow_correct) *)
Lemma visit_body_correct: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (lims: list nat) (x: Ctx) (p: Lit) (k: nat) (le: temp_env) (m: mem),
  visit_inv S N lss lims x p k le m -> (k < length (watching (wls x) p))%nat ->
  Exec ge le m visit_body (VisitK S N lss lims x p k).
Proof.
  intros S N lss lims x p k le m (kept & xc & t & HT & HM & Hvisit) Hkn.
  pose proof (visit_room S N lss lims x p k kept xc t m HM) as (Hcap & Hroom & Hsmall).
  pose proof (vm_le _ _ _ _ _ _ _ _ _ _ _ HM) as Hle.
  pose proof HM as [Hp _ HRep Apool _ _ Hback _ _].
  pose proof (r_n _ _ _ _ _ _ HRep) as HN.
  pose proof (r_wpool _ _ _ _ _ _ HRep) as Fwpool.
  destruct (visit_watcher S N lss lims x p k kept xc t m k HM Hkn) as [Hi_lt Hb_lt].
  destruct (Hback k) as [Hk1 Hk2].
  { lia. }
  destruct (nth k (watching (wls x) p) (0%nat, Pos 0%nat)) as [i b] eqn:Hnth.
  cbn [fst snd] in Hi_lt, Hb_lt, Hk1, Hk2.
  pose proof (key_small b N Hb_lt HN) as Hkb.
  destruct (watcher_entry (offs S (lit_key p)) k ltac:(lia)) as [Hek Hek1].
  pose proof HT as [Hs Hpk Hbase Hn Hj Hk].
  unfold visit_body, visit_loop, f_visit.
  cbn [fn_body drop_stmts first_stmt loop_body Swhile].
  (* int i = s->wpool[base + 2 * k]; int kb = s->wpool[base + 2 * k + 1]; *)
  run. rewrite Hk1. run. rewrite Hk2.
  (* if (lit_value(s, kb) == 1) *)
  call lit_value_fun. eapply call_weaken.
  - apply (lit_value_correct S N lss xc lims b m). split.
    + assumption.
    + assumption.
  - intros m' v [-> ->]. normal. eapply (exec_if_cmp _ _ _ Ceq _ _ _ 1).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + apply enc_small.
    + unfold Small. lia.
    + cbn [zcmp]. rewrite enc_true. destruct (lookup_true (vals xc) b) eqn:Htrue.
      * (* the blocker is true: keep the watcher; j++; k++; continue; *)
        cbv beta iota.
        apply (visit_keep_correct S N lss lims x p k kept xc t i b _t'26 _t'25).
        -- left. split.
           ++ reflexivity.
           ++ reflexivity.
        -- constructor; tmp.
        -- tmp.
        -- tmp.
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- intros le' m1 HT' Hi' Hkb' HM'.
           pose proof HT' as [Hs' Hpk' Hbase' Hn' Hj' Hk'].
           assert (Hj_incr: Int.add (Int.repr (Z.of_nat (length kept))) (Int.repr 1)
                            = Int.repr (Z.of_nat (length ((i, b) :: kept)))).
           { apply incr_nat. lia. }
           assert (Hk_incr: Int.add (Int.repr (Z.of_nat k)) (Int.repr 1)
                            = Int.repr (Z.of_nat (Datatypes.S k))).
           { apply incr_nat. lia. }
           run. apply exec_continue. abrupt. ints.
           apply loopk_continue with (Datatypes.S k).
           ++ unfold visit_variant, ltof. lia.
           ++ exists ((i, b) :: kept), xc. eexists. split.
              ** constructor; tmp.
              ** split.
                 --- apply HM'.
                 --- rewrite Hvisit,
                       (skipn_nth (watching (wls x) p) (0%nat, Pos 0%nat) k Hkn),
                       Hnth.
                     cbn [visit_t]. rewrite Htrue. reflexivity.
      * (* look at the clause *)
        cbv beta iota. apply exec_skip. normal.
        apply (visit_slow_correct S N lss lims x p k kept xc t i b).
        -- constructor; tmp.
        -- tmp.
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
Qed.

(* The loop of visit, over the watch list ws of p:

     {{ visit_inv 0 }}
       while (k < n) { ... }              (invariant visit_inv; visit_body_correct)
     {{ visit_inv n }}
       s->wlen[p] = j; return 0;                                   (visit_mem_finish)
     {{ VisitPost }}                                                                *)
Lemma visit_loop_correct: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (lims: list nat) (x: Ctx) (p: Lit) (le: temp_env) (m: mem),
  visit_inv S N lss lims x p 0 le m ->
  Exec ge le m visit_loop
    (SeqK ge visit_end (Returns f_visit (VisitPost S N lss lims x p))).
Proof.
  intros S N lss lims x p le m Hinv.
  unfold visit_loop, f_visit. cbn [fn_body drop_stmts first_stmt]. unfold Swhile.
  apply exec_loop with (R := visit_variant x p) (I := visit_inv S N lss lims x p)
    (a := 0%nat).
  - apply well_founded_ltof.
  - intros k le1 m1 Hinv1.
    pose proof Hinv1 as (kept & xc & t & HT & HM & Hvisit).
    pose proof (visit_room S N lss lims x p k kept xc t m1 HM)
      as (Hcap & Hroom & Hsmall).
    pose proof (vm_le _ _ _ _ _ _ _ _ _ _ _ HM) as Hle.
    pose proof HT as [Hs Hpk Hbase Hn Hj Hk].
    (* while (k < n) *)
    apply exec_seq. eapply (exec_if_cmp _ _ _ Clt).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + unfold Small. lia.
    + unfold Small. lia.
    + destruct (Nat.lt_ge_cases k (length (watching (wls x) p))) as [Hkn | Hkn].
      * (* the body *)
        replace (zcmp Clt (Z.of_nat k) (Z.of_nat (length (watching (wls x) p))))
          with true by (symmetry; cbn [zcmp]; apply Z.ltb_lt; lia).
        cbv beta iota. apply exec_skip. normal.
        apply visit_body_correct.
        -- assumption.
        -- assumption.
      * (* the end: s->wlen[p] = j; return 0; *)
        replace (zcmp Clt (Z.of_nat k) (Z.of_nat (length (watching (wls x) p))))
          with false by (symmetry; cbn [zcmp]; apply Z.ltb_ge; lia).
        cbv beta iota. apply exec_break. abrupt. apply loopk_break. normal.
        pose proof HM as [Hp _ HRep _ _ _ _ _ _].
        pose proof (lit_key_lt p N Hp) as HP.
        pose proof (key_small p N Hp (r_n _ _ _ _ _ _ HRep)) as Hkp.
        pose proof Hkp as Hkp'. unfold key in Hkp'.
        pose proof (r_wlen _ _ _ _ _ _ HRep) as Fwlen.
        pose proof (a_wlen _ _ _ _ _ _ HRep) as Awlen.
        unfold visit_end, f_visit. cbn [fn_body drop_stmts].
        run. eapply exec_store.
        -- evl.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- ofs. bound.
        -- ofs. cbn [cast_int_int].
           destruct (arr_storable m1 (b_wlen S) (2 * N) (lit_key p) _
                       (Z.of_nat (length kept)) Awlen HP) as [m2 Hst].
           exists m2. split.
           ++ apply Hst.
           ++ normal. eapply exec_return.
              ** ev.
              ** exists (vint 0). split.
                 --- apply result_int.
                 --- right. rewrite Hvisit, skipn_all2 by lia.
                     cbn [visit_t fst snd enc_conf].
                     split.
                     +++ reflexivity.
                     +++ apply (visit_mem_finish S N lss lims x p k kept xc t m1 m2).
                         *** assumption.
                         *** assumption.
  - assumption.
Qed.

(* visit visits the watchers of the false literal p (visit_t):

     {{ Rep x lims /\ extract p < N }}
       int base = 2 * s->woff[p]; int n = s->wlen[p]; int j = 0; int k = 0;
     {{ visit_inv 0 }}
       while (k < n) { ... }                                     (visit_loop_correct)
       s->wlen[p] = j; return 0;
     {{ result = -1 (out of room) \/
        result = enc_conf r /\ Rep x' lims, where visit_t gives (x', r) }}         *)
Lemma visit_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (p: Lit),
  {{ m | Rep m S N lss x lims /\ (extract p < N)%nat }}
    f_visit(sptr S, vint (key p))
  {{ m', v | v = vint (-1) \/
             (v = vint (enc_conf (snd (visit_t p (watching (wls x) p) [] x))) /\
              Rep m' S N lss (fst (visit_t p (watching (wls x) p) [] x)) lims) }}.
Proof.
  intros S N lss x lims p m [[HRep (t0 & Apool0 & Hpool0)] Hp].
  pose proof (key_small p N Hp (r_n _ _ _ _ _ _ HRep)) as Hkp.
  pose proof (lit_key_lt p N Hp) as HP.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_visit. cbn [fn_body fn_return].
    pose proof (r_woff _ _ _ _ _ _ HRep) as Fwoff.
    pose proof (r_wlen _ _ _ _ _ _ HRep) as Fwlen.
    pose proof (a_woff _ _ _ _ _ _ HRep) as Awoff.
    pose proof (a_wlen _ _ _ _ _ _ HRep) as Awlen.
    assert (Hbase: Int.mul (Int.repr 2) (Int.repr (Z.of_nat (offs S (lit_key p))))
                   = Int.repr (Z.of_nat (2 * offs S (lit_key p)))).
    { rewrite mul_repr. f_equal. lia. }
    (* int base = 2 * s->woff[p]; int n = s->wlen[p]; int j = 0; int k = 0; *)
    run. clear Fwoff Fwlen Awoff Awlen. ints.
    apply visit_loop_correct. exists [], x, t0. split.
    + constructor; tmp.
    + split.
      * (* nothing kept yet, and the pool holds all of ws *)
        constructor; try assumption.
        -- cbn [length]. lia.
        -- intros k q Hk Hq _. apply Hpool0.
           ++ assumption.
           ++ assumption.
           ++ intros [].
        -- intros q Hq. cbn [length] in Hq. lia.
        -- intros q Hq. apply Hpool0.
           ++ assumption.
           ++ unfold watching in Hq. lia.
           ++ intros [].
        -- exists []. rewrite app_nil_r. reflexivity.
        -- intros i b [].
      * reflexivity.
Qed.

Lemma visit_fun: exists (b: block),
  Genv.find_symbol ge _visit = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_visit).
Proof. apply find_fun. reflexivity. Qed.
