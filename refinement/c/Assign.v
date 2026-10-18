(* assign adds a literal to the values and the trail (assign), or gives up when the trail
   is full. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Propagate Analysis.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep RepReasons SetValue.
Import ListNotations.

(* The context x with l appended to its values and its trail. *)
Definition appended (x: Ctx) (l: Lit): Ctx :=
  x <| vals := tset (vals x) (extract l) (Some (is_pos l)) |>
    <| tr := tset (tr x) (tlen x) l |>
    <| tlen := S (tlen x) |>.

(* What assign returns: 0 when the trail is full, or 1 with the memory representing
   assign x l r and the pool array t kept. *)
Abbreviation AssignPost sh N lss x l r t m' v :=
  (v = vint 0 \/ (v = vint 1 /\ RepL m' sh N lss (assign x l r) /\ PoolArr m' sh t)).

(* The temporaries of assign for l with reason r: s, the atom a of l, its value v and
   r. *)
Record AssignTemps {sh: Shape} {l: Lit} {r: Reason} {le: temp_env}: Prop := {
  at_s: le ! _s = Some (sptr sh);
  at_a: le ! _a = Some (vnat (extract l));
  at_v: le ! _v = Some (vint (enc_value (Some (is_pos l))));
  at_r: le ! _r = Some (vint (enc_reason r))
}.
Arguments AssignTemps : clear implicits.

(* The statements of assign after the trail: the phase, reason and level of the atom, and
   return 1. *)
Definition assign_rest: statement := drop_stmts 7 (fn_body f_assign).

(* The stores of the phase, reason and level of the atom of l, after l was appended to
   the trail of x; writing y1 .. y3 for the context after each store, y3 is assign x l r:

     {{ RepL (appended x l) /\ a = extract l /\ v = the sign of l /\ r }}
       s->phs[a] = v;                                                     (rep_store_phs)
     {{ RepL y1 }}
       s->rsn[a] = r;                                                     (rep_store_rsn)
     {{ RepL y2 }}
       s->lvl[a] = s->dl;                                                 (rep_store_lvl)
     {{ RepL y3 }}
       return 1;
     {{ result = 1 /\ RepL (assign x l r) /\ Arr pool t }}

   None of them writes the pool, so its array t is kept. *)
Lemma assign_rest_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (l: Lit) (r: Reason) (t: nat -> Z) (le: temp_env) (m: mem),
  RepL m sh N lss (appended x l) -> (extract l < N)%nat ->
  ReasonBelow (length lss) N r -> PoolArr m sh t -> AssignTemps sh l r le ->
  Exec ge le m assign_rest
    (Returns f_assign (fun (m': mem) (v: val) => AssignPost sh N lss x l r t m' v)).
Proof.
  intros sh N lss x l r t le m HRep Hl Hr Apool [Hs Ha Hv Hr'].
  pose proof (r_n HRep) as HN.
  pose proof (r_nodup HRep) as Hnd.
  assert (Hdl: dl x = length (lims x)) by apply (r_dl_eq HRep).
  pose proof (r_dl_le HRep) as Hdle.
  pose proof (r_phs HRep) as Fphs.
  pose proof (a_phs HRep) as Aphs.
  unfold assign_rest, f_assign. cbn [fn_body drop_stmts].
  (* s->phs[a] = v; *)
  run. eapply (exec_store_arr Aphs Hl).
  - evl.
  - ofs.
  - reflexivity.
  - ev.
  - intros m1 Hst1. normal.
    pose proof (rep_store_phs m m1 (extract l)
                  (Some (is_pos l)) HRep Hl Hst1) as HRep1.
    assert (Apool1: PoolArr m1 sh t).
    { apply (arr_store_other Apool Hst1). neq Hnd. }
    set (y1 := (appended x l) <| phs := tset (phs (appended x l)) (extract l)
                 (Some (is_pos l)) |>) in HRep1.
    keep_mem m1.
    pose proof (r_rsn HRep1) as Frsn1.
    pose proof (a_rsn HRep1) as Arsn1.
    (* s->rsn[a] = r; *)
    run. eapply (exec_store_arr Arsn1 Hl).
    + evl.
    + ofs.
    + reflexivity.
    + ev.
    + intros m2 Hst2. normal.
      pose proof (rep_store_rsn m1 m2 (extract l) r HRep1 Hl Hr Hst2)
        as HRep2.
      assert (Apool2: PoolArr m2 sh t).
      { apply (arr_store_other Apool1 Hst2). neq Hnd. }
      set (y2 := y1 <| rsn := tset (rsn y1) (extract l) r |>) in HRep2.
      keep_mem m2.
      pose proof (r_lvl HRep2) as Flvl2.
      pose proof (a_lvl HRep2) as Alvl2.
      pose proof (r_dl HRep2) as Fdl2.
      (* s->lvl[a] = s->dl; *)
      run. eapply (exec_store_arr Alvl2 Hl).
      * evl.
      * ofs.
      * reflexivity.
      * ev.
      * intros m3 Hst3. normal.
        pose proof (rep_store_lvl m2 m3 (extract l) (length (lims x))
                      HRep2 Hl Hdle Hst3) as HRep3.
        (* return 1; with the level of the decisions, dl x *)
        eapply exec_return.
        -- ev.
        -- exists (vint 1). split.
           ++ apply result_int.
           ++ right. split.
              ** reflexivity.
              ** split.
                 --- unfold y2, y1 in HRep3. rewrite <- Hdl in HRep3. apply HRep3.
                 --- apply (arr_store_other Apool2 Hst3). neq Hnd.
Qed.

(* The statements of assign after its test: set_value, the stores and return 1. *)
Definition assign_stores: statement := drop_stmts 4 (fn_body f_assign).

(* The stores of assign, when the trail has room. Writing x1 .. x3 for the context after
   each step, set_value and each store keep the representation (by set_value_correct and
   the lemmas of Rep.v), and x3 is appended x l:

     {{ RepL m sh N lss x /\ tlen x < N /\ a = extract l /\ t = tlen x }}
       set_value(s, a, v);                                            (set_value_correct)
     {{ RepL x1 }}
       s->tr[t] = l;                                                       (rep_store_tr)
     {{ RepL x2 }}
       s->tlen = t + 1;                                                  (rep_store_tlen)
     {{ RepL x3 }}
       the other stores, and return 1;                             (assign_rest_correct)
     {{ result = 1 /\ RepL (assign x l r) /\ Arr pool t }}

   None of them writes the pool, so its array t is kept. *)
Lemma assign_stores_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (l: Lit) (r: Reason) (t: nat -> Z) (le: temp_env) (m: mem),
  RepL m sh N lss x -> (extract l < N)%nat -> (tlen x < N)%nat ->
  ReasonBelow (length lss) N r -> PoolArr m sh t -> AssignTemps sh l r le ->
  le ! _l = Some (vint (key l)) -> le ! _t = Some (vnat (tlen x)) ->
  Exec ge le m assign_stores
    (Returns f_assign (fun (m': mem) (v: val) => AssignPost sh N lss x l r t m' v)).
Proof.
  intros sh N lss x l r t le m HRep Hl Hlt Hr Apool [Hs Ha Hv Hr'] Hl' Ht.
  pose proof (r_n HRep) as HN.
  pose proof (key_small l N Hl HN) as Hkey.
  pose proof (r_nodup HRep) as Hnd.
  unfold assign_stores, f_assign. cbn [fn_body drop_stmts].
  (* set_value(s, a, v); *)
  run. eapply (exec_call_triple_none set_value_fun
                 (set_value_correct sh N lss x (extract l) (Some (is_pos l)))).
  - reflexivity.
  - evs.
  - split.
    + apply HRep.
    + apply Hl.
  - intros m1 v1 [HRep1 Hun1]. normal. transfer Hun1 Hnd. keep_mem m1.
    rename Apool into Apool1.
    set (x1 := x <| vals := tset (vals x) (extract l) (Some (is_pos l)) |>) in HRep1.
    pose proof (r_tr HRep1) as Ftr1.
    pose proof (a_tr HRep1) as Atr1.
    (* s->tr[t] = l; *)
    run. eapply (exec_store_arr Atr1 Hlt).
    + evl.
    + ofs.
    + reflexivity.
    + ev.
    + intros m2 Hst2. normal.
      assert (Hj: (tlen x1 <= tlen x < N)%nat) by (cbn; lia).
      pose proof (rep_store_tr m1 m2 (tlen x) l HRep1 Hj Hst2)
        as HRep2.
      assert (Apool2: PoolArr m2 sh t).
      { apply (arr_store_other Apool1 Hst2). neq Hnd. }
      set (x2 := x1 <| tr := tset (tr x1) (tlen x) l |>) in HRep2.
      keep_mem m2.
      pose proof (r_tlen HRep2) as Ftlen2.
      (* s->tlen = t + 1; *)
      run. eapply (exec_store_fld Ftlen2).
      * evl.
      * reflexivity.
      * ev.
      * intros m3 Hst3. normal.
        assert (Hadd: Int.add (Int.repr (Z.of_nat (tlen x))) (Int.repr 1)
                    = Int.repr (Z.of_nat (S (tlen x)))).
        { rewrite add_repr by lia. f_equal. lia. }
        cbn [cast_int_int] in Hst3. rewrite Hadd in Hst3.
        (* The trail is one longer: its new end is l, of an atom below N. *)
        assert (Hn: (S (tlen x) <= N)%nat) by lia.
        assert (Hq: (qhead x2 <= S (tlen x))%nat).
        { pose proof (r_qhead_le HRep). cbn. lia. }
        assert (Hatoms: forall (j: nat), (j < S (tlen x))%nat ->
                       (extract (tget (tr x2) j) < N)%nat).
        { intros j Hj'. unfold x2, x1. cbn [set_tr set_vals tr].
          rewrite tget_tset. destruct (Nat.eq_dec (tlen x) j) as [Heq | Hne].
          - assumption.
          - apply (r_tr_atoms HRep). lia. }
        pose proof (rep_store_tlen m2 m3 _ HRep2 Hn Hq Hatoms Hst3)
          as HRep3.
        assert (Apool3: PoolArr m3 sh t).
        { apply (arr_store_other Apool2 Hst3). neq Hnd. }
        (* the phase, reason and level *)
        apply (assign_rest_correct sh N lss x l r t).
        -- apply HRep3.
        -- assumption.
        -- assumption.
        -- assumption.
        -- constructor; tmp.
Qed.

(* assign stores the value of l, appends l to the trail and sets the phase, reason r and
   level of its atom, unless the trail is full:

     {{ RepL m sh N lss x /\ extract l < N /\ ReasonBelow r /\ Arr m pool t }}
       int a = l >> 1;
       int v = 1 - 2 * (l & 1);
       int t = s->tlen;
       if (t >= s->nv) return 0;
     {{ result = 0 (out of room) }}
     {{ RepL x /\ tlen x < N /\ a = extract l /\ t = tlen x }}
       the stores, and return 1;                                 (assign_stores_correct)
     {{ result = 1 /\ RepL (assign x l r) /\ Arr pool t }}                            *)
Lemma assign_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (l: Lit) (r: Reason) (t: nat -> Z),
  {{ m | RepL m sh N lss x /\ (extract l < N)%nat /\
    ReasonBelow (length lss) N r /\ PoolArr m sh t }}
    f_assign(sptr sh, vint (key l), vint (enc_reason r))
  {{ m', v | AssignPost sh N lss x l r t m' v }}.
Proof.
  intros sh N lss x l r t m (HRep & Hl & Hr & Apool).
  pose proof (key_small l N Hl (r_n HRep)) as Hkey.
  (* The shift gives the atom of l, and the lowest bit its sign. *)
  assert (Hshr: Int.shr (Int.repr (key l)) (Int.repr 1)
                = Int.repr (Z.of_nat (extract l))).
  { apply shr_key. lia. }
  assert (Hand: Int.and (Int.repr (key l)) (Int.repr 1)
                = Int.repr (if is_pos l then 0 else 1)).
  { apply and_key. lia. }
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_assign. cbn [fn_body fn_return].
    pose proof HRep as HRep0. destruct HRep0.
    (* int a = l >> 1; int v = 1 - 2 * (l & 1); int t = s->tlen; *)
    run.
    (* if (t >= s->nv) return 0; *)
    eapply exec_if_ge.
    + ev.
    + ev.
    + reflexivity.
    + lia.
    + (* the trail is full: return 0; *)
      intros Hfull. eapply exec_return.
      * ev.
      * ret. exists (vint 0). split.
        -- apply result_int.
        -- now left.
    + (* the trail has room: the stores *)
      intros Hroom. assert (Hlt: (tlen x < N)%nat) by lia.
      apply exec_skip. normal.
      apply (assign_stores_correct sh N lss x l r t).
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * constructor.
        -- tmp.
        -- ints. tmp.
        -- ints. rewrite sign_value. tmp.
        -- tmp.
      * tmp.
      * tmp.
Qed.

Lemma assign_fun: FunAt _assign f_assign.
Proof. apply find_fun. reflexivity. Qed.
