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
  set_tlen (set_tr (set_vals x (tset (vals x) (extract l) (Some (is_pos l))))
    (tset (tr x) (tlen x) l)) (Datatypes.S (tlen x)).

(* The statements of assign after the trail: the phase, reason and level of the atom, and
   return 1. *)
Definition assign_rest: statement := drop_stmts 7 (fn_body f_assign).

(* The stores of the phase, reason and level of the atom of l, after l was appended to
   the trail of x; writing y1 .. y3 for the context after each store, y3 is assign x l r:

     {{ RepB (appended x l) /\ a = extract l /\ v = the sign of l /\ r }}
       s->phs[a] = v;                                                     (rep_store_phs)
     {{ RepB y1 }}
       s->rsn[a] = r;                                                     (rep_store_rsn)
     {{ RepB y2 }}
       s->lvl[a] = s->dl;                                                 (rep_store_lvl)
     {{ RepB y3 }}
       return 1;
     {{ result = 1 /\ RepB (assign x l r) /\ Arr pool t }}

   None of them writes the pool, so its array t is kept. *)
Lemma assign_rest_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (l: Lit) (r: Reason) (t: nat -> Z) (le: temp_env) (m: mem),
  RepB m S N lss (appended x l) lims -> (extract l < N)%nat ->
  ReasonBelow (length lss) N r -> Arr m (b_wpool S) (2 * npool S) t ->
  le ! _s = Some (sptr S) -> le ! _a = Some (vint (Z.of_nat (extract l))) ->
  le ! _v = Some (vint (enc_value (Some (is_pos l)))) ->
  le ! _r = Some (vint (enc_reason r)) ->
  Exec ge le m assign_rest (Returns f_assign (fun (m': mem) (v: val) =>
    v = vint 0 \/
    (v = vint 1 /\ RepB m' S N lss (assign x l r) lims /\
     Arr m' (b_wpool S) (2 * npool S) t))).
Proof.
  intros S N lss x lims l r t le m HRep Hl Hr Apool Hs Ha Hv Hr'.
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_dl_eq _ _ _ _ _ _ _ HRep) as Hdl.
  pose proof (r_dl_le _ _ _ _ _ _ _ HRep) as Hdle.
  pose proof (r_phs _ _ _ _ _ _ _ HRep) as Fphs.
  pose proof (a_phs _ _ _ _ _ _ _ HRep) as Aphs.
  unfold assign_rest, f_assign. cbn [fn_body drop_stmts].
  (* s->phs[a] = v; *)
  run. eapply exec_store.
  - evl.
  - ev.
  - reflexivity.
  - reflexivity.
  - ofs. bound.
  - ofs. cbn [cast_int_int].
    destruct (arr_storable m (b_phs S) N (extract l) _ (enc_value (Some (is_pos l))) Aphs
                Hl) as [m1 Hst1].
    exists m1. split.
    + apply Hst1.
    + normal.
      pose proof (rep_store_phs m m1 S N lss (appended x l) lims (extract l)
                    (Some (is_pos l)) HRep Hl Hst1) as HRep1.
      assert (Apool1: Arr m1 (b_wpool S) (2 * npool S) t).
      { apply (arr_store_other _ _ _ _ _ _ _ _ _ Apool Hst1). neq Hnd. }
      set (y1 := set_phs (appended x l) (tset (phs (appended x l)) (extract l)
                   (Some (is_pos l)))) in HRep1.
      keep_mem m1.
      pose proof (r_rsn _ _ _ _ _ _ _ HRep1) as Frsn1.
      pose proof (a_rsn _ _ _ _ _ _ _ HRep1) as Arsn1.
      (* s->rsn[a] = r; *)
      run. eapply exec_store.
      * evl.
      * ev.
      * reflexivity.
      * reflexivity.
      * ofs. bound.
      * ofs. cbn [cast_int_int].
        destruct (arr_storable m1 (b_rsn S) N (extract l) _ (enc_reason r) Arsn1 Hl)
          as [m2 Hst2].
        exists m2. split.
        -- apply Hst2.
        -- normal.
           pose proof (rep_store_rsn m1 m2 S N lss y1 lims (extract l) r HRep1 Hl Hr
             Hst2)
             as HRep2.
           assert (Apool2: Arr m2 (b_wpool S) (2 * npool S) t).
           { apply (arr_store_other _ _ _ _ _ _ _ _ _ Apool1 Hst2). neq Hnd. }
           set (y2 := set_rsn y1 (tset (rsn y1) (extract l) r)) in HRep2.
           keep_mem m2.
           pose proof (r_lvl _ _ _ _ _ _ _ HRep2) as Flvl2.
           pose proof (a_lvl _ _ _ _ _ _ _ HRep2) as Alvl2.
           pose proof (r_dl _ _ _ _ _ _ _ HRep2) as Fdl2.
           (* s->lvl[a] = s->dl; *)
           run. eapply exec_store.
           ++ evl.
           ++ ev.
           ++ reflexivity.
           ++ reflexivity.
           ++ ofs. bound.
           ++ ofs. cbn [cast_int_int].
              destruct (arr_storable m2 (b_lvl S) N (extract l) _
                          (Z.of_nat (length lims)) Alvl2 Hl) as [m3 Hst3].
              exists m3. split.
              ** apply Hst3.
              ** normal.
                 pose proof (rep_store_lvl m2 m3 S N lss y2 lims (extract l) (length
                   lims)
                               HRep2 Hl Hdle Hst3) as HRep3.
                 (* return 1; with the level of the decisions, dl x *)
                 eapply exec_return.
                 --- ev.
                 --- exists (vint 1). split.
                     +++ apply result_int.
                     +++ right. split.
                         *** reflexivity.
                         *** split.
                             ---- unfold y2, y1 in HRep3. cbn [appended] in Hdl.
                                  rewrite <- Hdl in HRep3. apply HRep3.
                             ---- apply
                                          (arr_store_other _ _ _ _ _ _ _ _ _ Apool2
                                            Hst3).
                                  neq Hnd.
Qed.

(* The statements of assign after its test: set_value, the stores and return 1. *)
Definition assign_stores: statement := drop_stmts 4 (fn_body f_assign).

(* The stores of assign, when the trail has room. Writing x1 .. x3 for the context after
   each step, set_value and each store keep the representation (by set_value_correct and
   the lemmas of Rep.v), and x3 is appended x l:

     {{ RepB m S N lss x lims /\ tlen x < N /\ a = extract l /\ t = tlen x }}
       set_value(s, a, v);                                            (set_value_correct)
     {{ RepB x1 }}
       s->tr[t] = l;                                                       (rep_store_tr)
     {{ RepB x2 }}
       s->tlen = t + 1;                                                  (rep_store_tlen)
     {{ RepB x3 }}
       the other stores, and return 1;                             (assign_rest_correct)
     {{ result = 1 /\ RepB (assign x l r) /\ Arr pool t }}

   None of them writes the pool, so its array t is kept. *)
Lemma assign_stores_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (l: Lit) (r: Reason) (t: nat -> Z) (le: temp_env) (m: mem),
  RepB m S N lss x lims -> (extract l < N)%nat -> (tlen x < N)%nat ->
  ReasonBelow (length lss) N r -> Arr m (b_wpool S) (2 * npool S) t ->
  le ! _s = Some (sptr S) -> le ! _l = Some (vint (key l)) ->
  le ! _a = Some (vint (Z.of_nat (extract l))) ->
  le ! _v = Some (vint (enc_value (Some (is_pos l)))) ->
  le ! _t = Some (vint (Z.of_nat (tlen x))) -> le ! _r = Some (vint (enc_reason r)) ->
  Exec ge le m assign_stores (Returns f_assign (fun (m': mem) (v: val) =>
    v = vint 0 \/
    (v = vint 1 /\ RepB m' S N lss (assign x l r) lims /\
     Arr m' (b_wpool S) (2 * npool S) t))).
Proof.
  intros S N lss x lims l r t le m HRep Hl Hlt Hr Apool Hs Hl' Ha Hv Ht Hr'.
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (key_small l N Hl HN) as Hkey.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  unfold assign_stores, f_assign. cbn [fn_body drop_stmts].
  (* set_value(s, a, v); *)
  run. call set_value_fun. eapply call_weaken.
  { apply (set_value_correct (lt := []) S N lss x lims (extract l)
             (Some (is_pos l))).
    split; assumption. }
  intros m1 v1 [HRep1 Hun1]. normal. transfer Hun1 Hnd. keep_mem m1.
  rename Apool into Apool1.
  set (x1 := set_vals x (tset (vals x) (extract l) (Some (is_pos l)))) in HRep1.
  pose proof (r_tr _ _ _ _ _ _ _ HRep1) as Ftr1.
  pose proof (a_tr _ _ _ _ _ _ _ HRep1) as Atr1.
  (* s->tr[t] = l; *)
  run. eapply exec_store.
  - evl.
  - ev.
  - reflexivity.
  - reflexivity.
  - ofs. bound.
  - ofs. cbn [cast_int_int].
    destruct (arr_storable m1 (b_tr S) N (tlen x) _ (key l) Atr1 Hlt) as [m2 Hst2].
    exists m2. split.
    + apply Hst2.
    + normal.
      assert (Hj: (tlen x1 <= tlen x < N)%nat) by (cbn; lia).
      pose proof (rep_store_tr m1 m2 S N lss x1 lims (tlen x) l HRep1 Hj Hst2)
        as HRep2.
      assert (Apool2: Arr m2 (b_wpool S) (2 * npool S) t).
      { apply (arr_store_other _ _ _ _ _ _ _ _ _ Apool1 Hst2). neq Hnd. }
      set (x2 := set_tr x1 (tset (tr x1) (tlen x) l)) in HRep2.
      keep_mem m2.
      pose proof (r_tlen _ _ _ _ _ _ _ HRep2) as Ftlen2.
      (* s->tlen = t + 1; *)
      run. eapply exec_store.
      * evl.
      * ev.
      * reflexivity.
      * reflexivity.
      * fofs. bound.
      * fofs. cbn [cast_int_int].
        assert (Hadd: Int.add (Int.repr (Z.of_nat (tlen x))) (Int.repr 1)
                    = Int.repr (Z.of_nat (Datatypes.S (tlen x)))).
        { rewrite add_repr by lia. f_equal. lia. }
        rewrite Hadd.
        destruct
                  (fld_storable m2 (b_s S) 80 Mint32 _ (vint (Z.of_nat (Datatypes.S
                    (tlen x)))) Ftlen2) as [m3 Hst3].
        exists m3. split.
        -- apply Hst3.
        -- normal.
           (* The trail is one longer: its new end is l, of an atom below N. *)
           assert (Hn: (Datatypes.S (tlen x) <= N)%nat) by lia.
           assert (Hq: (qhead x2 <= Datatypes.S (tlen x))%nat).
           { pose proof (r_qhead_le _ _ _ _ _ _ _ HRep). cbn. lia. }
           assert (Hatoms: forall (j: nat), (j < Datatypes.S (tlen x))%nat ->
                          (extract (tget (tr x2) j) < N)%nat).
           { intros j Hj'. unfold x2, x1. cbn [set_tr set_vals tr].
             rewrite tget_tset. destruct (Nat.eq_dec (tlen x) j) as [Heq | Hne].
             - assumption.
             - apply (r_tr_atoms _ _ _ _ _ _ _ HRep). lia. }
           pose proof (rep_store_tlen m2 m3 S N lss x2 lims _ HRep2 Hn Hq Hatoms
                       Hst3) as HRep3.
           assert (Apool3: Arr m3 (b_wpool S) (2 * npool S) t).
           { apply (arr_store_other _ _ _ _ _ _ _ _ _ Apool2 Hst3). neq Hnd. }
           (* the phase, reason and level *)
           apply (assign_rest_correct S N lss x lims l r t).
           ++ apply HRep3.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ tmp.
Qed.

(* assign stores the value of l, appends l to the trail and sets the phase, reason r and
   level of its atom, unless the trail is full:

     {{ RepB m S N lss x lims /\ extract l < N /\ r has a clause C finds /\ Arr m pool t
     }}
       int a = l >> 1;
       int v = 1 - 2 * (l & 1);
       int t = s->tlen;
       if (t >= s->nv) return 0;
     {{ result = 0 (out of room) }}
     {{ RepB x /\ tlen x < N /\ a = extract l /\ t = tlen x }}
       the stores, and return 1;                                 (assign_stores_correct)
     {{ result = 1 /\ RepB (assign x l r) /\ Arr pool t }}                            *)
Lemma assign_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (l: Lit) (r: Reason) (t: nat -> Z),
  {{ m | RepB m S N lss x lims /\ (extract l < N)%nat /\
    ReasonBelow (length lss) N r /\ Arr m (b_wpool S) (2 * npool S) t }}
    f_assign(sptr S, vint (key l), vint (enc_reason r))
  {{ m', v | v = vint 0 \/
             (v = vint 1 /\ RepB m' S N lss (assign x l r) lims /\
              Arr m' (b_wpool S) (2 * npool S) t) }}.
Proof.
  intros S N lss x lims l r t m (HRep & Hl & Hr & Apool).
  pose proof (key_small l N Hl (r_n _ _ _ _ _ _ _ HRep)) as Hkey.
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
    eapply (exec_if_cmp _ _ _ Cge).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + unfold Small. lia.
    + unfold Small. lia.
    + destruct (Nat.lt_ge_cases (tlen x) N) as [Hlt | Hge].
      * (* the trail has room: the stores *)
        replace (zcmp Cge (Z.of_nat (tlen x)) (Z.of_nat N)) with false
          by (symmetry; cbn [zcmp]; apply Z.leb_gt; lia).
        cbv beta iota. apply exec_skip. normal.
        apply (assign_stores_correct S N lss x lims l r t).
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- tmp.
        -- tmp.
        -- ints. tmp.
        -- ints. rewrite sign_value. tmp.
        -- tmp.
        -- tmp.
      * (* the trail is full: return 0; *)
        replace (zcmp Cge (Z.of_nat (tlen x)) (Z.of_nat N)) with true
          by (symmetry; cbn [zcmp]; apply Z.leb_le; lia).
        cbv beta iota. eapply exec_return.
        -- ev.
        -- ret. exists (vint 0). split.
           ++ apply result_int.
           ++ now left.
Qed.

Lemma assign_fun: exists (b: block),
  Genv.find_symbol ge _assign = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_assign).
Proof. apply find_fun. reflexivity. Qed.
