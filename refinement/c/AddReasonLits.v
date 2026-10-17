(* add_reason_lits adds the literals of the reason of a trail literal to the analysis
   (reason_lits, then add_lits, as in analyze_loop). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Propagate Analysis.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep AddLits.
Import ListNotations.

(* What analyze_loop does with the reason of the trail literal t: add the literals of its
   clause other than t, or stop if it has none. *)
Definition reason_add (y: Ctx) (t: Lit) (d: nat) (lt: list Lit) (pathc: nat):
  Table bool * list Lit * option nat :=
match reason_lits y (tget (rsn y) (extract t)) with
| None    => (mrk y, lt, None)
| Some ys => add_lits (lvl y) d (nvars y) (Some t) ys (mrk y) lt pathc
end.

(* What add_reason_lits returns and leaves, from the memory m of the call: the count of
   reason_add or -1, the marks and lower literals it gives, and only the marks, lt and
   the
   fields of s changed. *)
Definition ReasonPost (S: Shape) (N: nat) (lss: list (list Lit)) (y: Ctx)
  (lims: list nat) (lt: list Lit) (t: Lit) (d pathc: nat) (m m': mem) (v: val): Prop :=
  match reason_add y t d lt pathc with
  | (mk', lt', r) =>
    v = vint (enc_count r) /\ RepL m' S N lss (set_mrk y mk') lims lt' /\
    Mem.unchanged_on
      (fun (b: block) (_: Z) => b <> b_mrk S /\ b <> b_lt S /\ b <> b_s S) m m'
  end.

(* Without a reason clause, nothing changes and the result is -1. *)
Lemma reason_post_none {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (y: Ctx) (lims: list nat) (t: Lit) (d pathc: nat) (m: mem),
  RepL m S N lss y lims lt -> reason_lits y (tget (rsn y) (extract t)) = None ->
  ReasonPost S N lss y lims lt t d pathc m m (vint (-1)).
Proof.
  intros S N lss y lims t d pathc m HRep Hnone. unfold ReasonPost, reason_add.
  rewrite Hnone. split.
  - reflexivity.
  - split.
    + apply rep_mrk_same. assumption.
    + apply Mem.unchanged_on_refl.
Qed.

(* The keys from position b on that hold the literals ls, read back as literals. *)
Lemma map_lit_of_seq: forall (t: nat -> Z) (ls: list Lit) (b: nat),
  (forall (k: nat), (k < length ls)%nat -> t (b + k)%nat = key (nth k ls (Pos 0%nat))) ->
  map (fun (q: nat) => lit_of (t q)) (seq b (length ls)) = ls.
Proof.
  intros t ls. induction ls as [|a ls IH]; intros b Ht.
  - reflexivity.
  - cbn [length seq map]. f_equal.
    + rewrite <- (Nat.add_0_r b), (Ht 0%nat) by (cbn; lia). apply lit_of_key.
    + apply IH. intros k Hk. replace (Datatypes.S b + k)%nat with (b + Datatypes.S k)%nat
        by lia.
      apply (Ht (Datatypes.S k)). cbn. lia.
Qed.

(* The statements of add_reason_lits for an input clause and for a reason clause. *)
Definition reason_input: statement :=
  then_stmt (first_stmt (drop_stmts 1 (fn_body f_add_reason_lits))).
Definition reason_learnt: statement :=
  then_stmt (first_stmt (drop_stmts 2 (fn_body f_add_reason_lits))).

(* The reason of t is input clause i (r = i + 1), one of the clauses as RepL says: add
   its literals, from cstart[i] to cstart[i + 1] in clits:

     {{ RepL y lt /\ r = i + 1 /\ i < ncl }}
       if (r > s->ncl) return -1;
       return add_lits(s, s->clits, s->cstart[r - 1], s->cstart[r], t, d, pathc);
     {{ ReasonPost, as reason_lits gives clause i }}                (add_lits_correct) *)
Lemma reason_input_correct {lt: list Lit}: forall (S: Shape) (N: nat)
  (lss: list (list Lit)) (y: Ctx) (lims: list nat) (t: Lit) (d pathc i: nat)
  (rest: statement) (le: temp_env) (m: mem),
  RepL m S N lss y lims lt -> tget (rsn y) (extract t) = input i ->
  (i < length lss)%nat -> (extract t < N)%nat -> (d <= N)%nat -> (pathc <= N)%nat ->
  le ! _s = Some (sptr S) -> le ! _t = Some (vint (key t)) ->
  le ! _d = Some (vint (Z.of_nat d)) -> le ! _pathc = Some (vint (Z.of_nat pathc)) ->
  le ! _r = Some (vint (Z.of_nat i + 1)) ->
  Exec ge le m reason_input
    (SeqK ge rest (Returns f_add_reason_lits (ReasonPost S N lss y lims lt t d pathc
      m))).
Proof.
  intros S N lss y lims t d pathc i rest le m HRep Hr Hi Ht Hd Hp Hs Ht' Hd' Hp' Hr'.
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_lss_small _ _ _ _ _ _ _ HRep) as Hlss.
  pose proof (r_ncl _ _ _ _ _ _ _ HRep) as Fncl.
  pose proof (r_cstart _ _ _ _ _ _ _ HRep) as Fcs.
  pose proof (a_starts _ _ _ _ _ _ _ HRep) as Astarts.
  pose proof (r_clits _ _ _ _ _ _ _ HRep) as Fcl.
  pose proof (a_lits _ _ _ _ _ _ _ HRep) as (tcl & Acl & Hatoms & Hcl).
  replace (Z.of_nat i + 1) with (Z.of_nat (Datatypes.S i)) in Hr' by lia.
  unfold reason_input, f_add_reason_lits. cbn [fn_body drop_stmts first_stmt then_stmt].
  (* if (r > s->ncl) return -1; *)
  run. eapply (exec_if_cmp _ _ _ Cgt).
  - ev.
  - ev.
  - reflexivity.
  - reflexivity.
  - unfold Small. lia.
  - unfold Small. lia.
  - (* clause i is there: add its literals *)
    replace (zcmp Cgt (Z.of_nat (Datatypes.S i)) (Z.of_nat (length lss))) with false
      by (cbn [zcmp]; symmetry; apply Z.ltb_ge; lia).
    destruct (r_starts _ _ _ _ _ _ _ HRep i Hi) as [Hsi Hsn].
    assert (Hsub: Int.sub (Int.repr (Z.of_nat (Datatypes.S i))) (Int.repr 1)
                  = Int.repr (Z.of_nat i)).
    { rewrite sub_repr. f_equal. lia. }
    cbv beta iota. apply exec_skip. normal.
    (* return add_lits(s, s->clits, s->cstart[r - 1], s->cstart[r], t, d, pathc); *)
    run. call add_lits_fun. eapply call_weaken.
    * apply (add_lits_correct (lt := lt) S N lss y lims (b_clits S) (nclits S) tcl
               (starts S i) (starts S (Datatypes.S i)) (Some t) d pathc).
      split.
      -- assumption.
      -- split.
         ++ now left.
         ++ split.
            ** assumption.
            ** split.
               --- lia.
               --- split.
                   +++ intros k Hk. apply Hatoms. lia.
                   +++ split.
                       *** intros y' Heq. injection Heq as <-. assumption.
                       *** split.
                           ---- assumption.
                           ---- split.
                                ++++ assumption.
                                ++++ apply (r_nclits_small _ _ _ _ _ _ _ HRep).
    * intros m' v Hpost. normal.
      destruct
                  (add_lits (lvl y) d (nvars y) (Some t) (map (fun (k: nat) => lit_of
                    (tcl k))
                     (seq (starts S i) (starts S (Datatypes.S i) - starts S i)))
                  (mrk y) lt pathc) as [[mk' lt'] r] eqn:Hadd.
      destruct Hpost as (-> & HRep' & Hun).
      eapply exec_return.
      -- ev.
      -- ret. exists (vint (enc_count r)). split.
         ++ apply result_int.
         ++ unfold ReasonPost, reason_add, reason_lits. rewrite Hr, (Hcl i Hi), Hadd.
            split.
            ** reflexivity.
            ** split.
               --- assumption.
               --- assumption.
Qed.

(* The reason of t is reason clause j (r = -(j + 1)): add its literals, from rbeg[j] on
   for rlen[j] of them in rlits, if it is one of the nr of them:

     {{ RepL y lt /\ r = -(j + 1) }}
       if (r < -s->nr) return -1;
     {{ result = -1, as reason clause j is not there: reason_lits gives none }}
       int b = s->rbeg[-r - 1];
       return add_lits(s, s->rlits, b, b + s->rlen[-r - 1], t, d, pathc);
     {{ ReasonPost, as reason_lits gives reason clause j }}         (add_lits_correct) *)
Lemma reason_learnt_correct {lt: list Lit}: forall (S: Shape) (N: nat)
  (lss: list (list Lit)) (y: Ctx) (lims: list nat) (t: Lit) (d pathc j: nat)
  (rest: statement) (le: temp_env) (m: mem),
  RepL m S N lss y lims lt -> tget (rsn y) (extract t) = learnt j ->
  (j < N)%nat -> (extract t < N)%nat -> (d <= N)%nat -> (pathc <= N)%nat ->
  le ! _s = Some (sptr S) -> le ! _t = Some (vint (key t)) ->
  le ! _d = Some (vint (Z.of_nat d)) -> le ! _pathc = Some (vint (Z.of_nat pathc)) ->
  le ! _r = Some (vint (- (Z.of_nat j + 1))) ->
  Exec ge le m reason_learnt
    (SeqK ge rest (Returns f_add_reason_lits (ReasonPost S N lss y lims lt t d pathc
      m))).
Proof.
  intros S N lss y lims t d pathc j rest le m HRep Hr Hj Ht Hd Hp Hs Ht' Hd' Hp' Hr'.
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_nr _ _ _ _ _ _ _ HRep) as Fnr.
  pose proof (r_nr_le _ _ _ _ _ _ _ HRep) as Hnr.
  pose proof (r_rcap_small _ _ _ _ _ _ _ HRep) as Hrcap.
  pose proof (r_rsize_le _ _ _ _ _ _ _ HRep) as Hsize.
  pose proof (r_rcl_atoms _ _ _ _ _ _ _ HRep) as Hatoms.
  pose proof (r_rbeg _ _ _ _ _ _ _ HRep) as Frbeg.
  pose proof (r_rlen _ _ _ _ _ _ _ HRep) as Frlen.
  pose proof (r_rlits _ _ _ _ _ _ _ HRep) as Frlits.
  pose proof (a_rbeg _ _ _ _ _ _ _ HRep) as (tb & Arbeg & Htb).
  pose proof (a_rlen _ _ _ _ _ _ _ HRep) as (tn & Arlen & Htn).
  pose proof (a_rlits _ _ _ _ _ _ _ HRep) as (trl & Arlits & Htrl).
  assert (Hneg: Int.neg (Int.repr (Z.of_nat (nr y))) = Int.repr (- Z.of_nat (nr y))).
  { apply Int.neg_repr. }
  unfold reason_learnt, f_add_reason_lits. cbn [fn_body drop_stmts first_stmt then_stmt].
  (* if (r < -s->nr) return -1; *)
  run. eapply (exec_if_cmp _ _ _ Clt _ _ (- (Z.of_nat j + 1)) (- Z.of_nat (nr y))).
  - ev.
  - (* -s->nr *)
    eapply eval_Eunop.
    + ev.
    + unfold sem_unary_operation, sem_neg. simpl. rewrite Hneg. reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold Small. lia.
  - unfold Small. lia.
  - destruct (Nat.lt_ge_cases j (nr y)) as [Hjn | Hjn].
    + (* reason clause j is there: add its literals *)
      replace (zcmp Clt (- (Z.of_nat j + 1)) (- Z.of_nat (nr y))) with false
        by (cbn [zcmp]; symmetry; apply Z.ltb_ge; lia).
      set (rs := reasons_size (rcl y) j).
      set (len := length (tget (rcl y) j)).
      (* Reason clause j ends within the first nr of them. *)
      assert (Hend: (rs + len <= reasons_size (rcl y) (nr y))%nat).
      { unfold rs, len. change (reasons_size (rcl y) j + length (tget (rcl y) j))%nat
          with (reasons_size (rcl y) (Datatypes.S j)).
        apply reasons_size_le. lia. }
      assert (Hidx: Int.sub (Int.neg (Int.repr (- (Z.of_nat j + 1)))) (Int.repr 1)
                    = Int.repr (Z.of_nat j)).
      { rewrite Int.neg_repr, sub_repr. f_equal. lia. }
      assert (Hadd: Int.add (Int.repr (Z.of_nat rs)) (Int.repr (Z.of_nat len))
                    = Int.repr (Z.of_nat (rs + len))).
      { rewrite add_repr. f_equal. lia. }
      cbv beta iota. apply exec_skip. normal.
      (* int b = s->rbeg[-r - 1]; *)
      run. rewrite (Htb j Hjn). run. rewrite (Htn j Hjn).
      fold rs len.
      (* return add_lits(s, s->rlits, b, b + s->rlen[-r - 1], t, d, pathc); *)
      call add_lits_fun. cbn [cast_int_int]. rewrite Hadd. eapply call_weaken.
      * apply (add_lits_correct (lt := lt) S N lss y lims (b_rlits S) (rcap y) trl
                 rs (rs + len) (Some t) d pathc).
        split.
        -- assumption.
        -- split.
           ++ now right.
           ++ split.
              ** assumption.
              ** split.
                 --- lia.
                 --- split.
                     +++ (* the keys of reason clause j *)
                         intros k Hk. exists (nth (k - rs) (tget (rcl y) j) (Pos 0%nat)).
                         split.
                         *** replace k with (rs + (k - rs))%nat at 1 by lia.
                             apply Htrl.
                             ---- assumption.
                             ---- unfold len in Hk. lia.
                         *** apply (Hatoms j).
                             ---- assumption.
                             ---- apply nth_In. unfold len in Hk. lia.
                     +++ split.
                         *** intros y' Heq. injection Heq as <-. assumption.
                         *** split.
                             ---- assumption.
                             ---- split.
                                  ++++ assumption.
                                  ++++ assumption.
      * intros m' v Hpost. normal.
        (* The keys read back are reason clause j. *)
        assert (Hys: map (fun (k: nat) => lit_of (trl k)) (seq rs (rs + len - rs))
                     = tget (rcl y) j).
        { replace (rs + len - rs)%nat with len by lia. apply map_lit_of_seq.
          intros k Hk. apply Htrl.
          - assumption.
          - assumption. }
        rewrite Hys in Hpost.
        destruct (add_lits (lvl y) d (nvars y) (Some t) (tget (rcl y) j) (mrk y) lt
          pathc)
          as [[mk' lt'] r] eqn:Hadd_lits.
        destruct Hpost as (-> & HRep' & Hun).
        eapply exec_return.
        -- ev.
        -- ret. exists (vint (enc_count r)). split.
           ++ apply result_int.
           ++ unfold ReasonPost, reason_add, reason_lits. rewrite Hr.
              replace (j <? nr y)%nat with true by (symmetry; now apply Nat.ltb_lt).
              rewrite Hadd_lits. split.
              ** reflexivity.
              ** split.
                 --- assumption.
                 --- assumption.
    + (* reason clause j is not there: return -1; *)
      replace (zcmp Clt (- (Z.of_nat j + 1)) (- Z.of_nat (nr y))) with true
        by (cbn [zcmp]; symmetry; apply Z.ltb_lt; lia).
      cbv beta iota. eapply exec_return.
      * ev.
      * ret. exists (vint (-1)). split.
        -- apply result_int.
        -- apply reason_post_none.
           ++ assumption.
           ++ unfold reason_lits. rewrite Hr.
              replace (j <? nr y)%nat with false by (symmetry; now apply Nat.ltb_ge).
              reflexivity.
Qed.

(* add_reason_lits reads the reason of t and adds the literals of its clause:

     {{ RepL m S N lss y lims lt /\ extract t < N /\ d <= N /\ pathc <= N }}
       int r = s->rsn[t >> 1];
       if (r > 0) { ... }                                         (reason_input_correct)
       if (r < 0) { ... }                                        (reason_learnt_correct)
       return -1;
     {{ ReasonPost: r = 0, no reason }}                                (reason_post_none)

   An input clause has a positive r and a reason clause a negative one, by enc_reason. *)
Lemma add_reason_lits_correct {lt: list Lit}: forall (S: Shape) (N: nat)
  (lss: list (list Lit)) (y: Ctx) (lims: list nat) (t: Lit) (d pathc: nat),
  {{ m | RepL m S N lss y lims lt /\ (extract t < N)%nat /\ (d <= N)%nat /\
         (pathc <= N)%nat }}
    f_add_reason_lits(sptr S, vint (key t), vint (Z.of_nat d), vint (Z.of_nat pathc))
  {{ m', v | ReasonPost S N lss y lims lt t d pathc m m' v }}.
Proof.
  intros S N lss y lims t d pathc m (HRep & Ht & Hd & Hp).
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_lss_small _ _ _ _ _ _ _ HRep) as Hlss.
  pose proof (r_rsn _ _ _ _ _ _ _ HRep) as Frsn.
  pose proof (a_rsn _ _ _ _ _ _ _ HRep) as Arsn.
  pose proof (r_rsn_below _ _ _ _ _ _ _ HRep (extract t) Ht) as Hbelow.
  pose proof (key_small t N Ht HN) as Hkt.
  assert (Hshr: Int.shr (Int.repr (key t)) (Int.repr 1)
                = Int.repr (Z.of_nat (extract t))).
  { apply shr_key. lia. }
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_add_reason_lits. cbn [fn_body fn_return].
    (* int r = s->rsn[t >> 1]; *)
    run.
    destruct (tget (rsn y) (extract t)) as [|i|j] eqn:Hr; cbn [enc_reason ReasonBelow]
      in *.
    + (* no reason: neither branch, return -1; *)
      eapply (exec_if_cmp _ _ _ Cgt).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * cbn [zcmp]. replace (0 <? 0) with false by reflexivity. cbv beta iota.
        apply exec_skip. normal. run. eapply (exec_if_cmp _ _ _ Clt).
        -- ev.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- unfold Small. lia.
        -- unfold Small. lia.
        -- cbn [zcmp]. replace (0 <? 0) with false by reflexivity. cbv beta iota.
           apply exec_skip. normal. eapply exec_return.
           ++ ev.
           ++ exists (vint (-1)). split.
              ** apply result_int.
              ** apply reason_post_none.
                 --- assumption.
                 --- unfold reason_lits. rewrite Hr. reflexivity.
    + (* input clause i: r = i + 1 > 0 *)
      eapply (exec_if_cmp _ _ _ Cgt).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * replace (zcmp Cgt (Z.of_nat i + 1) 0) with true
          by (cbn [zcmp]; symmetry; apply Z.ltb_lt; lia).
        cbv beta iota.
        apply (reason_input_correct S N lss y lims t d pathc i).
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- tmp.
        -- tmp.
        -- tmp.
        -- tmp.
        -- tmp.
    + (* reason clause j: r = -(j + 1) < 0 *)
      eapply (exec_if_cmp _ _ _ Cgt).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * replace (zcmp Cgt (- (Z.of_nat j + 1)) 0) with false
          by (cbn [zcmp]; symmetry; apply Z.ltb_ge; lia).
        cbv beta iota. apply exec_skip. normal. run.
        eapply (exec_if_cmp _ _ _ Clt).
        -- ev.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- unfold Small. lia.
        -- unfold Small. lia.
        -- replace (zcmp Clt (- (Z.of_nat j + 1)) 0) with true
             by (cbn [zcmp]; symmetry; apply Z.ltb_lt; lia).
           cbv beta iota.
           apply (reason_learnt_correct S N lss y lims t d pathc j).
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ tmp.
Qed.

Lemma add_reason_lits_fun: exists (b: block),
  Genv.find_symbol ge _add_reason_lits = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_add_reason_lits).
Proof. apply find_fun. reflexivity. Qed.
