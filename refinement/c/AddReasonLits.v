(* add_reason_lits adds the literals of the reason of a trail literal to the analysis
   (reason_lits, then add_lits, as in analyze_loop). *)
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
From RocqSAT.refinement Require Import Tactics.
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
From RocqSAT.refinement.c Require Import RepReasons.
From RocqSAT.refinement.c Require Import AddLits.

(* What analyze_loop does with the reason of the trail literal t: add the literals of its
   clause other than t, or stop if it has none. *)
Definition reason_add (y: Ctx) (t: Lit) (d pathc: nat): Ctx * option nat :=
match reason_lits y (tget (rsn y) (extract t)) with
| None    => (y, None)
| Some ys => add_lits y d (Some t) ys pathc
end.

(* What add_reason_lits returns and leaves, from the memory m of the call: the count of
   reason_add or -1, and the context it gives; m' is m on AddFrame. *)
Definition ReasonPost (sh: Shape) (N: nat) (lss: list (list Lit)) (y: Ctx) (t: Lit)
  (d pathc: nat) (m m': mem) (v: val): Prop :=
  match reason_add y t d pathc with
  | (y', r) =>
    v = vint (enc_count r) /\ RepL m' sh N lss y' /\ Mem.unchanged_on (AddFrame sh) m m'
  end.

(* Without a reason clause, nothing changes and the result is -1. *)
Lemma reason_post_none: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (y: Ctx) (t: Lit) (d pathc: nat) (m: mem),
  RepL m sh N lss y -> reason_lits y (tget (rsn y) (extract t)) = None ->
  ReasonPost sh N lss y t d pathc m m (vint (-1)).
Proof.
  intros sh N lss y t d pathc m HRep Hnone. unfold ReasonPost, reason_add.
  rewrite Hnone. splits.
  - reflexivity.
  - assumption.
  - frame.
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
    + apply IH. intros k Hk. replace (S b + k)%nat with (b + S k)%nat
        by lia.
      apply (Ht (S k)). cbn. lia.
Qed.

(* The branches of add_reason_lits for an input clause and for a reason clause. *)
Definition input_branch: statement :=
  then_stmt (first_stmt (drop_stmts 1 (fn_body f_add_reason_lits))).
Definition learnt_branch: statement :=
  then_stmt (first_stmt (drop_stmts 2 (fn_body f_add_reason_lits))).

(* The temporaries both branches read: s, t, d and pathc. *)
Record ReasonTemps (sh: Shape) (t: Lit) (d pathc: nat) (le: temp_env): Prop := {
  rt_s: le ! _s = Some (sptr sh);
  rt_t: le ! _t = Some (vint (key t));
  rt_d: le ! _d = Some (vnat d);
  rt_pathc: le ! _pathc = Some (vnat pathc);
}.

(* The reason of t is input clause i (r = i + 1), one of the clauses as RepL says: add
   its literals, from cstart[i] to cstart[i + 1] in clits:

     {{ RepL y /\ r = i + 1 /\ i < ncl }}
       if (r > s->ncl) return -1;
       return add_lits(s, s->clits, s->cstart[r - 1], s->cstart[r], t, d, pathc);
     {{ ReasonPost, as reason_lits gives clause i }}                (add_lits_correct) *)
Lemma input_branch_correct: forall (sh: Shape) (N: nat)
  (lss: list (list Lit)) (y: Ctx) (t: Lit) (d pathc i: nat)
  (rest: statement) (le: temp_env) (m: mem),
  RepL m sh N lss y -> tget (rsn y) (extract t) = input i ->
  (i < length lss)%nat -> (extract t < N)%nat -> (d <= N)%nat -> (pathc <= N)%nat ->
  ReasonTemps sh t d pathc le -> le ! _r = Some (vint (Z.of_nat i + 1)) ->
  Exec ge le m input_branch
    (SeqK ge rest (Returns f_add_reason_lits (ReasonPost sh N lss y t d pathc m))).
Proof.
  intros sh N lss y t d pathc i rest le m HRep Hr Hi Ht Hd Hp [Hs Ht' Hd' Hp'] Hr'.
  pose proof (r_n HRep) as HN.
  pose proof (r_lss_small HRep) as Hlss.
  pose proof (r_ncl HRep) as Fncl.
  pose proof (r_cstart HRep) as Fcs.
  pose proof (a_starts HRep) as Astarts.
  pose proof (r_clits HRep) as Fcl.
  pose proof (a_lits HRep) as (tcl & Acl & Hatoms & Hcl).
  replace (Z.of_nat i + 1) with (Z.of_nat (S i)) in Hr' by lia.
  unfold input_branch, f_add_reason_lits. cbn [fn_body drop_stmts first_stmt then_stmt].
  (* if (r > s->ncl) return -1; *)
  run. branch.
  - (* clause i is not there: impossible, as i < length lss *)
    intros Hgt. lia.
  - (* clause i is there: add its literals *)
    intros Hle. destruct (r_starts HRep i Hi) as [Hsi Hsn].
    assert (Hsub: Int.sub (Int.repr (Z.of_nat (S i))) (Int.repr 1)
                  = Int.repr (Z.of_nat i)).
    { rewrite sub_repr. f_equal. lia. }
    apply exec_skip. normal.
    (* return add_lits(s, s->clits, s->cstart[r - 1], s->cstart[r], t, d, pathc); *)
    run.
    call add_lits_fun
      (add_lits_correct sh N lss y (b_clits sh) (nclits sh) tcl (starts sh i)
         (starts sh (S i)) (Some t) d pathc).
    + splits.
      * apply HRep.
      * now left.
      * assumption.
      * lia.
      * intros k Hk. apply Hatoms. lia.
      * intros y' Heq. injection Heq as <-. assumption.
      * assumption.
      * assumption.
      * apply (r_nclits_small HRep).
    + intros m' v Hpost. normal.
      destruct (add_lits y d (Some t) (span_lits tcl (starts sh i) (starts sh (S i)))
                  pathc) as [y' r] eqn:Hadd.
      destruct Hpost as (-> & HRep' & Hun).
      return_int.
      unfold ReasonPost, reason_add, reason_lits. rewrite Hr, (Hcl i Hi).
      fold (span_lits tcl (starts sh i) (starts sh (S i))). rewrite Hadd. split.
      * reflexivity.
      * split; assumption.
Qed.

(* The reason of t is reason clause j (r = -(j + 1)): add its literals, from rbeg[j] on
   for rlen[j] of them in rlits, if it is one of the nr of them:

     {{ RepL y /\ r = -(j + 1) }}
       if (r < -s->nr) return -1;
     {{ result = -1, as reason clause j is not there: reason_lits gives none }}
       int b = s->rbeg[-r - 1];
       return add_lits(s, s->rlits, b, b + s->rlen[-r - 1], t, d, pathc);
     {{ ReasonPost, as reason_lits gives reason clause j }}         (add_lits_correct) *)
Lemma learnt_branch_correct: forall (sh: Shape) (N: nat)
  (lss: list (list Lit)) (y: Ctx) (t: Lit) (d pathc j: nat)
  (rest: statement) (le: temp_env) (m: mem),
  RepL m sh N lss y -> tget (rsn y) (extract t) = learnt j ->
  (j < N)%nat -> (extract t < N)%nat -> (d <= N)%nat -> (pathc <= N)%nat ->
  ReasonTemps sh t d pathc le -> le ! _r = Some (vint (- (Z.of_nat j + 1))) ->
  Exec ge le m learnt_branch
    (SeqK ge rest (Returns f_add_reason_lits (ReasonPost sh N lss y t d pathc m))).
Proof.
  intros sh N lss y t d pathc j rest le m HRep Hr Hj Ht Hd Hp [Hs Ht' Hd' Hp'] Hr'.
  pose proof (r_n HRep) as HN.
  pose proof (r_nr HRep) as Fnr.
  pose proof (r_nr_le HRep) as Hnr.
  pose proof (r_rcap_small HRep) as Hrcap.
  pose proof (r_rsize_le HRep) as Hsize.
  pose proof (r_rcl_atoms HRep) as Hatoms.
  pose proof (r_rbeg HRep) as Frbeg.
  pose proof (r_rlen HRep) as Frlen.
  pose proof (r_rlits HRep) as Frlits.
  pose proof (a_rbeg HRep) as (tb & Arbeg & Htb).
  pose proof (a_rlen HRep) as (tn & Arlen & Htn).
  pose proof (a_rlits HRep) as (trl & Arlits & Htrl).
  assert (Hneg: Int.neg (Int.repr (Z.of_nat (nr y))) = Int.repr (- Z.of_nat (nr y))).
  { apply Int.neg_repr. }
  unfold learnt_branch, f_add_reason_lits. cbn [fn_body drop_stmts first_stmt then_stmt].
  (* if (r < -s->nr) return -1; *)
  run. eapply (exec_if_lt (- (Z.of_nat j + 1)) (- Z.of_nat (nr y))).
  - ev.
  - (* -s->nr *)
    eapply eval_Eunop.
    + ev.
    + unfold sem_unary_operation, sem_neg. simpl. rewrite Hneg. reflexivity.
  - reflexivity.
  - lia.
  - (* reason clause j is not there: return -1; *)
    intros Hlt. return_int.
    apply reason_post_none.
    + assumption.
    + unfold reason_lits. rewrite Hr.
      replace (j <? nr y)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
      reflexivity.
  - (* reason clause j is there: add its literals *)
    intros Hge. assert (Hjn: (j < nr y)%nat) by lia.
    set (rs := reasons_size (rcl y) j).
    set (len := length (tget (rcl y) j)).
    (* Reason clause j ends within the first nr of them. *)
    assert (Hend: (rs + len <= reasons_size (rcl y) (nr y))%nat).
    { unfold rs, len. change (reasons_size (rcl y) j + length (tget (rcl y) j))%nat
        with (reasons_size (rcl y) (S j)).
      apply reasons_size_le. lia. }
    assert (Hidx: Int.sub (Int.neg (Int.repr (- (Z.of_nat j + 1)))) (Int.repr 1)
                  = Int.repr (Z.of_nat j)).
    { rewrite Int.neg_repr, sub_repr. f_equal. lia. }
    assert (Hadd: Int.add (Int.repr (Z.of_nat rs)) (Int.repr (Z.of_nat len))
                  = Int.repr (Z.of_nat (rs + len))).
    { rewrite add_repr. f_equal. lia. }
    apply exec_skip. normal.
    (* int b = s->rbeg[-r - 1]; *)
    run. rewrite (Htb j Hjn). run. rewrite (Htn j Hjn).
    fold rs len.
    (* return add_lits(s, s->rlits, b, b + s->rlen[-r - 1], t, d, pathc); *)
    eapply (exec_call_triple add_lits_fun
              (add_lits_correct sh N lss y (b_rlits sh) (rcap y) trl
                 rs (rs + len) (Some t) d pathc)).
    + reflexivity.
    + unfold vint. rewrite <- Hadd. evs.
    + split.
      * apply HRep.
      * split.
        -- now right.
        -- split.
           ++ assumption.
           ++ split.
              ** lia.
              ** split.
                 --- (* the keys of reason clause j *)
                     intros k Hk. exists (nth (k - rs) (tget (rcl y) j) (Pos 0%nat)).
                     split.
                     +++ replace k with (rs + (k - rs))%nat at 1 by lia.
                         apply Htrl.
                         *** assumption.
                         *** unfold len in Hk. lia.
                     +++ apply (Hatoms j).
                         *** assumption.
                         *** apply nth_In. unfold len in Hk. lia.
                 --- split.
                     +++ intros y' Heq. injection Heq as <-. assumption.
                     +++ split.
                         *** assumption.
                         *** split; assumption.
    + intros m' v Hpost. normal.
      (* The keys read back are reason clause j. *)
      assert (Hys: span_lits trl rs (rs + len) = tget (rcl y) j).
      { unfold span_lits. replace (rs + len - rs)%nat with len by lia.
        apply map_lit_of_seq.
        intros k Hk. apply Htrl.
        - assumption.
        - assumption. }
      rewrite Hys in Hpost.
      destruct (add_lits y d (Some t) (tget (rcl y) j) pathc) as [y' r] eqn:Hadd_lits.
      destruct Hpost as (-> & HRep' & Hun).
      return_int.
      unfold ReasonPost, reason_add, reason_lits. rewrite Hr.
      replace (j <? nr y)%nat with true by (symmetry; now apply Nat.ltb_lt).
      rewrite Hadd_lits. split.
      * reflexivity.
      * split; assumption.
Qed.

(* add_reason_lits reads the reason of t and adds the literals of its clause:

     {{ RepL m sh N lss y /\ extract t < N /\ d <= N /\ pathc <= N }}
       int r = s->rsn[t >> 1];
       if (r > 0) { ... }                                         (input_branch_correct)
       if (r < 0) { ... }                                        (learnt_branch_correct)
       return -1;
     {{ ReasonPost: r = 0, no reason }}                                (reason_post_none)

   An input clause has a positive r and a reason clause a negative one, by enc_reason. *)
Lemma add_reason_lits_correct: forall (sh: Shape) (N: nat)
  (lss: list (list Lit)) (y: Ctx) (t: Lit) (d pathc: nat),
  {{ m | RepL m sh N lss y /\ (extract t < N)%nat /\ (d <= N)%nat /\
         (pathc <= N)%nat }}
    f_add_reason_lits(sptr sh, vint (key t), vnat d, vnat pathc)
  {{ m', v | ReasonPost sh N lss y t d pathc m m' v }}.
Proof.
  intros sh N lss y t d pathc m (HRep & Ht & Hd & Hp).
  pose proof (r_n HRep) as HN.
  pose proof (r_lss_small HRep) as Hlss.
  pose proof (r_rsn HRep) as Frsn.
  pose proof (a_rsn HRep) as Arsn.
  pose proof (r_rsn_below HRep (extract t) Ht) as Hbelow.
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
      branch.
      * intros Hgt. lia.
      * intros _. apply exec_skip. normal. run. branch.
        -- intros Hlt. lia.
        -- intros _. apply exec_skip. normal. return_int.
           apply reason_post_none.
           ++ assumption.
           ++ unfold reason_lits. rewrite Hr. reflexivity.
    + (* input clause i: r = i + 1 > 0 *)
      branch.
      * intros _. apply (input_branch_correct sh N lss y t d pathc i).
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- constructor; tmp.
        -- tmp.
      * intros Hle. lia.
    + (* reason clause j: r = -(j + 1) < 0 *)
      branch.
      * intros Hgt. lia.
      * intros _. apply exec_skip. normal. run. branch.
        -- intros _. apply (learnt_branch_correct sh N lss y t d pathc j).
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ constructor; tmp.
           ++ tmp.
        -- intros Hge. lia.
Qed.

Lemma add_reason_lits_fun: FunAt _add_reason_lits f_add_reason_lits.
Proof. apply find_fun. reflexivity. Qed.
