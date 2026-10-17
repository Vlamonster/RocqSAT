(* analyze analyses a conflict: the counting analysis of MiniSat (analyze). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Heur Propagate Analysis Step.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep RepReasons AddLits
  PrevMarked UnmarkRange AddReasonLits.
Import ListNotations.

Section Model.
  (* Positions found by prev_marked are at most where it starts. *)
  Lemma prev_marked_le: forall (tr: Table Lit) (mk: Table bool) (lo n idx: nat),
    (prev_marked tr mk lo idx n <= idx)%nat.
  Proof.
    intros tr mk lo n. induction n as [|n IH]; intros idx; cbn [prev_marked].
    - lia.
    - destruct (tget mk (lit_key (¬tget tr (idx - 1)))).
      + lia.
      + specialize (IH (idx - 1)%nat). lia.
  Qed.

  (* A count add_lits gives stays within its bound. *)
  Lemma add_lits_count_le: forall (lv: Table nat) (d bound: nat) (t: option Lit)
    (ys: list Lit) (mk mk': Table bool) (lt lt': list Lit) (h h': Heur) (p q: nat),
    add_lits lv d bound t ys mk lt h p = (mk', lt', h', Some q) -> (p <= bound)%nat ->
    (q <= bound)%nat.
  Proof.
    intros lv d bound t ys. induction ys as [|y ys IH];
      intros mk mk' lt lt' h h' p q Hadd Hp; cbn [add_lits] in Hadd.
    - injection Hadd as _ _ _ <-. assumption.
    - destruct (is_lit t y || tget mk (lit_key y)).
      + apply (IH mk mk' lt lt' h h' p q Hadd Hp).
      + destruct (Nat.eqb (tget lv (extract y)) d).
        * destruct (Nat.leb_spec bound p) as [Hle | Hgt].
          -- discriminate.
          -- apply (IH _ mk' lt lt' _ h' (Datatypes.S p) q Hadd). lia.
        * destruct (bound <=? length lt)%nat.
          -- discriminate.
          -- apply (IH _ mk' _ lt' _ h' p q Hadd Hp).
  Qed.

  (* So does the count of reason_add. *)
  Lemma reason_add_count_le: forall (y: Ctx) (t: Lit) (d: nat) (lt lt': list Lit)
    (mk': Table bool) (h': Heur) (p q: nat),
    reason_add y t d lt p = (mk', lt', h', Some q) -> (p <= nvars y)%nat ->
      (q <= nvars y)%nat.
  Proof.
    intros y t d lt lt' mk' h' p q Hadd Hp. unfold reason_add in Hadd.
    destruct (reason_lits y (tget (rsn y) (extract t))) as [ys|].
    - apply (add_lits_count_le _ _ _ _ _ _ _ _ _ _ _ _ _ Hadd Hp).
    - discriminate.
  Qed.

  (* The reasons do not depend on the marks or the heuristic. *)
  Lemma reason_lits_heur: forall (x: Ctx) (mk: Table bool) (h: Heur) (r: Reason),
    reason_lits (with_heur (set_mrk x mk) h) r = reason_lits x r.
  Proof. intros x mk h r. destruct r; reflexivity. Qed.

  (* The reasons do not depend on the heuristic of the context. *)
  Lemma reason_lits_with_heur: forall (x: Ctx) (h0: Heur) (r: Reason),
    reason_lits (with_heur x h0) r = reason_lits x r.
  Proof. intros x h0 r. destruct r; reflexivity. Qed.

  (* The analysis reads the heuristic only from its argument, not from the context. *)
  Lemma analyze_loop_heur: forall (x: Ctx) (h0: Heur) (d lo fuel idx: nat)
    (mk: Table bool) (lt: list Lit) (h: Heur) (p: nat),
    analyze_loop (with_heur x h0) d lo fuel idx mk lt h p =
      analyze_loop x d lo fuel idx mk lt h p.
  Proof.
    intros x h0 d lo fuel. induction fuel as [|fuel IH]; intros idx mk lt h p.
    - reflexivity.
    - cbn [analyze_loop]. rewrite reason_lits_with_heur. cbn [with_heur tr rsn lvl nvars].
      destruct (Nat.eqb p 0).
      + reflexivity.
      + destruct (prev_marked (tr x) mk lo idx (idx - lo) <=? lo)%nat.
        * reflexivity.
        * destruct (Nat.eqb p 1).
          -- reflexivity.
          -- destruct (reason_lits x _) as [ys|].
             ++ destruct (add_lits _ _ _ _ ys _ lt h (p - 1)) as [[[mk2 lt2] h2] [q|]].
                ** apply IH.
                ** reflexivity.
             ++ reflexivity.
  Qed.

  Lemma analyze_heur: forall (x: Ctx) (h0 h: Heur) (i d lo: nat),
    analyze (with_heur x h0) h i d lo = analyze x h i d lo.
  Proof.
    intros x h0 h i d lo. unfold analyze. cbn [with_heur cmap lvl nvars mrk tr tlen].
    destruct (tget (cmap x) i) as [ls|].
    - destruct (add_lits _ _ _ _ ls _ [] h 0) as [[[mk lt] h1] [p|]].
      + apply analyze_loop_heur.
      + reflexivity.
    - reflexivity.
  Qed.

  Variables (x: Ctx) (d lo: nat).

  (* Without fuel or without a count, the analysis ends: no literal to assert, and the
     marks of level d from idx down are cleared. *)
  Lemma analyze_loop_stop: forall (fuel idx: nat) (mk: Table bool) (lt: list Lit)
    (h: Heur) (p: nat), (fuel = 0 \/ p = 0)%nat ->
    analyze_loop x d lo fuel idx mk lt h p =
      (None, unmark_range (tr x) mk idx (idx - lo), lt, h).
  Proof.
    intros fuel idx mk lt h p [-> | ->].
    - reflexivity.
    - destruct fuel; reflexivity.
  Qed.

  (* With a count and fuel, the newest marked position idx1 decides: none above lo ends
     the analysis, ... *)
  Lemma analyze_loop_low: forall (f idx: nat) (mk: Table bool) (lt: list Lit) (h: Heur)
    (p: nat),
    (prev_marked (tr x) mk lo idx (idx - lo) <= lo)%nat ->
    analyze_loop x d lo (Datatypes.S f) idx mk lt h (Datatypes.S p) =
      (None, unmark_range (tr x) mk (prev_marked (tr x) mk lo idx (idx - lo))
               (prev_marked (tr x) mk lo idx (idx - lo) - lo), lt, h).
  Proof.
    intros f idx mk lt h p Hlow. cbn [analyze_loop].
    replace (prev_marked (tr x) mk lo idx (idx - lo) <=? lo)%nat with true
      by (symmetry; now apply Nat.leb_le).
    reflexivity.
  Qed.

  (* ... the last literal of level d gives the literal to assert, ... *)
  Lemma analyze_loop_found: forall (f idx: nat) (mk: Table bool) (lt: list Lit) (h: Heur),
    (lo < prev_marked (tr x) mk lo idx (idx - lo))%nat ->
    analyze_loop x d lo (Datatypes.S f) idx mk lt h 1 =
      (Some (¬tget (tr x) (prev_marked (tr x) mk lo idx (idx - lo) - 1)), mk, lt, h).
  Proof.
    intros f idx mk lt h Hhigh. cbn [analyze_loop].
    replace (prev_marked (tr x) mk lo idx (idx - lo) <=? lo)%nat with false
      by (symmetry; now apply Nat.leb_gt).
    reflexivity.
  Qed.

  (* ... and otherwise the analysis goes on with the literals of the reason of t, the
     literal at idx1 - 1, unmarked. *)
  Lemma analyze_loop_step: forall (f idx: nat) (mk: Table bool) (lt: list Lit) (h: Heur)
    (p idx1: nat) (t: Lit),
    idx1 = prev_marked (tr x) mk lo idx (idx - lo) -> t = tget (tr x) (idx1 - 1) ->
    (lo < idx1)%nat ->
    analyze_loop x d lo (Datatypes.S f) idx mk lt h (Datatypes.S (Datatypes.S p)) =
      match reason_add (with_heur (set_mrk x (tset mk (lit_key (¬t)) false)) h) t d lt
              (Datatypes.S p) with
      | (mk2, lt2, h2, Some q) => analyze_loop x d lo f (idx1 - 1) mk2 lt2 h2 q
      | (mk2, lt2, h2, None)   =>
        (None, unmark_range (tr x) mk2 (idx1 - 1) (idx1 - 1 - lo), lt2, h2)
      end.
  Proof.
    intros f idx mk lt h p idx1 t Hidx1 Ht Hhigh. cbn [analyze_loop].
    rewrite <- Hidx1, <- Ht.
    replace (idx1 <=? lo)%nat with false by (symmetry; now apply Nat.leb_gt).
    cbn [Nat.eqb]. replace (Datatypes.S (Datatypes.S p) - 1)%nat with (Datatypes.S p)
      by lia.
    unfold reason_add. rewrite reason_lits_heur.
    cbn [with_heur set_mrk rsn lvl nvars mrk hr].
    destruct (reason_lits x (tget (rsn x) (extract t))) as [ys|].
    - destruct (add_lits (lvl x) d (nvars x) (Some t) ys (tset mk (lit_key (¬t)) false)
                  lt h (Datatypes.S p)) as [[[mk2 lt2] h2] [q|]].
      + reflexivity.
      + reflexivity.
    - reflexivity.
  Qed.
End Model.

(* The blocks the analysis writes: the marks, the lower literals, the fields of s and the
   heuristic, as add_lits does. *)
Definition AnalysisFrame (S: Shape): block -> Z -> Prop := AddKept S.

(* What analyze returns and leaves for the result res of the model, from the memory m of
   the call: the literal to assert or -1, the marks and the lower literals of res, and
   only the blocks of the analysis changed. *)
Definition AnalyzePost (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (res: option Lit * Table bool * list Lit * Heur) (m m': mem)
  (v: val): Prop :=
  match res with
  | (ou, mk, lt, h) =>
    v = vint (enc_lit ou) /\ RepL m' S N lss (with_heur (set_mrk x mk) h) lims lt /\
    (forall (u: Lit), ou = Some u -> (extract u < N)%nat) /\
    Mem.unchanged_on (AnalysisFrame S) m m'
  end.

(* The loop of analyze at count pc tracks the model: with a count p, what is left of the
   analysis is analyze_loop from there; after a failed count (-1), its end. *)
Definition LoopRes (N: nat) (x: Ctx) (d lo fuel idx: nat) (mk: Table bool)
  (lt: list Lit) (h: Heur) (pc: Z) (res: option Lit * Table bool * list Lit * Heur):
  Prop :=
  (exists (p: nat), pc = Z.of_nat p /\ (p <= N)%nat /\
     res = analyze_loop x d lo fuel idx mk lt h p) \/
  (pc = -1 /\ res = (None, unmark_range (tr x) mk idx (idx - lo), lt, h)).

(* The state of the loop of analyze with fuel left, from the memory m of the call: the
   temporaries, the marks mk and lower literals lt in memory, the positions from idx on
   done, and the result res of the model still to come (LoopRes). *)
Record AnalyzeState (m: mem) (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (d lo: nat) (res: option Lit * Table bool * list Lit * Heur)
  (fuel idx: nat) (pc: Z) (mk: Table bool) (lt: list Lit) (h: Heur) (le: temp_env)
  (m1: mem): Prop := {
  as_s: le ! _s = Some (sptr S);
  as_d: le ! _d = Some (vint (Z.of_nat d));
  as_lo: le ! _lo = Some (vint (Z.of_nat lo));
  as_idx: le ! _idx = Some (vint (Z.of_nat idx));
  as_pathc: le ! _pathc = Some (vint pc);
  as_fuel: le ! _fuel = Some (vint (Z.of_nat fuel));
  as_idx_le: (idx <= tlen x)%nat;
  as_fuel_le: (fuel <= tlen x)%nat;
  as_rep: RepL m1 S N lss (with_heur (set_mrk x mk) h) lims lt;
  as_frame: Mem.unchanged_on (AnalysisFrame S) m m1;
  as_res: LoopRes N x d lo fuel idx mk lt h pc res;
}.

Definition analyze_inv (m: mem) (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (d lo: nat) (res: option Lit * Table bool * list Lit * Heur)
  (fuel: nat) (le: temp_env) (m1: mem): Prop :=
  exists (idx: nat) (pc: Z) (mk: Table bool) (lt: list Lit) (h: Heur),
    AnalyzeState m S N lss x lims d lo res fuel idx pc mk lt h le m1.

(* The parts of analyze: its loop, the body of the loop after the test of the fuel, and
   the statements after the loop. *)
Definition analyze_loop_stmt: statement := first_stmt (drop_stmts 3 (fn_body f_analyze)).
Definition analyze_body: statement := drop_stmts 1 (loop_body analyze_loop_stmt).
Definition analyze_end: statement := drop_stmts 4 (fn_body f_analyze).

(* What the body of the loop ends in. *)
Definition AnalyzeK (m: mem) (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (d lo: nat) (res: option Lit * Table bool * list Lit * Heur)
  (fuel: nat): temp_env -> mem -> outcome -> Prop :=
  LoopK Peano.lt (analyze_inv m S N lss x lims d lo res)
    (SeqK ge analyze_end (Returns f_analyze (AnalyzePost S N lss x lims res m))) fuel.

(* The end of the analysis without a literal to assert: the marks of level d left are
   cleared.

     {{ RepL (with_heur (set_mrk x mk) h) lt /\
        res = (None, unmark_range (tr x) mk idx (idx - lo), lt, h) }}
       unmark_range(s, idx, lo);                                  (unmark_range_correct)
       return -1;
     {{ AnalyzePost res }}                                                          *)
Lemma analyze_end_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (d lo: nat) (res: option Lit * Table bool * list Lit * Heur) (idx: nat)
  (mk: Table bool) (lt: list Lit) (h: Heur) (le: temp_env) (m m1: mem),
  RepL m1 S N lss (with_heur (set_mrk x mk) h) lims lt ->
  Mem.unchanged_on (AnalysisFrame S) m m1 -> (idx <= tlen x)%nat -> (lo <= N)%nat ->
  res = (None, unmark_range (tr x) mk idx (idx - lo), lt, h) ->
  le ! _s = Some (sptr S) -> le ! _idx = Some (vint (Z.of_nat idx)) ->
  le ! _lo = Some (vint (Z.of_nat lo)) ->
  Exec ge le m1 analyze_end (Returns f_analyze (AnalyzePost S N lss x lims res m)).
Proof.
  intros S N lss x lims d lo res idx mk lt h le m m1 HRep Hun Hidx Hlo -> Hs Hidx' Hlo'.
  unfold analyze_end, f_analyze. cbn [fn_body drop_stmts].
  (* unmark_range(s, idx, lo); *)
  run. call unmark_range_fun. eapply call_weaken.
  - apply (unmark_range_correct (lt := lt) S N lss (with_heur (set_mrk x mk) h) lims idx
             lo).
    split.
    + assumption.
    + split.
      * assumption.
      * assumption.
  - intros m2 v [HRep2 Hun2]. normal.
    (* return -1; *)
    eapply exec_return.
    + ev.
    + exists (vint (-1)). split.
      * apply result_int.
      * split.
        -- reflexivity.
        -- split.
           ++ apply HRep2.
           ++ split.
              ** intros u Hu. discriminate.
              ** apply (Mem.unchanged_on_trans _ m m1 m2).
                 --- assumption.
                 --- apply (Mem.unchanged_on_implies _ _ _ _ Hun2).
                     intros b0 ofs [_ [Hb _]] _. assumption.
Qed.

(* A count that is used up or failed ends the analysis. *)
Lemma loop_res_stop: forall (N: nat) (x: Ctx) (d lo fuel idx: nat) (mk: Table bool)
  (lt: list Lit) (h: Heur) (pc: Z) (res: option Lit * Table bool * list Lit * Heur),
  LoopRes N x d lo fuel idx mk lt h pc res -> (fuel = 0%nat \/ pc <= 0) ->
  res = (None, unmark_range (tr x) mk idx (idx - lo), lt, h).
Proof.
  intros N x d lo fuel idx mk lt h pc res [(p & -> & _ & Hres) | (_ & Hres)] Hstop.
  - rewrite Hres. apply analyze_loop_stop. lia.
  - assumption.
Qed.

(* The statements of the body of the loop after the test of the count against 1. *)
Definition analyze_resolve: statement := drop_stmts 6 analyze_body.

(* The rest of a round with count p + 2: t, the literal at idx1 - 1, is of level d but not
   the last one, so it is unmarked and its reason resolved with:

     {{ RepL (with_heur (set_mrk x mk) h) lt /\ pathc = p + 2 /\ t at idx1 - 1, marked }}
       s->mrk[t ^ 1] = 0;                                                (rep_store_mrk)
     {{ RepL y lt, for y = with_heur (set_mrk x (tset mk (lit_key (¬t)) false)) h }}
       idx = idx1 - 1;
       pathc = add_reason_lits(s, t, d, pathc - 1);            (add_reason_lits_correct)
     {{ RepL (with_heur (set_mrk y mk2) h2) lt2, for
        reason_add y t d lt (p + 1) = (mk2, lt2, h2, r) }}
       fuel--;
     {{ AnalyzeState f (idx1 - 1) (enc_count r) mk2 lt2 h2 }}      (analyze_loop_step) *)
Lemma analyze_resolve_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (d lo: nat) (res: option Lit * Table bool * list Lit * Heur)
  (f idx idx1 p: nat) (t: Lit) (mk: Table bool) (lt: list Lit) (h: Heur) (le: temp_env)
  (m m1: mem),
  (d <= N)%nat -> (lo <= N)%nat -> RepL m1 S N lss (with_heur (set_mrk x mk) h) lims lt ->
  Mem.unchanged_on (AnalysisFrame S) m m1 ->
  idx1 = prev_marked (tr x) mk lo idx (idx - lo) -> t = tget (tr x) (idx1 - 1) ->
  (lo < idx1)%nat -> (idx1 <= tlen x)%nat -> (Datatypes.S f <= tlen x)%nat ->
  (Datatypes.S (Datatypes.S p) <= N)%nat ->
  res = analyze_loop x d lo (Datatypes.S f) idx mk lt h (Datatypes.S (Datatypes.S p)) ->
  le ! _s = Some (sptr S) -> le ! _d = Some (vint (Z.of_nat d)) ->
  le ! _lo = Some (vint (Z.of_nat lo)) -> le ! _idx1 = Some (vint (Z.of_nat idx1)) ->
  le ! _t = Some (vint (key t)) ->
  le ! _pathc = Some (vint (Z.of_nat (Datatypes.S (Datatypes.S p)))) ->
  le ! _fuel = Some (vint (Z.of_nat (Datatypes.S f))) ->
  Exec ge le m1 analyze_resolve (AnalyzeK m S N lss x lims d lo res (Datatypes.S f)).
Proof.
  intros S N lss x lims d lo res f idx idx1 p t mk lt h le m m1 Hd Hlo HRep Hun Hidx1 Ht
    Hhigh Hidx1_le Hfuel_le Hp Hres Hs Hd' Hlo' Hidx1' Ht' Hpc' Hfuel'.
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_nvars _ _ _ _ _ _ _ HRep) as Hnv. cbn [with_heur set_mrk nvars] in Hnv.
  assert (Hta: (extract t < N)%nat).
  { pose proof (r_tr_atoms _ _ _ _ _ _ _ HRep (idx1 - 1)%nat) as Hat.
    cbn [with_heur set_mrk tr tlen] in Hat. rewrite Ht. apply Hat. lia. }
  pose proof (key_small t N Hta HN) as Hkt.
  assert (Hk: (lit_key (¬t) < 2 * N)%nat) by (destruct t; cbn in *; lia).
  assert (Hxor: Int.xor (Int.repr (key t)) (Int.repr 1) = Int.repr (key (¬t))).
  { apply xor_key. lia. }
  assert (Hsub: Int.sub (Int.repr (Z.of_nat idx1)) (Int.repr 1)
                = Int.repr (Z.of_nat (idx1 - 1))).
  { rewrite sub_repr. f_equal. lia. }
  assert (Hpc: Int.sub (Int.repr (Z.of_nat (Datatypes.S (Datatypes.S p)))) (Int.repr 1)
               = Int.repr (Z.of_nat (Datatypes.S p))).
  { rewrite sub_repr. f_equal. lia. }
  assert (Hfuel: Int.sub (Int.repr (Z.of_nat (Datatypes.S f))) (Int.repr 1)
                 = Int.repr (Z.of_nat f)).
  { rewrite sub_repr. f_equal. lia. }
  pose proof (r_mrk _ _ _ _ _ _ _ HRep) as Fmrk.
  pose proof (a_mrk _ _ _ _ _ _ _ HRep) as Amrk.
  unfold analyze_resolve, analyze_body, analyze_loop_stmt, f_analyze.
  cbn [fn_body drop_stmts first_stmt loop_body Swhile].
  (* s->mrk[t ^ 1] = 0; *)
  run. eapply exec_store.
  - evl.
  - ev.
  - reflexivity.
  - reflexivity.
  - ofs. bound.
  - ofs. cbn [cast_int_int].
    destruct (arr_storable m1 (b_mrk S) (2 * N) (lit_key (¬t)) _ 0 Amrk Hk) as [m2 Hst2].
    exists m2. split.
    + apply Hst2.
    + normal.
      set (y := with_heur (set_mrk x (tset mk (lit_key (¬t)) false)) h).
      assert (HRep2: RepL m2 S N lss y lims lt).
      { apply (rep_store_mrk m1 m2 S N lss (with_heur (set_mrk x mk) h) lims
                 (lit_key (¬t)) false HRep Hk Hst2). }
      assert (Hun2: Mem.unchanged_on (AnalysisFrame S) m m2).
      { apply (store_unchanged _ m m1 m2 Mint32 (b_mrk S) _ _ Hun Hst2).
        intros i [_ [Hb _]]. apply Hb. reflexivity. }
      (* idx = idx1 - 1; pathc = add_reason_lits(s, t, d, pathc - 1); *)
      run. call add_reason_lits_fun. cbn [cast_int_int]. rewrite Hpc. eapply call_weaken.
      * apply (add_reason_lits_correct (lt := lt) S N lss y lims t d (Datatypes.S p)).
        split.
        -- assumption.
        -- split.
           ++ assumption.
           ++ split.
              ** assumption.
              ** lia.
      * intros m3 v Hpost. normal. unfold ReasonPost in Hpost.
        destruct (reason_add y t d lt (Datatypes.S p)) as [[[mk2 lt2] h2] r] eqn:Hadd.
        destruct Hpost as (-> & HRep3 & Hun3).
        (* fuel--; and the loop goes on *)
        run. ints. apply loopk_next with f.
        -- lia.
        -- exists (idx1 - 1)%nat, (enc_count r), mk2, lt2, h2. constructor.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ lia.
           ++ lia.
           ++ apply HRep3.
           ++ apply (Mem.unchanged_on_trans _ m m2 m3).
              ** assumption.
              ** apply Hun3.
           ++ (* the model goes on with the reason of t *)
              rewrite Hres, (analyze_loop_step x d lo f idx mk lt h p idx1 t Hidx1 Ht
                Hhigh).
              fold y. rewrite Hadd. destruct r as [q|].
              ** left. exists q. split.
                 --- reflexivity.
                 --- split.
                     +++ rewrite <- Hnv.
                         apply (reason_add_count_le y t d lt lt2 mk2 h2 (Datatypes.S p) q
                           Hadd).
                         cbn [y with_heur set_mrk nvars]. lia.
                     +++ reflexivity.
              ** right. split.
                 --- reflexivity.
                 --- reflexivity.
Qed.

(* One round of the loop of analyze, with fuel f + 1 and count pc:

     {{ AnalyzeState (f + 1) idx pc mk lt }}
       if (pathc <= 0) break;                                           (loop_res_stop)
       int idx1 = prev_marked(s, idx, lo);                         (prev_marked_correct)
       idx = idx1;
       if (idx1 <= lo) break;                                        (analyze_loop_low)
       int t = s->tr[idx1 - 1];
       if (pathc == 1) return t ^ 1;                               (analyze_loop_found)
     {{ AnalyzePost: the last literal of level d gives ¬t }}
       s->mrk[t ^ 1] = 0;                                                (rep_store_mrk)
       idx = idx1 - 1;
       pathc = add_reason_lits(s, t, d, pathc - 1);            (add_reason_lits_correct)
       fuel--;                                                      (analyze_loop_step)
     {{ AnalyzeState f (idx1 - 1) pathc mk2 lt2 }}

   A break ends the loop with the end of the analysis (analyze_end_correct). *)
Lemma analyze_body_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (d lo: nat) (res: option Lit * Table bool * list Lit * Heur)
  (f idx: nat) (pc: Z) (mk: Table bool) (lt: list Lit) (h: Heur) (le: temp_env)
  (m m1: mem),
  (d <= N)%nat -> (lo <= N)%nat ->
  AnalyzeState m S N lss x lims d lo res (Datatypes.S f) idx pc mk lt h le m1 ->
  Exec ge le m1 analyze_body (AnalyzeK m S N lss x lims d lo res (Datatypes.S f)).
Proof.
  intros S N lss x lims d lo res f idx pc mk lt h le m m1 Hd Hlo
    [Hs Hd' Hlo' Hidx' Hpc' Hfuel' Hidx Hfuel HRep Hun Hres].
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_nvars _ _ _ _ _ _ _ HRep) as Hnv. cbn [with_heur set_mrk nvars] in Hnv.
  pose proof (r_tlen_le _ _ _ _ _ _ _ HRep) as Htlen.
  cbn [with_heur set_mrk tlen] in Htlen.
  unfold analyze_body, analyze_loop_stmt, f_analyze.
  cbn [fn_body drop_stmts first_stmt loop_body Swhile].
  (* if (pathc <= 0) break; *)
  apply exec_seq. eapply (exec_if_cmp _ _ _ Cle _ _ pc 0).
  - ev.
  - ev.
  - reflexivity.
  - reflexivity.
  - destruct Hres as [(p & -> & Hp & _) | (-> & _)].
    + unfold Small. lia.
    + unfold Small. lia.
  - unfold Small. lia.
  - cbn [zcmp]. destruct (Z.leb_spec pc 0) as [Hle | Hgt].
    + (* no count: break; and the end *)
      cbv beta iota. apply exec_break. abrupt. apply loopk_break. normal.
      apply (analyze_end_correct S N lss x lims d lo res idx mk lt h le m m1).
      * assumption.
      * assumption.
      * assumption.
      * assumption.
      * apply (loop_res_stop N x d lo (Datatypes.S f) idx mk lt h pc res Hres). now right.
      * assumption.
      * assumption.
      * assumption.
    + destruct Hres as [(p & -> & Hp & Hres) | (-> & _)].
      2: lia.
      destruct p as [|p0].
      { lia. }
      cbv beta iota. apply exec_skip. normal.
      (* int idx1 = prev_marked(s, idx, lo); idx = idx1; *)
      run. call prev_marked_fun. eapply call_weaken.
      * apply (prev_marked_correct (lt := lt) S N lss (with_heur (set_mrk x mk) h) lims
                 idx lo).
        split.
        -- assumption.
        -- split.
           ++ assumption.
           ++ assumption.
      * intros m' v [-> ->]. normal. cbn [with_heur set_mrk tr mrk].
        set (idx1 := prev_marked (tr x) mk lo idx (idx - lo)).
        pose proof (prev_marked_le (tr x) mk lo (idx - lo) idx) as Hidx1. fold idx1 in
          Hidx1.
        run.
        (* if (idx1 <= lo) break; *)
        eapply (exec_if_cmp _ _ _ Cle).
        -- ev.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- unfold Small. lia.
        -- unfold Small. lia.
        -- cbn [zcmp]. destruct (Nat.leb_spec idx1 lo) as [Hlow | Hhigh].
           ++ (* nothing marked above lo: break; and the end *)
              replace (Z.of_nat idx1 <=? Z.of_nat lo) with true
                by (symmetry; apply Z.leb_le; lia).
              cbv beta iota. apply exec_break. abrupt. apply loopk_break. normal.
              apply (analyze_end_correct S N lss x lims d lo res idx1 mk lt h).
              ** assumption.
              ** assumption.
              ** lia.
              ** assumption.
              ** rewrite Hres. apply analyze_loop_low. assumption.
              ** tmp.
              ** tmp.
              ** tmp.
           ++ replace (Z.of_nat idx1 <=? Z.of_nat lo) with false
                by (symmetry; apply Z.leb_gt; lia).
              (* t, the literal at idx1 - 1, has its negation marked *)
              set (t := tget (tr x) (idx1 - 1)).
              assert (Ht: (extract t < N)%nat).
              { pose proof (r_tr_atoms _ _ _ _ _ _ _ HRep (idx1 - 1)%nat) as Hat.
                cbn [with_heur set_mrk tr tlen] in Hat. apply Hat. lia. }
              pose proof (key_small t N Ht HN) as Hkt.
              assert (Hneg: (extract (¬t) < N)%nat) by (destruct t; cbn in *; lia).
              assert (Hxor: Int.xor (Int.repr (key t)) (Int.repr 1)
                            = Int.repr (key (¬t))).
              { apply xor_key. lia. }
              assert (Hsub: Int.sub (Int.repr (Z.of_nat idx1)) (Int.repr 1)
                            = Int.repr (Z.of_nat (idx1 - 1))).
              { rewrite sub_repr. f_equal. lia. }
              pose proof (r_tr _ _ _ _ _ _ _ HRep) as Ftr.
              pose proof (a_tr _ _ _ _ _ _ _ HRep) as Atr.
              cbn [with_heur set_mrk tr] in Atr.
              cbv beta iota. apply exec_skip. normal.
              (* int t = s->tr[idx1 - 1]; *)
              run. fold t.
              (* if (pathc == 1) return t ^ 1; *)
              eapply (exec_if_cmp _ _ _ Ceq).
              ** ev.
              ** ev.
              ** reflexivity.
              ** reflexivity.
              ** unfold Small. lia.
              ** unfold Small. lia.
              ** cbn [zcmp]. destruct p0 as [|p'].
                 --- (* the last literal of level d: return ¬t *)
                     cbv beta iota. eapply exec_return.
                     +++ ev.
                     +++ ret. exists (vint (key (¬t))). split.
                         *** cbn [cast_int_int]. rewrite Hxor. apply result_int.
                         *** rewrite Hres, (analyze_loop_found x d lo) by assumption.
                             fold idx1 t. split.
                             ---- reflexivity.
                             ---- split.
                                  ++++ assumption.
                                  ++++ split.
                                       **** intros u Hu. injection Hu as <-.
                                            assumption.
                                       **** assumption.
                 --- (* more of level d: unmark ¬t and resolve with its reason *)
                     replace (Z.eqb (Z.of_nat (Datatypes.S (Datatypes.S p'))) 1) with
                       false
                       by (symmetry; apply Z.eqb_neq; lia).
                     cbv beta iota. apply exec_skip. normal.
                     apply (analyze_resolve_correct S N lss x lims d lo res f idx idx1
                       p' t
                              mk lt h _ m m1).
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ reflexivity.
                     +++ reflexivity.
                     +++ assumption.
                     +++ lia.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
                     +++ tmp.
Qed.

(* analyze analyses the conflict on clause i at level d, whose last decision is at trail
   position lo:

     {{ RepB m S N lss x lims /\ i < length lss /\ d <= N /\ lo <= N }}
       int idx = s->tlen;
       int pathc = add_lits(s, s->clits, s->cstart[i], s->cstart[i + 1], -1, d, 0);
                                                                     (add_lits_correct)
       int fuel = s->tlen;
     {{ analyze_inv (tlen x): LoopRes of analyze x i d lo }}
       while (fuel > 0) { ... }        (invariant analyze_inv; analyze_body_correct)
     {{ fuel = 0: the end of the analysis }}                           (loop_res_stop)
       unmark_range(s, idx, lo); return -1;                     (analyze_end_correct)
     {{ AnalyzePost (analyze x i d lo) }}

   The loop ends: the fuel decreases. *)
Lemma analyze_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (i d lo: nat),
  {{ m | RepB m S N lss x lims /\ (i < length lss)%nat /\ (d <= N)%nat /\
         (lo <= N)%nat }}
    f_analyze(sptr S, vint (Z.of_nat i), vint (Z.of_nat d), vint (Z.of_nat lo))
  {{ m', v | AnalyzePost S N lss x lims (analyze x (hr x) i d lo) m m' v }}.
Proof.
  intros S N lss x lims i d lo m (HRep & Hi & Hd & Hlo).
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_nvars _ _ _ _ _ _ _ HRep) as Hnv.
  pose proof (r_tlen_le _ _ _ _ _ _ _ HRep) as Htlen.
  pose proof (r_lss_small _ _ _ _ _ _ _ HRep) as Hlss.
  pose proof (r_tlen _ _ _ _ _ _ _ HRep) as Ftlen.
  pose proof (r_clits _ _ _ _ _ _ _ HRep) as Fcl.
  pose proof (r_cstart _ _ _ _ _ _ _ HRep) as Fcs.
  pose proof (a_starts _ _ _ _ _ _ _ HRep) as Astarts.
  pose proof (a_lits _ _ _ _ _ _ _ HRep) as (tcl & Acl & Hatoms & Hcl).
  destruct (r_starts _ _ _ _ _ _ _ HRep i Hi) as [Hsi Hsn].
  assert (Hadd1: Int.add (Int.repr (Z.of_nat i)) (Int.repr 1)
                 = Int.repr (Z.of_nat (Datatypes.S i))).
  { apply incr_nat. lia. }
  remember (analyze x (hr x) i d lo) as res eqn:Hres.
  unfold analyze in Hres. rewrite (Hcl i Hi) in Hres.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_analyze. cbn [fn_body fn_return].
    (* int idx = s->tlen; int pathc = add_lits(...); *)
    run. call add_lits_fun. eapply call_weaken.
    + apply (add_lits_correct (lt := []) S N lss x lims (b_clits S) (nclits S) tcl
               (starts S i) (starts S (Datatypes.S i)) None d 0).
      split.
      * assumption.
      * split.
        -- now left.
        -- split.
           ++ assumption.
           ++ split.
              ** lia.
              ** split.
                 --- intros k Hk. apply Hatoms. lia.
                 --- split.
                     +++ intros y Hy. discriminate.
                     +++ split.
                         *** assumption.
                         *** split.
                             ---- lia.
                             ---- apply (r_nclits_small _ _ _ _ _ _ _ HRep).
    + intros m1 v Hpost. normal.
      destruct
                  (add_lits (lvl x) d (nvars x) None (map (fun (k: nat) => lit_of
                    (tcl k))
                     (seq (starts S i) (starts S (Datatypes.S i) - starts S i)))
                  (mrk x) [] (hr x) 0) as [[[mk lt] h] r] eqn:Hadd.
      destruct Hpost as (-> & HRep1 & Hun1). keep_mem m1.
      pose proof (r_tlen _ _ _ _ _ _ _ HRep1) as Ftlen1.
      (* int fuel = s->tlen; *)
      run. unfold Swhile.
      apply exec_loop with (R := Peano.lt) (I := analyze_inv m S N lss x lims d lo res)
        (a := tlen x).
      * apply lt_wf.
      * intros fuel le1 m2 (idx & pc & mk' & lt' & h' & HS).
        pose proof HS as [Hs Hd' Hlo' Hidx' _ Hfuel' Hidx Hfuel HRep2 Hun2 Hres2].
        (* while (fuel > 0) *)
        apply exec_seq. eapply (exec_if_cmp _ _ _ Cgt).
        -- ev.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- unfold Small. lia.
        -- unfold Small. lia.
        -- destruct fuel as [|f].
           ++ (* no fuel: break; and the end *)
              replace (zcmp Cgt (Z.of_nat 0) 0) with false by reflexivity.
              cbv beta iota. apply exec_break. abrupt. apply loopk_break. normal.
              apply (analyze_end_correct S N lss x lims d lo res idx mk' lt' h' le1 m m2).
              ** assumption.
              ** assumption.
              ** assumption.
              ** assumption.
              ** apply (loop_res_stop N x d lo 0 idx mk' lt' h' pc res Hres2). now left.
              ** assumption.
              ** assumption.
              ** assumption.
           ++ replace (zcmp Cgt (Z.of_nat (Datatypes.S f)) 0) with true
                by (cbn [zcmp]; symmetry; apply Z.ltb_lt; lia).
              cbv beta iota. apply exec_skip. normal.
              apply (analyze_body_correct S N lss x lims d lo res f idx pc mk' lt' h' le1
                       m m2).
              ** assumption.
              ** assumption.
              ** assumption.
      * (* The invariant holds at the end of the trail, after the conflict clause. *)
        exists (tlen x), (enc_count r), mk, lt, h. constructor.
        -- tmp.
        -- tmp.
        -- tmp.
        -- tmp.
        -- tmp.
        -- tmp.
        -- lia.
        -- lia.
        -- assumption.
        -- apply Hun1.
        -- rewrite Hres. destruct r as [p|].
           ++ left. exists p. split.
              ** reflexivity.
              ** split.
                 --- rewrite <- Hnv.
                     apply (add_lits_count_le _ _ _ _ _ _ _ _ _ _ _ 0 p Hadd). lia.
                 --- reflexivity.
           ++ right. split.
              ** reflexivity.
              ** reflexivity.
Qed.

Lemma analyze_fun: exists (b: block),
  Genv.find_symbol ge _analyze = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_analyze).
Proof. apply find_fun. reflexivity. Qed.
