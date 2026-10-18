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

  (* The count reason_add gives stays at most the number of atoms. *)
  Lemma reason_add_count_le: forall (y y': Ctx) (t: Lit) (d p q: nat),
    reason_add y t d p = (y', Some q) -> (p <= nvars y)%nat -> (q <= nvars y)%nat.
  Proof.
    intros y y' t d p q Hadd Hp. unfold reason_add in Hadd.
    destruct (reason_lits y (tget (rsn y) (extract t))) as [ys|].
    - apply (add_lits_count_le _ _ Hadd Hp).
    - discriminate.
  Qed.

  (* reason_add leaves the trail. *)
  Lemma reason_add_tlen: forall (y y': Ctx) (t: Lit) (d p: nat) (r: option nat),
    reason_add y t d p = (y', r) -> tlen y' = tlen y.
  Proof.
    intros y y' t d p r Hadd. unfold reason_add in Hadd.
    destruct (reason_lits y (tget (rsn y) (extract t))) as [ys|].
    - apply analysed_tlen. now apply add_lits_analysed in Hadd.
    - now injection Hadd as <- _.
  Qed.
  #[global] Arguments reason_add_tlen {y y' t d p r}.

  Variables (d lo: nat).

  (* Without fuel or without a count, the analysis ends: no literal to assert, and the
     marks of level d from idx down are cleared. *)
  Lemma analyze_loop_stop: forall (y: Ctx) (fuel idx p: nat), (fuel = 0 \/ p = 0)%nat ->
    analyze_loop y d lo fuel idx p = (unmark_range y idx lo, None).
  Proof.
    intros y fuel idx p [-> | ->].
    - reflexivity.
    - destruct fuel; reflexivity.
  Qed.

  (* With a count and fuel, the newest marked position idx1 decides: none above lo ends
     the analysis, ... *)
  Lemma analyze_loop_low: forall (y: Ctx) (f idx p: nat),
    (newest_marked y lo idx <= lo)%nat ->
    analyze_loop y d lo (S f) idx (S p) =
      (unmark_range y (newest_marked y lo idx) lo, None).
  Proof.
    intros y f idx p Hlow. cbn [analyze_loop].
    replace (newest_marked y lo idx <=? lo)%nat with true
      by (symmetry; now apply Nat.leb_le).
    reflexivity.
  Qed.

  (* ... the last literal of level d gives the literal to assert, ... *)
  Lemma analyze_loop_found: forall (y: Ctx) (f idx: nat),
    (lo < newest_marked y lo idx)%nat ->
    analyze_loop y d lo (S f) idx 1 =
      (y, Some (¬tget (tr y) (newest_marked y lo idx - 1))).
  Proof.
    intros y f idx Hhigh. cbn [analyze_loop].
    replace (newest_marked y lo idx <=? lo)%nat with false
      by (symmetry; now apply Nat.leb_gt).
    reflexivity.
  Qed.

  (* ... and otherwise the analysis goes on with the literals of the reason of t, the
     literal at idx1 - 1, unmarked. *)
  Lemma analyze_loop_step: forall (y: Ctx) (f idx p idx1: nat) (t: Lit),
    idx1 = newest_marked y lo idx -> t = tget (tr y) (idx1 - 1) ->
    (lo < idx1)%nat ->
    analyze_loop y d lo (S f) idx (S (S p)) =
      match reason_add (y <| mrk := tset (mrk y) (lit_key (¬t)) false |>) t d (S p) with
      | (y2, Some q) => analyze_loop y2 d lo f (idx1 - 1) q
      | (y2, None)   => (unmark_range y2 (idx1 - 1) lo, None)
      end.
  Proof.
    intros y f idx p idx1 t Hidx1 Ht Hhigh. cbn [analyze_loop].
    rewrite <- Hidx1, <- Ht.
    replace (idx1 <=? lo)%nat with false by (symmetry; now apply Nat.leb_gt).
    cbn [Nat.eqb]. replace (S (S p) - 1)%nat with (S p)
      by lia.
    unfold reason_add. rewrite reason_lits_mrk. cbn [set_mrk rsn].
    destruct (reason_lits y (tget (rsn y) (extract t))) as [ys|].
    - reflexivity.
    - reflexivity.
  Qed.
End Model.

(* What analyze returns and leaves for the result res of the model, from the memory m of
   the call: the literal to assert or -1, and the context of res; m' is m on AddFrame, as
   for add_lits. *)
Definition AnalyzePost (sh: Shape) (N: nat) (lss: list (list Lit)) (res: Ctx * option Lit)
  (m m': mem) (v: val): Prop :=
  match res with
  | (x', ou) =>
    v = vint (enc_lit ou) /\ RepL m' sh N lss x' /\
    OptBelow N ou /\
    Mem.unchanged_on (AddFrame sh) m m'
  end.

(* The loop of analyze at count pc on the current context y tracks the model: with a
   count p, what is left of the analysis is analyze_loop from there; after a failed
   count (-1), its end. *)
Definition LoopRes (N: nat) (y: Ctx) (d lo fuel idx: nat) (pc: Z)
  (res: Ctx * option Lit): Prop :=
  (exists (p: nat), pc = Z.of_nat p /\ (p <= N)%nat /\
     res = analyze_loop y d lo fuel idx p) \/
  (pc = -1 /\ res = (unmark_range y idx lo, None)).

(* The temporaries of the loop of analyze. *)
Record AnalyzeTemps (sh: Shape) (d lo idx: nat) (pc: Z) (fuel: nat) (le: temp_env):
  Prop := {
  at_s: le ! _s = Some (sptr sh);
  at_d: le ! _d = Some (vnat d);
  at_lo: le ! _lo = Some (vnat lo);
  at_idx: le ! _idx = Some (vnat idx);
  at_pathc: le ! _pathc = Some (vint pc);
  at_fuel: le ! _fuel = Some (vnat fuel);
}.

(* The state of the loop of analyze, with the current context y: what is left of the
   model gives res. *)
Record AnalyzeState {m: mem} {sh: Shape} {N: nat} {lss: list (list Lit)}
  {d lo: nat} {res: Ctx * option Lit} {fuel idx: nat} {pc: Z} {y: Ctx} {le: temp_env}
  {m1: mem}: Prop := {
  as_temps: AnalyzeTemps sh d lo idx pc fuel le;
  as_idx_le: (idx <= tlen y)%nat;
  as_fuel_le: (fuel <= tlen y)%nat;
  as_rep: RepL m1 sh N lss y;
  as_frame: Mem.unchanged_on (AddFrame sh) m m1;
  as_res: LoopRes N y d lo fuel idx pc res;
}.
Arguments AnalyzeState : clear implicits.

(* The invariant of the loop of analyze: some state with this fuel. *)
Definition analyze_inv (m: mem) (sh: Shape) (N: nat) (lss: list (list Lit)) (d lo: nat)
  (res: Ctx * option Lit) (fuel: nat) (le: temp_env) (m1: mem): Prop :=
  exists (idx: nat) (pc: Z) (y: Ctx),
    AnalyzeState m sh N lss d lo res fuel idx pc y le m1.

(* The parts of analyze: its loop, the body of the loop after the test of the fuel, and
   the statements after the loop. *)
Definition analyze_loop_stmt: statement := first_stmt (drop_stmts 3 (fn_body f_analyze)).
Definition analyze_body: statement := drop_stmts 1 (loop_body analyze_loop_stmt).
Definition analyze_end: statement := drop_stmts 4 (fn_body f_analyze).

(* What the body of the loop ends in. *)
Definition AnalyzeK (m: mem) (sh: Shape) (N: nat) (lss: list (list Lit)) (d lo: nat)
  (res: Ctx * option Lit) (fuel: nat): temp_env -> mem -> outcome -> Prop :=
  LoopK Peano.lt (analyze_inv m sh N lss d lo res)
    (SeqK ge analyze_end (Returns f_analyze (AnalyzePost sh N lss res m))) fuel.

(* The end of the analysis without a literal to assert: the marks of level d left are
   cleared.

     {{ RepL y /\ res = (unmark_range y idx lo, None) }}
       unmark_range(s, idx, lo);                                  (unmark_range_correct)
       return -1;
     {{ AnalyzePost res }}                                                          *)
Lemma analyze_end_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit)) (lo: nat)
  (res: Ctx * option Lit) (idx: nat) (y: Ctx) (le: temp_env) (m m1: mem),
  RepL m1 sh N lss y -> Mem.unchanged_on (AddFrame sh) m m1 ->
  (idx <= tlen y)%nat -> (lo <= N)%nat -> res = (unmark_range y idx lo, None) ->
  le ! _s = Some (sptr sh) -> le ! _idx = Some (vnat idx) ->
  le ! _lo = Some (vnat lo) ->
  Exec ge le m1 analyze_end (Returns f_analyze (AnalyzePost sh N lss res m)).
Proof.
  intros sh N lss lo res idx y le m m1 HRep Hun Hidx Hlo -> Hs Hidx' Hlo'.
  unfold analyze_end, f_analyze. cbn [fn_body drop_stmts].
  (* unmark_range(s, idx, lo); *)
  run.
  eapply (exec_call_triple_none unmark_range_fun
            (unmark_range_correct sh N lss y idx lo)).
  - reflexivity.
  - evs.
  - split.
    + apply HRep.
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
Lemma loop_res_stop: forall (N: nat) (y: Ctx) (d lo fuel idx: nat) (pc: Z)
  (res: Ctx * option Lit),
  LoopRes N y d lo fuel idx pc res -> (fuel = 0%nat \/ pc <= 0) ->
  res = (unmark_range y idx lo, None).
Proof.
  intros N y d lo fuel idx pc res [(p & -> & _ & Hres) | (_ & Hres)] Hstop.
  - rewrite Hres. apply analyze_loop_stop. lia.
  - assumption.
Qed.

(* The statements of the body of the loop after the test of the count against 1. *)
Definition analyze_resolve: statement := drop_stmts 6 analyze_body.

(* The rest of a round with count p + 2: t, the literal at idx1 - 1, is of level d but not
   the last one, so it is unmarked and its reason resolved with:

     {{ RepL y /\ pathc = p + 2 /\ t at idx1 - 1, marked }}
       s->mrk[t ^ 1] = 0;                                                (rep_store_mrk)
     {{ RepL y1, for y1 = y <| mrk := tset (mrk y) (lit_key (¬t)) false |> }}
       idx = idx1 - 1;
       pathc = add_reason_lits(s, t, d, pathc - 1);            (add_reason_lits_correct)
     {{ RepL y2, for reason_add y1 t d (p + 1) = (y2, r) }}
       fuel--;
     {{ AnalyzeState f (idx1 - 1) (enc_count r) y2 }}              (analyze_loop_step) *)
Lemma analyze_resolve_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (d lo: nat) (res: Ctx * option Lit) (f idx idx1 p: nat) (t: Lit) (y: Ctx)
  (le: temp_env) (m m1: mem),
  (d <= N)%nat -> (lo <= N)%nat -> RepL m1 sh N lss y ->
  Mem.unchanged_on (AddFrame sh) m m1 ->
  idx1 = newest_marked y lo idx -> t = tget (tr y) (idx1 - 1) ->
  (lo < idx1)%nat -> (idx1 <= tlen y)%nat -> (S f <= tlen y)%nat ->
  (S (S p) <= N)%nat ->
  res = analyze_loop y d lo (S f) idx (S (S p)) ->
  AnalyzeTemps sh d lo idx1 (Z.of_nat (S (S p))) (S f) le ->
  le ! _idx1 = Some (vnat idx1) -> le ! _t = Some (vint (key t)) ->
  Exec ge le m1 analyze_resolve (AnalyzeK m sh N lss d lo res (S f)).
Proof.
  intros sh N lss d lo res f idx idx1 p t y le m m1 Hd Hlo HRep Hun Hidx1 Ht
    Hhigh Hidx1_le Hfuel_le Hp Hres [Hs Hd' Hlo' _ Hpc' Hfuel'] Hidx1' Ht'.
  pose proof (r_n HRep) as HN.
  pose proof (r_nodup HRep) as Hnd.
  pose proof (r_nvars HRep) as Hnv.
  assert (Hta: (extract t < N)%nat).
  { rewrite Ht. apply (r_tr_atoms HRep). lia. }
  pose proof (key_small t N Hta HN) as Hkt.
  assert (Hk: (lit_key (¬t) < 2 * N)%nat) by (destruct t; cbn in *; lia).
  assert (Hxor: Int.xor (Int.repr (key t)) (Int.repr 1) = Int.repr (key (¬t))).
  { apply xor_key. lia. }
  assert (Hsub: Int.sub (Int.repr (Z.of_nat idx1)) (Int.repr 1)
                = Int.repr (Z.of_nat (idx1 - 1))).
  { rewrite sub_repr. f_equal. lia. }
  assert (Hpc: Int.sub (Int.repr (Z.of_nat (S (S p)))) (Int.repr 1)
               = Int.repr (Z.of_nat (S p))).
  { rewrite sub_repr. f_equal. lia. }
  assert (Hfuel: Int.sub (Int.repr (Z.of_nat (S f))) (Int.repr 1)
                 = Int.repr (Z.of_nat f)).
  { rewrite sub_repr. f_equal. lia. }
  pose proof (r_mrk HRep) as Fmrk.
  pose proof (a_mrk HRep) as Amrk.
  unfold analyze_resolve, analyze_body, analyze_loop_stmt, f_analyze.
  cbn [fn_body drop_stmts first_stmt loop_body Swhile].
  (* s->mrk[t ^ 1] = 0; *)
  run. eapply (exec_store_arr Amrk Hk).
  - evl.
  - ofs.
  - reflexivity.
  - ev.
  - intros m2 Hst2. normal.
    set (y1 := y <| mrk := tset (mrk y) (lit_key (¬t)) false |>).
    assert (HRep2: RepL m2 sh N lss y1).
    { apply (rep_store_mrk m1 m2 (lit_key (¬t)) false HRep Hk Hst2). }
    assert (Hun2: Mem.unchanged_on (AddFrame sh) m m2).
    { apply (store_unchanged _ m m1 m2 Mint32 (b_mrk sh) _ _ Hun Hst2).
      intros i [_ [Hb _]]. apply Hb. reflexivity. }
    (* idx = idx1 - 1; pathc = add_reason_lits(s, t, d, pathc - 1); *)
    run.
    eapply (exec_call_triple add_reason_lits_fun
              (add_reason_lits_correct sh N lss y1 t d (S p))).
    + reflexivity.
    + unfold vint. rewrite <- Hpc. evs.
    + split.
      * apply HRep2.
      * split.
        -- assumption.
        -- split.
           ++ assumption.
           ++ lia.
    + intros m3 v Hpost. normal. unfold ReasonPost in Hpost.
      destruct (reason_add y1 t d (S p)) as [y2 r] eqn:Hadd.
      destruct Hpost as (-> & HRep3 & Hun3).
      assert (Htlen2: tlen y2 = tlen y) by apply (reason_add_tlen Hadd).
      (* fuel--; and the loop goes on *)
      run. ints. apply loopk_next with f.
      * lia.
      * exists (idx1 - 1)%nat, (enc_count r), y2. constructor.
        -- constructor.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ tmp.
        -- rewrite Htlen2. lia.
        -- rewrite Htlen2. lia.
        -- apply HRep3.
        -- apply (Mem.unchanged_on_trans _ m m2 m3).
           ++ assumption.
           ++ apply Hun3.
        -- (* the model goes on with the reason of t *)
           rewrite Hres, (analyze_loop_step d lo y f idx p idx1 t Hidx1 Ht Hhigh).
           fold y1. rewrite Hadd. destruct r as [q|].
           ++ left. exists q. split.
              ** reflexivity.
              ** split.
                 --- rewrite <- Hnv.
                     apply (reason_add_count_le y1 y2 t d (S p) q Hadd).
                     cbn [y1 set_mrk nvars]. lia.
                 --- reflexivity.
           ++ right. split.
              ** reflexivity.
              ** reflexivity.
Qed.

(* One round of the loop of analyze, with fuel f + 1 and count pc:

     {{ AnalyzeState (f + 1) idx pc y }}
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
     {{ AnalyzeState f (idx1 - 1) pathc y2 }}

   A break ends the loop with the end of the analysis (analyze_end_correct). *)
Lemma analyze_body_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit))
  (d lo: nat) (res: Ctx * option Lit) (f idx: nat) (pc: Z) (y: Ctx) (le: temp_env)
  (m m1: mem),
  (d <= N)%nat -> (lo <= N)%nat ->
  AnalyzeState m sh N lss d lo res (S f) idx pc y le m1 ->
  Exec ge le m1 analyze_body (AnalyzeK m sh N lss d lo res (S f)).
Proof.
  intros sh N lss d lo res f idx pc y le m m1 Hd Hlo
    [[Hs Hd' Hlo' Hidx' Hpc' Hfuel'] Hidx Hfuel HRep Hun Hres].
  pose proof (r_n HRep) as HN.
  pose proof (r_nodup HRep) as Hnd.
  pose proof (r_nvars HRep) as Hnv.
  pose proof (r_tlen_le HRep) as Htlen.
  unfold analyze_body, analyze_loop_stmt, f_analyze.
  cbn [fn_body drop_stmts first_stmt loop_body Swhile].
  (* if (pathc <= 0) break; *)
  apply exec_seq. eapply (exec_if_le pc 0).
  - ev.
  - ev.
  - reflexivity.
  - destruct Hres as [(p & -> & Hp & _) | (-> & _)].
    + lia.
    + lia.
  - (* no count: break; and the end *)
    intros Hle. apply exec_break. abrupt. apply loopk_break. normal.
    apply (analyze_end_correct sh N lss lo res idx y le m m1).
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + apply (loop_res_stop N y d lo (S f) idx pc res Hres). now right.
    + assumption.
    + assumption.
    + assumption.
  - intros Hgt. destruct Hres as [(p & -> & Hp & Hres) | (-> & _)].
    2: lia.
    destruct p as [|p0].
    { lia. }
    apply exec_skip. normal.
    (* int idx1 = prev_marked(s, idx, lo); idx = idx1; *)
    run.
    eapply (exec_call_triple prev_marked_fun
              (prev_marked_correct sh N lss y idx lo)).
    + reflexivity.
    + evs.
    + split.
      * apply HRep.
      * split.
        -- assumption.
        -- assumption.
    + intros m' v [-> ->]. normal.
      set (idx1 := newest_marked y lo idx).
      pose proof (prev_marked_le (tr y) (mrk y) lo (idx - lo) idx) as Hidx1.
      fold idx1 in Hidx1.
      run.
      (* if (idx1 <= lo) break; *)
      eapply exec_if_le.
      * ev.
      * ev.
      * reflexivity.
      * lia.
      * (* nothing marked above lo: break; and the end *)
        intros Hlow. apply exec_break. abrupt. apply loopk_break. normal.
        apply (analyze_end_correct sh N lss lo res idx1 y).
        -- assumption.
        -- assumption.
        -- lia.
        -- assumption.
        -- rewrite Hres. apply analyze_loop_low. lia.
        -- tmp.
        -- tmp.
        -- tmp.
      * (* t, the literal at idx1 - 1, has its negation marked *)
        intros Hhigh. set (t := tget (tr y) (idx1 - 1)).
        assert (Ht: (extract t < N)%nat).
        { apply (r_tr_atoms HRep). lia. }
        pose proof (key_small t N Ht HN) as Hkt.
        assert (Hneg: (extract (¬t) < N)%nat) by (destruct t; cbn in *; lia).
        assert (Hxor: Int.xor (Int.repr (key t)) (Int.repr 1)
                      = Int.repr (key (¬t))).
        { apply xor_key. lia. }
        assert (Hsub: Int.sub (Int.repr (Z.of_nat idx1)) (Int.repr 1)
                      = Int.repr (Z.of_nat (idx1 - 1))).
        { rewrite sub_repr. f_equal. lia. }
        pose proof (r_tr HRep) as Ftr.
        pose proof (a_tr HRep) as Atr.
        apply exec_skip. normal.
        (* int t = s->tr[idx1 - 1]; *)
        run. fold t.
        (* if (pathc == 1) return t ^ 1; *)
        eapply exec_if_eq.
        -- ev.
        -- ev.
        -- reflexivity.
        -- lia.
        -- (* the last literal of level d: return ¬t *)
           intros Hlast. destruct p0 as [|p'].
           ++ eapply exec_return.
              ** ev.
              ** ret. exists (vint (key (¬t))). split.
                 --- cbn [cast_int_int]. rewrite Hxor. apply result_int.
                 --- rewrite Hres, (analyze_loop_found d lo) by lia.
                     fold idx1 t. split.
                     +++ reflexivity.
                     +++ split.
                         *** assumption.
                         *** split.
                             ---- intros u Hu. injection Hu as <-. assumption.
                             ---- assumption.
           ++ lia.
        -- (* more of level d: unmark ¬t and resolve with its reason *)
           intros Hmore. destruct p0 as [|p'].
           ++ lia.
           ++ apply exec_skip. normal.
              apply (analyze_resolve_correct sh N lss d lo res f idx idx1 p' t y _
                       m m1).
              ** assumption.
              ** assumption.
              ** assumption.
              ** assumption.
              ** reflexivity.
              ** reflexivity.
              ** lia.
              ** lia.
              ** assumption.
              ** assumption.
              ** assumption.
              ** constructor.
                 --- tmp.
                 --- tmp.
                 --- tmp.
                 --- tmp.
                 --- tmp.
                 --- tmp.
              ** tmp.
              ** tmp.
Qed.

(* analyze analyses the conflict on clause i at level d, whose last decision is at trail
   position lo:

     {{ RepL m sh N lss x /\ i < length lss /\ d <= N /\ lo <= N }}
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
Lemma analyze_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (i d lo: nat),
  {{ m | RepL m sh N lss x /\ (i < length lss)%nat /\ (d <= N)%nat /\ (lo <= N)%nat }}
    f_analyze(sptr sh, vnat i, vnat d, vnat lo)
  {{ m', v | AnalyzePost sh N lss (analyze x i d lo) m m' v }}.
Proof.
  intros sh N lss x i d lo m (HRep & Hi & Hd & Hlo).
  pose proof (r_n HRep) as HN.
  pose proof (r_nvars HRep) as Hnv.
  pose proof (r_tlen_le HRep) as Htlen.
  pose proof (r_lss_small HRep) as Hlss.
  pose proof (r_tlen HRep) as Ftlen.
  pose proof (r_clits HRep) as Fcl.
  pose proof (r_cstart HRep) as Fcs.
  pose proof (a_starts HRep) as Astarts.
  pose proof (a_lits HRep) as (tcl & Acl & Hatoms & Hcl).
  destruct (r_starts HRep i Hi) as [Hsi Hsn].
  assert (Hadd1: Int.add (Int.repr (Z.of_nat i)) (Int.repr 1)
                 = Int.repr (Z.of_nat (S i))).
  { apply incr_nat. lia. }
  remember (analyze x i d lo) as res eqn:Hres.
  unfold analyze in Hres. rewrite (Hcl i Hi) in Hres.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_analyze. cbn [fn_body fn_return].
    (* int idx = s->tlen; int pathc = add_lits(...); *)
    run.
    eapply (exec_call_triple add_lits_fun
              (add_lits_correct sh N lss x (b_clits sh) (nclits sh) tcl
                 (starts sh i) (starts sh (S i)) None d 0)).
    + reflexivity.
    + evs.
    + split.
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
                             ---- apply (r_nclits_small HRep).
    + intros m1 v Hpost. normal.
      fold (span_lits tcl (starts sh i) (starts sh (S i))) in Hres.
      destruct (add_lits x d None (span_lits tcl (starts sh i) (starts sh (S i))) 0)
        as [x1 r] eqn:Hadd.
      destruct Hpost as (-> & HRep1 & Hun1). keep_mem m1.
      assert (Htlen1: tlen x1 = tlen x).
      { apply analysed_tlen. now apply add_lits_analysed in Hadd. }
      pose proof (r_tlen HRep1) as Ftlen1.
      (* int fuel = s->tlen; *)
      run. unfold Swhile.
      apply exec_loop with (R := Peano.lt) (I := analyze_inv m sh N lss d lo res)
        (a := tlen x1).
      * apply lt_wf.
      * intros fuel le1 m2 (idx & pc & y & HS).
        pose proof HS as [[Hs Hd' Hlo' Hidx' _ Hfuel'] Hidx Hfuel HRep2 Hun2 Hres2].
        pose proof (r_tlen_le HRep2) as Htlen2.
        (* while (fuel > 0) *)
        apply exec_seq. eapply exec_if_gt.
        -- ev.
        -- ev.
        -- reflexivity.
        -- lia.
        -- (* fuel left: the body *)
           intros Hpos. destruct fuel as [|f].
           ++ lia.
           ++ apply exec_skip. normal.
              apply (analyze_body_correct sh N lss d lo res f idx pc y le1 m m2).
              ** assumption.
              ** assumption.
              ** assumption.
        -- (* no fuel: break; and the end *)
           intros Hzero. apply exec_break. abrupt. apply loopk_break. normal.
           apply (analyze_end_correct sh N lss lo res idx y le1 m m2).
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ assumption.
           ++ apply (loop_res_stop N y d lo fuel idx pc res Hres2). left. lia.
           ++ assumption.
           ++ assumption.
           ++ assumption.
      * (* The invariant holds at the end of the trail, after the conflict clause. *)
        exists (tlen x1), (enc_count r), x1. constructor.
        -- constructor.
           ++ tmp.
           ++ tmp.
           ++ tmp.
           ++ rewrite Htlen1. tmp.
           ++ tmp.
           ++ tmp.
        -- lia.
        -- lia.
        -- assumption.
        -- apply Hun1.
        -- rewrite Hres. destruct r as [p|].
           ++ left. exists p. split.
              ** reflexivity.
              ** split.
                 --- rewrite <- Hnv.
                     apply (add_lits_count_le 0 p Hadd). lia.
                 --- reflexivity.
           ++ right. split.
              ** reflexivity.
              ** reflexivity.
Qed.

Lemma analyze_fun: FunAt _analyze f_analyze.
Proof. apply find_fun. reflexivity. Qed.
