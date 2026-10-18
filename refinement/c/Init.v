(* init sets up the initial context (initial_of) for the clauses in memory, or rejects
   them. *)
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
From RocqSAT.refinement.c Require Import RepHeur.
From RocqSAT.refinement.c Require Import Wpush.
From RocqSAT.refinement.c Require Import Zero.
From RocqSAT.refinement.c Require Import FillNone.
From RocqSAT.refinement.c Require Import CheckClauses.
From RocqSAT.refinement.c Require Import CheckLits.
From RocqSAT.refinement.c Require Import CheckRoom.
From RocqSAT.refinement.c Require Import Index.
From RocqSAT.refinement.c Require Import AddAtoms.

(* The contents of the tables that init writes or reads, but for the clauses and the
   room of the watch lists, which are given. *)
Record InitTables: Type := mkTables {
  t_vals: nat -> Z;
  t_pool: nat -> Z;
  t_wlen: nat -> Z;
  t_tr: nat -> Z;
  t_shorts: nat -> Z;
  t_alls: nat -> Z;
  t_saved: nat -> Z;
  t_lims: nat -> Z;
  t_phs: nat -> Z;
  t_mrk: nat -> Z;
  t_rsn: nat -> Z;
  t_lvl: nat -> Z;
  t_lt: nat -> Z;
  t_rlits: nat -> Z;
  t_rbeg: nat -> Z;
  t_rlen: nat -> Z;
  t_rpos: nat -> Z;
  t_act: nat -> Z;
  t_heap: nat -> Z;
  t_hpos: nat -> Z;
  t_dlit: nat -> Z;
}.

(* The values of the int fields that init sets. *)
Record InitFields: Type := mkFields {
  v_tlen: val;
  v_qhead: val;
  v_nshorts: val;
  v_cur: val;
  v_dl: val;
  v_ltlen: val;
  v_rtop: val;
  v_nr: val;
  v_inc: val;
  v_hsize: val;
}.

(* The memory during init: the fields and the arrays, with the tables tb and the fields
   fl, the number zl of literals to decide on in alls, and small ints in alls. *)
Record Setup {m: mem} {sh: Shape} {N: nat} {lss: list (list Lit)} {rc: nat}
  {tw tc: nat -> Z} {zl: Z} {tb: InitTables} {fl: InitFields}: Prop := {
  se_nodup: NoDup (iblocks sh);
  se_nv: IntAt m sh o_nv N;
  se_ncl: IntAt m sh o_ncl (length lss);
  se_cstart: PtrAt m sh o_cstart (b_cstart sh);
  se_clits: PtrAt m sh o_clits (b_clits sh);
  se_vals: PtrAt m sh o_vals (b_vals sh);
  se_wpool: PtrAt m sh o_wpool (b_wpool sh);
  se_npool: IntAt m sh o_npool (npool sh);
  se_woff: PtrAt m sh o_woff (b_woff sh);
  se_wlen: PtrAt m sh o_wlen (b_wlen sh);
  se_wcap: PtrAt m sh o_wcap (b_wcap sh);
  se_tr: PtrAt m sh o_tr (b_tr sh);
  se_tlen: Fld m (b_s sh) o_tlen Mint32 (v_tlen fl);
  se_qhead: Fld m (b_s sh) o_qhead Mint32 (v_qhead fl);
  se_shorts: PtrAt m sh o_shorts (b_shorts sh);
  se_nshorts: Fld m (b_s sh) o_nshorts Mint32 (v_nshorts fl);
  se_alls: PtrAt m sh o_alls (b_alls sh);
  se_nlits: Fld m (b_s sh) o_nlits Mint32 (vint zl);
  se_cur: Fld m (b_s sh) o_cur Mint32 (v_cur fl);
  se_saved: PtrAt m sh o_saved (b_saved sh);
  se_lims: PtrAt m sh o_lims (b_lims sh);
  se_dl: Fld m (b_s sh) o_dl Mint32 (v_dl fl);
  se_phs: PtrAt m sh o_phs (b_phs sh);
  se_mrk: PtrAt m sh o_mrk (b_mrk sh);
  se_rsn: PtrAt m sh o_rsn (b_rsn sh);
  se_lvl: PtrAt m sh o_lvl (b_lvl sh);
  se_lt: PtrAt m sh o_lt (b_lt sh);
  se_ltlen: Fld m (b_s sh) o_ltlen Mint32 (v_ltlen fl);
  se_rlits: PtrAt m sh o_rlits (b_rlits sh);
  se_rcap: IntAt m sh o_rcap rc;
  se_rtop: Fld m (b_s sh) o_rtop Mint32 (v_rtop fl);
  se_rbeg: PtrAt m sh o_rbeg (b_rbeg sh);
  se_rlen: PtrAt m sh o_rlen (b_rlen sh);
  se_rpos: PtrAt m sh o_rpos (b_rpos sh);
  se_nr: Fld m (b_s sh) o_nr Mint32 (v_nr fl);
  se_act: PtrAt m sh o_act (b_act sh);
  se_inc: Fld m (b_s sh) o_inc Mint32 (v_inc fl);
  se_heap: PtrAt m sh o_heap (b_heap sh);
  se_hpos: PtrAt m sh o_hpos (b_hpos sh);
  se_hsize: Fld m (b_s sh) o_hsize Mint32 (v_hsize fl);
  se_dlit: PtrAt m sh o_dlit (b_dlit sh);
  se_rcap_small: Z.of_nat rc < small_bound;
  se_astarts: Arr m (b_cstart sh) (S (length lss))
    (fun (i: nat) => Z.of_nat (starts sh i));
  se_alits: Arr m (b_clits sh) (nclits sh) (fun (q: nat) => key (lits sh q));
  se_avals: Arr m (b_vals sh) (2 * N) (t_vals tb);
  se_apool: PoolArr m sh (t_pool tb);
  se_awoff: Arr m (b_woff sh) (2 * N) tw;
  se_awlen: Arr m (b_wlen sh) (2 * N) (t_wlen tb);
  se_awcap: Arr m (b_wcap sh) (2 * N) tc;
  se_atr: Arr m (b_tr sh) N (t_tr tb);
  se_ashorts: Arr m (b_shorts sh) (length lss) (t_shorts tb);
  se_aalls: Arr m (b_alls sh) (2 * N) (t_alls tb);
  se_asaved: Arr m (b_saved sh) N (t_saved tb);
  se_alims: Arr m (b_lims sh) N (t_lims tb);
  se_aphs: Arr m (b_phs sh) N (t_phs tb);
  se_amrk: Arr m (b_mrk sh) (2 * N) (t_mrk tb);
  se_arsn: Arr m (b_rsn sh) N (t_rsn tb);
  se_alvl: Arr m (b_lvl sh) N (t_lvl tb);
  se_alt: Arr m (b_lt sh) N (t_lt tb);
  se_arlits: Arr m (b_rlits sh) rc (t_rlits tb);
  se_arbeg: Arr m (b_rbeg sh) N (t_rbeg tb);
  se_arlen: Arr m (b_rlen sh) N (t_rlen tb);
  se_arpos: Arr m (b_rpos sh) N (t_rpos tb);
  se_aact: Arr m (b_act sh) N (t_act tb);
  se_aheap: Arr m (b_heap sh) N (t_heap tb);
  se_ahpos: Arr m (b_hpos sh) N (t_hpos tb);
  se_adlit: Arr m (b_dlit sh) N (t_dlit tb);
  se_nlits_small: Small zl;
  se_alls_small: forall (k: nat), (k < 2 * N)%nat -> Small (t_alls tb k);
}.
Arguments Setup : clear implicits.

(* The memory before init: the clauses in place, the watch lists laid out by the caller
   in tables tw and tc, the room rc for the literals of the reason clauses, small ints in
   alls and as their number, and the other tables and fields with any contents. *)
Definition IRep (m: mem) (sh: Shape) (N: nat) (lss: list (list Lit)) (rc: nat)
  (tw tc: nat -> Z): Prop :=
  exists (zl: Z) (tb: InitTables) (fl: InitFields), Setup m sh N lss rc tw tc zl tb fl.

(* The zero table. *)
Definition zeros: nat -> Z := fun (_: nat) => 0.

(* The table of -1, which encodes None (enc_pos, enc_lit). *)
Definition nones: nat -> Z := fun (_: nat) => -1.

(* The tables after the first phase of init: those that the initial context has empty
   are 0. *)
Definition clear_ctx (tb: InitTables): InitTables :=
  mkTables zeros (t_pool tb) zeros zeros (t_shorts tb) (t_alls tb) (t_saved tb)
    (t_lims tb) zeros zeros zeros zeros (t_lt tb) (t_rlits tb) (t_rbeg tb) (t_rlen tb)
    (t_rpos tb) (t_act tb) (t_heap tb) (t_hpos tb) (t_dlit tb).

(* And after the second: those of the heuristic hold the empty one, act and heap 0,
   hpos and dlit -1 (None). *)
Definition clear_heur (tb: InitTables): InitTables :=
  mkTables (t_vals tb) (t_pool tb) (t_wlen tb) (t_tr tb) (t_shorts tb) (t_alls tb)
    (t_saved tb) (t_lims tb) (t_phs tb) (t_mrk tb) (t_rsn tb) (t_lvl tb) (t_lt tb)
    (t_rlits tb) (t_rbeg tb) (t_rlen tb) (t_rpos tb) zeros zeros nones nones.

(* The tables after both. *)
Definition cleared (tb: InitTables): InitTables := clear_heur (clear_ctx tb).

(* The fields after the third phase: all 0 but the bump inc. *)
Definition zero_fields (inc: val): InitFields :=
  mkFields (vint 0) (vint 0) (vint 0) (vint 0) (vint 0) (vint 0) (vint 0) (vint 0) inc
    (vint 0).

(* The shape sh with the watch lists laid out as offs and caps. *)
Definition with_room (sh: Shape) (o c: nat -> nat): Shape :=
mkShape (b_s sh) (b_cstart sh) (b_clits sh) (b_vals sh) (b_wpool sh) (b_woff sh)
  (b_wlen sh) (b_wcap sh) (b_tr sh) (b_shorts sh) (b_alls sh) (b_saved sh) (b_lims sh)
  (b_phs sh) (b_mrk sh) (b_rsn sh) (b_lvl sh) (b_lt sh) (b_rlits sh) (b_rbeg sh)
  (b_rlen sh) (b_rpos sh) (b_act sh)
  (b_heap sh) (b_hpos sh) (b_dlit sh) (starts sh) (lits sh) (nclits sh) o c (npool sh).

(* The shape with the watch lists laid out as the caller asked, in tw and tc. *)
Definition room_shape (sh: Shape) (tw tc: nat -> Z): Shape :=
  with_room sh (fun (k: nat) => Z.to_nat (tw k)) (fun (k: nat) => Z.to_nat (tc k)).

(* The table of the literals acc to decide on, in their order. *)
Abbreviation alls_of acc := (fill (tmake (Pos 0%nat)) 0%nat acc).

(* The initial context is the one with every clause indexed, with its short clauses and
   the initial heuristic. *)
Lemma initial_of_idx: forall (lss: list (list Lit)) (ls: list Lit) (nv rc: nat),
  initial_of lss ls nv rc =
  (ictx lss (alls_of ls) (length ls) nv rc (length lss))
    <| shorts := ish (idx lss (length lss)) |>
    <| hr := init_heur (alls_of ls) nv (length ls) |>.
Proof.
  intros lss ls nv rc. unfold initial_of, ictx, idx. rewrite firstn_all.
  now destruct (index 0%nat lss (tmake None) (tmake []) []) as [[cm wl] ss].
Qed.

(* The positions of the clauses cover the literals from position 0 to the end. *)
Lemma cover_range: forall (st: nat -> nat) (n q: nat),
  st 0%nat = 0%nat ->
  (forall (i: nat), (i < n)%nat -> (st i <= st (S i))%nat) ->
  (q < st n)%nat -> exists (i: nat), (i < n)%nat /\ (st i <= q < st (S i))%nat.
Proof.
  intros st n q H0 Hmono. induction n as [|n IH]; intros Hq.
  - lia.
  - destruct (Nat.lt_ge_cases q (st n)) as [Hlt | Hge].
    + destruct IH as [i [Hi Hrange]].
      * intros i Hi. apply Hmono. lia.
      * assumption.
      * exists i. split.
        -- lia.
        -- assumption.
    + exists n. split; lia.
Qed.

(* The clause literals, at the positions below nclits sh, are the literals of the
   clauses. *)
Lemma clause_lits_iff: forall (sh: Shape) (lss: list (list Lit)) (l: Lit),
  Layout sh lss ->
  (exists (q: nat), (q < nclits sh)%nat /\ lits sh q = l) <->
  exists (cs: list Lit), In cs lss /\ In l cs.
Proof.
  intros sh lss l [Hclauses H0 Hend]. split.
  - intros [q [Hq <-]]. rewrite <- Hend in Hq.
    destruct (cover_range (starts sh) (length lss) q H0) as [i [Hi Hrange]].
    + intros i Hi. now apply Hclauses.
    + assumption.
    + exists (nth i lss []). split.
      * now apply nth_In.
      * destruct (Hclauses i Hi) as [_ ->]. unfold span. apply in_map. apply in_seq.
        lia.
  - intros [cs [Hcs Hl]]. apply In_nth with (d := []) in Hcs as [i [Hi <-]].
    destruct (Hclauses i Hi) as [Hrange Heq].
    rewrite Heq in Hl. unfold span in Hl. apply in_map_iff in Hl as [q [<- Hq]].
    apply in_seq in Hq. exists q.
    split.
    + lia.
    + reflexivity.
Qed.

(* When the clauses have atoms below N, so do all clause literals. *)
Lemma clause_lits_atoms: forall (sh: Shape) (N: nat) (lss: list (list Lit)),
  Layout sh lss ->
  (forall (i: nat), (i < length lss)%nat -> AtomsBelow N (nth i lss [])) ->
  forall (q: nat), (q < nclits sh)%nat -> (extract (lits sh q) < N)%nat.
Proof.
  intros sh N lss Hly Hat q Hq.
  assert (Hq': exists (q': nat), (q' < nclits sh)%nat /\ lits sh q' = lits sh q).
  { exists q. split.
    - assumption.
    - reflexivity. }
  apply (clause_lits_iff sh lss (lits sh q) Hly) in Hq' as [cs [Hcs Hl]].
  apply In_nth with (d := []) in Hcs as [i [Hi <-]]. apply (Hat i Hi). assumption.
Qed.

(* What init is given about its input besides the memory: the clause layout, the sizes,
   and the bounds of the room of the watch lists. *)
Record InitInput {sh: Shape} {N: nat} {lss: list (list Lit)} {tw tc: nat -> Z}: Prop := {
  in_layout: Layout sh lss;
  in_sizes: Sizes sh N lss;
  in_npool: Z.of_nat (npool sh) < small_bound;
  in_room: forall (k: nat), (k < 2 * N)%nat -> Small (tw k) /\ Small (tc k);
}.
Arguments InitInput : clear implicits.

(* What init gives: 0 to reject the input, or 1 with the initial context in memory. *)
Definition InitPost (sh: Shape) (N: nat) (lss: list (list Lit)) (rc: nat) (m': mem)
  (v: val): Prop :=
  v = vint 0 \/
  (v = vint 1 /\ (1 <= N)%nat /\ exists (offs caps: nat -> nat) (acc: list Lit),
     Rep m' (with_room sh offs caps) N lss (initial_of lss acc N rc) /\
     (forall (i: nat), (i < length lss)%nat -> NoDup (nth i lss [])) /\
     forall (l: Lit), In l acc <-> exists (cs: list Lit), In cs lss /\ In l cs).

(* The phases of init, each proved in a lemma of its own: clearing the tables (those of
   the heuristic last), setting the fields, the checks, and indexing the clauses. *)
Definition init_clear: statement := drop_stmts 2 (fn_body f_init).
Definition init_clear_heur: statement := drop_stmts 9 (fn_body f_init).
Definition init_fields: statement := drop_stmts 13 (fn_body f_init).
Definition init_checks: statement := drop_stmts 22 (fn_body f_init).
Definition init_index: statement := drop_stmts 26 (fn_body f_init).

(* The empty heuristic of nl literals to decide on is within the bounds for N atoms: its
   bump nl + 1 is below act_lim / 2 = 2^29, as nl <= 2 N and N < 2^28. *)
Lemma empty_heur_ok: forall (N nl: nat),
  (1 <= N)%nat -> (nl <= 2 * N)%nat -> Z.of_nat N < atom_bound ->
  HeurOk N (empty_heur nl).
Proof.
  intros N nl HN1 Hnl HN. constructor.
  - (* no activity yet *)
    intros a Ha. cbn [empty_heur act]. rewrite tget_tmake.
    change act_lim with small_bound. lia.
  - (* the bump *)
    cbn [empty_heur inc]. change (act_lim / 2) with key_bound. lia.
  - (* the heap entries are 0, an atom as N >= 1 *)
    intros i Hi. cbn [empty_heur heap]. rewrite tget_tmake. lia.
  - (* no atom in the heap *)
    intros a i Ha Hi. cbn [empty_heur hpos] in Hi. rewrite tget_tmake in Hi.
    discriminate.
  - cbn [empty_heur hsize]. lia.
  - (* no literal to decide on yet *)
    intros a l Ha Hl. cbn [empty_heur dlit] in Hl. rewrite tget_tmake in Hl.
    discriminate.
Qed.

Section Phases.
  (* A call of init for the clauses lss of N atoms, with the watch lists laid out in tw
     and tc and the room rc for the literals of the reason clauses. *)
  Variables (sh: Shape) (N: nat) (lss: list (list Lit)) (rc: nat) (tw tc: nat -> Z).
  Hypothesis (HIn: InitInput sh N lss tw tc).

  (* After the checks: the memory represents the context ictx with the clause literals
     acc to decide on, no watches yet, no marks, levels and reasons, the empty heuristic,
     and the watch lists laid out as the caller asked. *)
  Lemma setup_rep: forall (m: mem) (tb: InitTables) (acc: list Lit),
    (1 <= N)%nat ->
    Setup m sh N lss rc tw tc (Z.of_nat (length acc)) (cleared tb)
      (zero_fields (vint (Z.of_nat (length acc) + 1))) ->
    (forall (i: nat), (i < length lss)%nat -> AtomsBelow N (nth i lss [])) ->
    NoDup acc -> (length acc <= 2 * N)%nat ->
    (forall (l: Lit),
       In l acc <-> exists (q: nat), (q < nclits sh)%nat /\ lits sh q = l) ->
    (forall (k: nat), (k < length acc)%nat ->
       t_alls tb k = key (nth k acc (Pos 0%nat))) ->
    Fits tw tc (2 * N) (Z.of_nat (npool sh)) -> InOrder tw tc (2 * N) ->
    Rep m (room_shape sh tw tc) N lss (ictx lss (alls_of acc) (length acc) N rc 0).
  Proof.
    intros m tb acc HN1 HSe Hat Hndacc Hlacc Hacc Hta Hroom Horder.
    pose proof HIn as [Hly [HN Hncl Hkeys Hlss] Hnp Hsmall].
    pose proof Hly as [Hclauses H0 Hend].
    destruct HSe as [Hnd Fnv Fncl Fcs Fcl Fvals Fpool Fnp Fwoff Fwlen Fwcap Ftr Ftlen
      Fqh Fsh Fns Falls Fnl Fcur Fsv Flims Fdl Fphs Fmrk Frsn Flvl Flt Fltlen Frl Frcap
      Frtop Frb Frn Frp Fnr Fact Finc Fheap Fhpos Fhsize Fdlit Hrc Ast Alits Avals Apool
      Awoff Awlen Awcap Atr Ash Aalls Asaved Alims Aphs Amrk Arsn Alvl Alt Arl Arb Arn
      Arp Aact Aheap Ahpos Adlit Hzl Hta_small].
    pose proof Hnd as Hnd'. unfold iblocks in Hnd'.
    set (al := alls_of acc).
    assert (Hal: forall (k: nat), (k < length acc)%nat ->
                   tget al k = nth k acc (Pos 0%nat)).
    { intros k Hk. subst al. rewrite <- (Nat.add_0_l k), fill_spec by assumption.
      reflexivity. }
    pose proof (clause_lits_atoms sh N lss Hly Hat) as Hlat.
    split.
    - (* Every field holds what the shape and ictx say, but the following ones. *)
      constructor; try assumption.
      + (* the clauses, at their positions of clits *)
        exists (fun (q: nat) => key (lits sh q)). split.
        * assumption.
        * split.
          -- intros q Hq. exists (lits sh q). split.
             ++ reflexivity.
             ++ apply Hlat. assumption.
          -- intros i Hi. cbn [ictx cmap]. rewrite idx_cm by lia.
             replace (i <? length lss)%nat with true by (symmetry; now apply Nat.ltb_lt).
             destruct (Hclauses i Hi) as [_ Heq]. rewrite Heq. unfold span. f_equal.
             apply map_ext.
             intros q. symmetry. apply lit_of_key.
      + (* no values yet: every literal is unassigned *)
        eapply arr_ext.
        * eassumption.
        * intros k Hk. unfold key_value. destruct (Nat.even k); reflexivity.
      + (* the offsets of the watch lists *)
        eapply arr_ext.
        * eassumption.
        * intros k Hk. cbn [room_shape with_room Rep.offs]. rewrite Z2Nat.id.
          -- reflexivity.
          -- now destruct (Hroom k Hk).
      + (* the capacities of the watch lists *)
        eapply arr_ext.
        * eassumption.
        * intros k Hk. cbn [room_shape with_room Rep.caps]. rewrite Z2Nat.id.
          -- reflexivity.
          -- now destruct (Hroom k Hk).
      + (* no short clause yet *)
        exists (t_shorts tb). split.
        * assumption.
        * intros q Hq. cbn [ictx shorts length] in Hq. lia.
      + (* the literals to decide on *)
        exists (t_alls tb). split.
        * assumption.
        * intros k Hk. cbn [ictx alls nlits] in *. rewrite Hta, Hal by assumption.
          reflexivity.
      + (* no saved cursor *)
        exists (t_saved tb). split.
        * assumption.
        * intros k Hk. cbn [ictx saved length] in Hk. lia.
      + (* no decision *)
        exists (t_lims tb). split.
        * assumption.
        * intros k Hk. cbn [ictx lims length] in Hk. lia.
      + (* no clause past the last *)
        intros i Hi. cbn [ictx cmap]. rewrite idx_cm by lia.
        replace (i <? length lss)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
        reflexivity.
      + (* the ranges of the clauses *)
        intros i Hi. destruct (Hclauses i Hi) as [Hrange _]. assumption.
      + (* the number of atoms *)
        reflexivity.
      + (* every watch list fits in the pool *)
        intros k Hk. cbn [room_shape with_room Rep.offs Rep.caps Rep.npool].
        destruct (Hroom k Hk) as (Ho & Hc & Hoc). lia.
      + (* the watch lists come one after the other *)
        intros k k' Hk. cbn [room_shape with_room Rep.offs Rep.caps].
        pose proof (Horder k k' Hk) as Hkk.
        assert (Hk1: (k < 2 * N)%nat) by lia. assert (Hk2: (k' < 2 * N)%nat) by lia.
        destruct (Hroom k Hk1) as (H1 & H2 & H3).
        destruct (Hroom k' Hk2) as (H4 & H5 & H6).
        lia.
      + (* the empty watch lists fit their room *)
        intros k Hk. cbn [ictx wls]. unfold idx. cbn [firstn index iwl].
        rewrite tget_tmake.
        cbn [length]. lia.
      + (* the empty watch lists hold no watcher *)
        intros k i b Hk Hi. unfold idx in Hi. cbn in Hi. rewrite tget_tmake in Hi.
        destruct Hi.
      + (* nor blockers *)
        intros k i b Hk Hi. unfold idx in Hi. cbn in Hi. rewrite tget_tmake in Hi.
        destruct Hi.
      + (* the empty trail *)
        cbn [ictx tlen]. lia.
      + (* the empty queue *)
        cbn [ictx tlen qhead]. lia.
      + (* the empty trail has no atoms *)
        intros j Hj. cbn [ictx tlen] in Hj. lia.
      + (* no short clause *)
        cbn [ictx shorts length]. lia.
      + (* no short clause *)
        intros i [].
      + (* the literals to decide on have atoms below N *)
        intros k Hk. cbn [ictx alls nlits] in *. rewrite Hal by assumption.
        destruct (proj1 (Hacc (nth k acc (Pos 0%nat))) (nth_In _ _ Hk)) as [q [Hq <-]].
        now apply Hlat.
      + (* the cursor at the start *)
        cbn [ictx cur nlits]. lia.
      + (* no saved cursor *)
        intros c [].
      + (* no decision, and no saved cursor *)
        reflexivity.
      + (* no decision *)
        cbn [ictx lims length]. lia.
      + (* no lower literals of an analysis *)
        exists (t_lt tb). split.
        * assumption.
        * intros k Hk. cbn [ictx lower length] in Hk. lia.
      + (* no reason clauses: their literals *)
        exists (t_rlits tb). split.
        * assumption.
        * intros j k Hj. cbn [ictx nr] in Hj. lia.
      + (* their starts *)
        exists (t_rbeg tb). split.
        * assumption.
        * intros j Hj. cbn [ictx nr] in Hj. lia.
      + (* their lengths *)
        exists (t_rlen tb). split.
        * assumption.
        * intros j Hj. cbn [ictx nr] in Hj. lia.
      + (* their trail positions *)
        exists (t_rpos tb). split.
        * assumption.
        * intros j Hj. cbn [ictx nr] in Hj. lia.
      + (* no decision *)
        reflexivity.
      + (* no reasons *)
        intros a Ha. cbn [ictx rsn]. rewrite tget_tmake. cbn [ReasonBelow]. apply I.
      + (* all levels 0 *)
        intros a Ha. cbn [ictx lvl]. rewrite tget_tmake. lia.
      + (* no lower literals *)
        cbn [ictx lower length]. lia.
      + intros y [].
      + (* no reason clauses *)
        cbn [ictx nr]. lia.
      + cbn [ictx nr rcl reasons_size]. lia.
      + intros j y Hj. cbn [ictx nr] in Hj. lia.
      + intros j Hj. cbn [ictx nr] in Hj. lia.
      + (* the empty heuristic *)
        apply empty_heur_ok; assumption.
    - split.
      + (* no lower literals *)
        reflexivity.
      + (* the pool holds the empty watch lists *)
        exists (t_pool tb). split.
        * assumption.
        * intros k q Hk Hq. unfold idx in Hq. cbn in Hq. rewrite tget_tmake in Hq.
          cbn in Hq. lia.
  Qed.

  (* The last phase: indexing the clauses, which sets the watches and the short clauses,
     and adding the literals to decide on to the heuristic:

       {{ Rep (ictx ... 0) /\ the array of short clauses }}
         int ns = index_clauses(s);                              (index_clauses_correct)
         if (ns < 0) return 0;
       {{ result = 0 (out of room) }}
       {{ Rep (ictx ... (length lss)) /\ the short clauses are in their array }}
         s->nshorts = ns;                                              (rep_store_shorts)
       {{ RepL (ictx ... (length lss) with its short clauses, the empty heuristic) }}
         add_atoms(s);                                                (add_atoms_correct)
       {{ RepL (initial_of lss acc N rc): the heuristic is init_heur }}
         return 1;
       {{ result = 1 /\ Rep (initial_of lss acc N rc) }}                               *)
  Lemma init_index_correct: forall (acc: list Lit) (tsh: nat -> Z) (le: temp_env)
    (m: mem),
    (1 <= N)%nat ->
    (forall (i: nat), (i < length lss)%nat -> NoDup (nth i lss [])) ->
    (forall (l: Lit), In l acc <-> exists (cs: list Lit), In cs lss /\ In l cs) ->
    Rep m (room_shape sh tw tc) N lss (ictx lss (alls_of acc) (length acc) N rc 0) ->
    Arr m (b_shorts sh) (length lss) tsh ->
    le ! _s = Some (sptr sh) ->
    Exec ge le m init_index (Returns f_init (InitPost sh N lss rc)).
  Proof.
    intros acc tsh le m HN1 Hndc Hacc HRep0 Ash Hs.
    set (S' := room_shape sh tw tc) in *.
    set (al := alls_of acc) in *.
    pose proof (r_lss_small (proj1 HRep0)) as Hlss.
    unfold init_index, f_init. cbn [fn_body drop_stmts].
    (* int ns = index_clauses(s); *)
    run. call index_clauses_fun (index_clauses_correct S' N lss al (length acc) rc tsh).
    - split.
      + assumption.
      + split; assumption.
    - intros m1 v Hv. normal. run.
      destruct Hv as [-> | (tsh' & -> & [HRep1 Hpool1] & Ash1 & Htsh1)].
      + (* out of room: if (ns < 0) return 0; *)
        branch (-1) 0.
        * intros _. return_int.
          now left.
        * intros Hge. lia.
      + (* the short clauses ns: s->nshorts = ns; return 1; *)
        pose proof (idx_lists lss (length lss) (le_n _)) as (_ & Hshc & Hshl).
        branch _ 0.
        * intros Hlt. lia.
        * intros _. keep_mem m1.
          pose proof (Rep.r_nodup HRep1) as Hnd.
          pose proof (Rep.r_nshorts HRep1) as Fns1.
          unfold S', room_shape, with_room in *.
          cbn [b_s b_shorts b_wpool b_act b_heap b_hpos b_dlit] in Fns1, Ash1, Hnd,
            Hpool1.
          run. store Fns1 as m2 Hst2.
          pose proof (rep_store_shorts m1 m2 _ tsh' HRep1 Ash1
                        Htsh1 Hshl Hshc Hst2) as HRep2.
          destruct Hpool1 as [_ [tp [Apool1 Hpool1]]].
          assert (Apool2: Arr m2 (b_wpool sh) (2 * npool S') tp).
          { apply (arr_store_other Apool1 Hst2). neq Hnd. }
          keep_mem m2.
          (* add_atoms(s); *)
          run. call add_atoms_fun (add_atoms_correct S' N lss _).
          -- apply HRep2.
          -- intros m3 v3 [HRep3 Hun3]. normal. unfold HeurFrame, S' in Hun3.
             cbn [b_act b_heap b_hpos b_dlit b_s] in Hun3.
             transfer Hun3 Hnd. keep_mem m3.
             (* return 1; *)
             return_int.
             right. splits.
             ++ reflexivity.
             ++ assumption.
             ++ exists (fun (k: nat) => Z.to_nat (tw k)),
                  (fun (k: nat) => Z.to_nat (tc k)), acc.
                split.
                ** rewrite initial_of_idx. split.
                   --- apply HRep3.
                   --- split.
                       +++ (* no lower literals *)
                           reflexivity.
                       +++ exists tp. split; assumption.
                ** split; assumption.
  Qed.

  (* The checks, after the tables and fields are cleared:

       {{ Setup zl (cleared tb) (zero_fields vin) }}
         if (!check_clauses(s)) return 0;                       (check_clauses_correct)
       {{ result = 0: a literal out of range or twice in a clause }}
         if (!check_lits(s)) return 0;                             (check_lits_correct)
       {{ result = 0: alls is not the literals acc of the clauses, each once }}
         s->inc = s->nlits + 1;
       {{ Setup (length acc) (cleared tb) (zero_fields (length acc + 1)) }}
         if (!check_room(s)) return 0;                             (check_room_correct)
       {{ result = 0: the watch lists do not fit }}
       {{ Rep (ictx ... 0) }}                                               (setup_rep)
         ...                                                   (init_index_correct) *)
  Lemma init_checks_correct: forall (zl: Z) (tb: InitTables) (vin: val) (le: temp_env)
    (m: mem),
    (1 <= N)%nat -> Setup m sh N lss rc tw tc zl (cleared tb) (zero_fields vin) ->
    le ! _s = Some (sptr sh) ->
    Exec ge le m init_checks (Returns f_init (InitPost sh N lss rc)).
  Proof.
    intros zl tb vin le m HN1 HSe Hs.
    pose proof HIn as [Hly Hsz Hnp Hsmall]. pose proof Hsz as [HN _ _ _].
    destruct HSe as [Hnd Fnv Fncl Fcs Fcl Fvals Fpool Fnp Fwoff Fwlen Fwcap Ftr Ftlen
      Fqh Fsh Fns Falls Fnl Fcur Fsv Flims Fdl Fphs Fmrk Frsn Flvl Flt Fltlen Frl Frcap
      Frtop Frb Frn Frp Fnr Fact Finc Fheap Fhpos Fhsize Fdlit Hrc Ast Alits Avals Apool
      Awoff Awlen Awcap Atr Ash Aalls Asaved Alims Aphs Amrk Arsn Alvl Alt Arl Arb Arn
      Arp Aact Aheap Ahpos Adlit Hzl Hta].
    pose proof Hnd as Hnd'. unfold iblocks in Hnd'.
    assert (HF: ClauseFlds sh N lss m) by (constructor; assumption).
    unfold init_checks, f_init. cbn [fn_body drop_stmts].
    (* if (!check_clauses(s)) return 0; *)
    run. call check_clauses_fun (check_clauses_correct sh N lss zeros).
    - repeat (split; [assumption | ]). intros k Hk. reflexivity.
    - intros m1 v Hv. normal. run.
      destruct Hv as [-> | (-> & Hat & Hndc & (tm1 & Amrk1 & Hm1) & Hun1)].
      + (* a literal out of range or twice in a clause: return 0; *)
        branch 1.
        * intros _. return_int.
          now left.
        * intros Heq. lia.
      + branch 0.
        * intros Hne. lia.
        * intros _. clear HF. transfer Hun1 Hnd'. keep_mem m1.
          assert (HF1: ClauseFlds sh N lss m1) by (constructor; assumption).
          (* the literals of the clauses have atoms below N *)
          pose proof (clause_lits_atoms sh N lss Hly Hat) as Hlat.
          (* if (!check_lits(s)) return 0; *)
          run. call check_lits_fun (check_lits_correct sh N lss zl (t_alls tb) tm1).
          -- constructor; assumption.
          -- intros m2 v ((tm2 & Amrk2) & Hun2 & Hv). normal. clear HF1.
             transfer Hun2 Hnd'. keep_mem m2. run.
             destruct Hv
               as [-> | (-> & Amrk0 & acc & Hzacc & Hndacc & Hlacc & Hacc & Hta2)].
             ++ (* alls is not the clause literals, once each: return 0; *)
                branch 1.
                ** intros _. return_int.
                   now left.
                ** intros Heq. lia.
             ++ branch 0.
                ** intros Hne. lia.
                ** intros _. apply exec_skip. normal. subst zl.
                   (* s->inc = s->nlits + 1; *)
                   run. store Finc as m3 Hst3.
                   pose proof (fld_store Finc Hst3) as Finc3. clear Finc.
                   carry Hst3 Hnd'. cbn [Val.load_result cast_int_int] in Finc3.
                   rewrite add_repr in Finc3.
                   (* if (!check_room(s)) return 0; *)
                   run. call check_room_fun (check_room_correct sh N tw tc).
                   --- repeat (split; [assumption | ]). assumption.
                   --- intros m4 v [-> Hv]. normal. run.
                       destruct Hv as [-> | (-> & Hroom & Horder)].
                       +++ (* the watch lists do not fit: return 0; *)
                           branch 1.
                           *** intros _. return_int.
                               now left.
                           *** intros Heq. lia.
                       +++ (* the memory represents ictx: index the clauses *)
                           branch 0.
                           *** intros Hne. lia.
                           *** intros _. apply exec_skip. normal.
                               apply (init_index_correct acc (t_shorts tb)).
                               ---- assumption.
                               ---- assumption.
                               ---- intros l. rewrite Hacc.
                                    now apply clause_lits_iff.
                               ---- apply (setup_rep _ tb acc).
                                    ++++ assumption.
                                    ++++ constructor; assumption.
                                    ++++ assumption.
                                    ++++ assumption.
                                    ++++ assumption.
                                    ++++ assumption.
                                    ++++ assumption.
                                    ++++ assumption.
                                    ++++ assumption.
                               ---- assumption.
                               ---- tmp.
  Qed.

  (* Setting the fields of an empty trail, queue, short clauses, cursor, decisions,
     analysis and reason clauses:

       {{ Setup zl (cleared tb) fl }}
         s->tlen = 0;
         s->qhead = 0;
         s->nshorts = 0;
         s->cur = 0;
         s->dl = 0;
         s->ltlen = 0;
         s->rtop = 0;
         s->nr = 0;
         s->hsize = 0;
       {{ Setup zl (cleared tb) (zero_fields (v_inc fl)) }}
         ...                                                  (init_checks_correct) *)
  Lemma init_fields_correct: forall (zl: Z) (tb: InitTables) (fl: InitFields)
    (le: temp_env) (m: mem),
    (1 <= N)%nat -> Setup m sh N lss rc tw tc zl (cleared tb) fl ->
    le ! _s = Some (sptr sh) ->
    Exec ge le m init_fields (Returns f_init (InitPost sh N lss rc)).
  Proof.
    intros zl tb fl le m HN1 HSe Hs.
    destruct HSe as [Hnd Fnv Fncl Fcs Fcl Fvals Fpool Fnp Fwoff Fwlen Fwcap Ftr Ftlen
      Fqh Fsh Fns Falls Fnl Fcur Fsv Flims Fdl Fphs Fmrk Frsn Flvl Flt Fltlen Frl Frcap
      Frtop Frb Frn Frp Fnr Fact Finc Fheap Fhpos Fhsize Fdlit Hrc Ast Alits Avals Apool
      Awoff Awlen Awcap Atr Ash Aalls Asaved Alims Aphs Amrk Arsn Alvl Alt Arl Arb Arn
      Arp Aact Aheap Ahpos Adlit Hzl Hta].
    pose proof Hnd as Hnd'. unfold iblocks in Hnd'.
    unfold init_fields, f_init. cbn [fn_body drop_stmts].
    (* s->tlen = 0; *)
    run. store Ftlen as m1 Hst1.
    pose proof (fld_store Ftlen Hst1) as Ftlen1. clear Ftlen.
    carry Hst1 Hnd'.
    (* s->qhead = 0; *)
    run. store Fqh as m2 Hst2.
    pose proof (fld_store Fqh Hst2) as Fqh2. clear Fqh.
    carry Hst2 Hnd'.
    (* s->nshorts = 0; *)
    run. store Fns as m3 Hst3.
    pose proof (fld_store Fns Hst3) as Fns3. clear Fns.
    carry Hst3 Hnd'.
    (* s->cur = 0; *)
    run. store Fcur as m4 Hst4.
    pose proof (fld_store Fcur Hst4) as Fcur4. clear Fcur.
    carry Hst4 Hnd'.
    (* s->dl = 0; *)
    run. store Fdl as m5 Hst5.
    pose proof (fld_store Fdl Hst5) as Fdl5. clear Fdl.
    carry Hst5 Hnd'.
    (* s->ltlen = 0; *)
    run. store Fltlen as m6 Hst6.
    pose proof (fld_store Fltlen Hst6) as Fltlen6. clear Fltlen.
    carry Hst6 Hnd'.
    (* s->rtop = 0; *)
    run. store Frtop as m7 Hst7.
    pose proof (fld_store Frtop Hst7) as Frtop7. clear Frtop.
    carry Hst7 Hnd'.
    (* s->nr = 0; *)
    run. store Fnr as m8 Hst8.
    pose proof (fld_store Fnr Hst8) as Fnr8. clear Fnr.
    carry Hst8 Hnd'.
    (* s->hsize = 0; *)
    run. store Fhsize as m9 Hst9.
    pose proof (fld_store Fhsize Hst9) as Fhsize9.
    clear Fhsize.
    carry Hst9 Hnd'.
    cbn [Val.load_result] in Ftlen1, Fqh2, Fns3, Fcur4, Fdl5,
      Fltlen6, Frtop7, Fnr8, Fhsize9.
    apply (init_checks_correct zl tb (v_inc fl)).
    - assumption.
    - constructor; assumption.
    - tmp.
  Qed.

  (* Clearing the tables of the heuristic, which the empty heuristic has empty:

       {{ Setup zl (clear_ctx tb) fl }}
         zero(s->act, s->nv);                                            (zero_correct)
         zero(s->heap, s->nv);
         fill_none(s->hpos, s->nv);                                 (fill_none_correct)
         fill_none(s->dlit, s->nv);
       {{ Setup zl (cleared tb) fl }}
         ...                                                  (init_fields_correct) *)
  Lemma init_clear_heur_correct: forall (zl: Z) (tb: InitTables) (fl: InitFields)
    (le: temp_env) (m: mem),
    (1 <= N)%nat -> Setup m sh N lss rc tw tc zl (clear_ctx tb) fl ->
    le ! _s = Some (sptr sh) ->
    Exec ge le m init_clear_heur (Returns f_init (InitPost sh N lss rc)).
  Proof.
    intros zl tb fl le m HN1 HSe Hs.
    pose proof (sz_n (in_sizes HIn)) as HN.
    destruct HSe as [Hnd Fnv Fncl Fcs Fcl Fvals Fpool Fnp Fwoff Fwlen Fwcap Ftr Ftlen
      Fqh Fsh Fns Falls Fnl Fcur Fsv Flims Fdl Fphs Fmrk Frsn Flvl Flt Fltlen Frl Frcap
      Frtop Frb Frn Frp Fnr Fact Finc Fheap Fhpos Fhsize Fdlit Hrc Ast Alits Avals Apool
      Awoff Awlen Awcap Atr Ash Aalls Asaved Alims Aphs Amrk Arsn Alvl Alt Arl Arb Arn
      Arp Aact Aheap Ahpos Adlit Hzl Hta].
    pose proof Hnd as Hnd'. unfold iblocks in Hnd'.
    unfold init_clear_heur, f_init. cbn [fn_body drop_stmts].
    (* zero(s->act, s->nv); *)
    run. call zero_fun (zero_correct (b_act sh) N (t_act tb)).
    - split.
      + assumption.
      + lia.
    - intros m1 v1 [Aact1 Hun1]. normal. transfer Hun1 Hnd'. keep_mem m1.
      (* zero(s->heap, s->nv); *)
      run. call zero_fun (zero_correct (b_heap sh) N (t_heap tb)).
      + split.
        * assumption.
        * lia.
      + intros m2 v2 [Aheap2 Hun2]. normal. transfer Hun2 Hnd'. keep_mem m2.
        (* fill_none(s->hpos, s->nv); *)
        run. call fill_none_fun (fill_none_correct (b_hpos sh) N (t_hpos tb)).
        * split.
          -- assumption.
          -- lia.
        * intros m3 v3 [Ahpos3 Hun3]. normal. transfer Hun3 Hnd'. keep_mem m3.
          (* fill_none(s->dlit, s->nv); *)
          run. call fill_none_fun (fill_none_correct (b_dlit sh) N (t_dlit tb)).
          -- split.
             ++ assumption.
             ++ lia.
          -- intros m4 v4 [Adlit4 Hun4]. normal. transfer Hun4 Hnd'. keep_mem m4.
             apply (init_fields_correct zl tb fl).
             ++ assumption.
             ++ constructor; assumption.
             ++ tmp.
  Qed.

  (* Clearing the tables that the initial context has empty:

       {{ Setup zl tb fl }}
         zero(s->vals, n);                                               (zero_correct)
         zero(s->tr, s->nv);
         zero(s->phs, s->nv);
         zero(s->mrk, n);
         zero(s->wlen, n);
         zero(s->rsn, s->nv);
         zero(s->lvl, s->nv);
       {{ Setup zl (clear_ctx tb) fl }}
         ...                                              (init_clear_heur_correct) *)
  Lemma init_clear_correct: forall (zl: Z) (tb: InitTables) (fl: InitFields)
    (le: temp_env) (m: mem),
    (1 <= N)%nat -> Setup m sh N lss rc tw tc zl tb fl ->
    le ! _s = Some (sptr sh) -> le ! _n = Some (vnat (2 * N)) ->
    Exec ge le m init_clear (Returns f_init (InitPost sh N lss rc)).
  Proof.
    intros zl tb fl le m HN1 HSe Hs Hn.
    pose proof (sz_n (in_sizes HIn)) as HN.
    destruct HSe as [Hnd Fnv Fncl Fcs Fcl Fvals Fpool Fnp Fwoff Fwlen Fwcap Ftr Ftlen
      Fqh Fsh Fns Falls Fnl Fcur Fsv Flims Fdl Fphs Fmrk Frsn Flvl Flt Fltlen Frl Frcap
      Frtop Frb Frn Frp Fnr Fact Finc Fheap Fhpos Fhsize Fdlit Hrc Ast Alits Avals Apool
      Awoff Awlen Awcap Atr Ash Aalls Asaved Alims Aphs Amrk Arsn Alvl Alt Arl Arb Arn
      Arp Aact Aheap Ahpos Adlit Hzl Hta].
    pose proof Hnd as Hnd'. unfold iblocks in Hnd'.
    unfold init_clear, f_init. cbn [fn_body drop_stmts].
    (* zero(s->vals, n); *)
    run. call zero_fun (zero_correct (b_vals sh) (2 * N) (t_vals tb)).
    - split.
      + assumption.
      + lia.
    - intros m1 v1 [Avals1 Hun1]. normal. transfer Hun1 Hnd'. keep_mem m1.
      (* zero(s->tr, s->nv); *)
      run. call zero_fun (zero_correct (b_tr sh) N (t_tr tb)).
      + split.
        * assumption.
        * lia.
      + intros m2 v2 [Atr2 Hun2]. normal. transfer Hun2 Hnd'. keep_mem m2.
        (* zero(s->phs, s->nv); *)
        run. call zero_fun (zero_correct (b_phs sh) N (t_phs tb)).
        * split.
          -- assumption.
          -- lia.
        * intros m3 v3 [Aphs3 Hun3]. normal. transfer Hun3 Hnd'. keep_mem m3.
          (* zero(s->mrk, n); *)
          run. call zero_fun (zero_correct (b_mrk sh) (2 * N) (t_mrk tb)).
          -- split.
             ++ assumption.
             ++ lia.
          -- intros m4 v4 [Amrk4 Hun4]. normal. transfer Hun4 Hnd'. keep_mem m4.
             (* zero(s->wlen, n); *)
             run. call zero_fun (zero_correct (b_wlen sh) (2 * N) (t_wlen tb)).
             ++ split.
                ** assumption.
                ** lia.
             ++ intros m5 v5 [Awlen5 Hun5]. normal. transfer Hun5 Hnd'. keep_mem m5.
                (* zero(s->rsn, s->nv); *)
                run. call zero_fun (zero_correct (b_rsn sh) N (t_rsn tb)).
                ** split.
                   --- assumption.
                   --- lia.
                ** intros m6 v6 [Arsn6 Hun6]. normal. transfer Hun6 Hnd'. keep_mem m6.
                   (* zero(s->lvl, s->nv); *)
                   run. call zero_fun (zero_correct (b_lvl sh) N (t_lvl tb)).
                   --- split.
                       +++ assumption.
                       +++ lia.
                   --- intros m7 v7 [Alvl7 Hun7]. normal. transfer Hun7 Hnd'.
                       keep_mem m7.
                       apply (init_clear_heur_correct zl tb fl).
                       +++ assumption.
                       +++ constructor; assumption.
                       +++ tmp.
  Qed.
End Phases.

(* init rejects an empty set of atoms, and sets up the solver in four phases otherwise:

     {{ IRep m sh N lss rc tw tc }}
       if (s->nv < 1) return 0;
     {{ result = 0 }}
       int n = 2 * s->nv;
       ...                                                         (init_clear_correct)
     {{ InitPost }}                                                                *)
Theorem init_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit)) (rc: nat)
  (tw tc: nat -> Z),
  InitInput sh N lss tw tc ->
  {{ m | IRep m sh N lss rc tw tc }}
    f_init(sptr sh)
  {{ m', v | InitPost sh N lss rc m' v }}.
Proof.
  intros sh N lss rc tw tc HIn m (zl & tb & fl & HSe).
  pose proof (sz_n (in_sizes HIn)) as HN.
  pose proof (se_nv HSe) as Fnv.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_init. cbn [fn_body fn_return].
    (* if (s->nv < 1) return 0; *)
    run. branch _ 1.
    + (* no atoms: return 0; *)
      intros _. return_int.
      now left.
    + (* int n = 2 * s->nv; and the four phases *)
      intros HN1_z. assert (HN1: (1 <= N)%nat) by lia.
      assert (Hmul: Int.mul (Int.repr 2) (Int.repr (Z.of_nat N))
                    = Int.repr (Z.of_nat (2 * N))).
      { rewrite mul_repr. f_equal. lia. }
      apply exec_skip. normal. apply exec_seq. apply exec_seq.
      eapply exec_set.
      * ev.
      * apply seqk_normal. eapply exec_set.
        -- ev.
        -- apply seqk_normal.
           apply (init_clear_correct sh N lss rc tw tc HIn zl tb fl).
           ++ assumption.
           ++ assumption.
           ++ tmp.
           ++ cbn [cast_int_int]. ints. tmp.
Qed.

Lemma init_fun: FunAt _init f_init.
Proof. apply find_fun. reflexivity. Qed.