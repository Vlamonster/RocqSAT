(* init sets up the initial context (initial_of) for the clauses in memory, or rejects
   them. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Propagate Analysis Step
  CStep.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep Wpush Zero
  CheckClauses CheckLits CheckRoom Index.
Import ListNotations.

(* The memory before init: the clauses in place, the watch lists laid out by the caller
   in tables tw and tc, the room rc for the literals of the reason clauses, and the other
   tables and fields with any contents. *)
Record IRep (m: mem) (S: Shape) (N: nat) (lss: list (list Lit)) (rc: nat)
  (tw tc: nat -> Z): Prop := {
  i_nodup: NoDup (iblocks S);
  i_nv: Fld m (b_s S) 0 Mint32 (vint (Z.of_nat N));
  i_ncl: Fld m (b_s S) 4 Mint32 (vint (Z.of_nat (length lss)));
  i_cstart: Fld m (b_s S) 8 Mptr (Vptr (b_cstart S) Ptrofs.zero);
  i_clits: Fld m (b_s S) 16 Mptr (Vptr (b_clits S) Ptrofs.zero);
  i_vals: Fld m (b_s S) 24 Mptr (Vptr (b_vals S) Ptrofs.zero);
  i_wpool: Fld m (b_s S) 32 Mptr (Vptr (b_wpool S) Ptrofs.zero);
  i_npool: Fld m (b_s S) 40 Mint32 (vint (Z.of_nat (npool S)));
  i_woff: Fld m (b_s S) 48 Mptr (Vptr (b_woff S) Ptrofs.zero);
  i_wlen: Fld m (b_s S) 56 Mptr (Vptr (b_wlen S) Ptrofs.zero);
  i_wcap: Fld m (b_s S) 64 Mptr (Vptr (b_wcap S) Ptrofs.zero);
  i_tr: Fld m (b_s S) 72 Mptr (Vptr (b_tr S) Ptrofs.zero);
  i_tlen: exists (v: val), Fld m (b_s S) 80 Mint32 v;
  i_qhead: exists (v: val), Fld m (b_s S) 84 Mint32 v;
  i_shorts: Fld m (b_s S) 88 Mptr (Vptr (b_shorts S) Ptrofs.zero);
  i_nshorts: exists (v: val), Fld m (b_s S) 96 Mint32 v;
  i_alls: Fld m (b_s S) 104 Mptr (Vptr (b_alls S) Ptrofs.zero);
  i_nlits: exists (zl: Z), Small zl /\ Fld m (b_s S) 112 Mint32 (vint zl);
  i_cur: exists (v: val), Fld m (b_s S) 116 Mint32 v;
  i_saved: Fld m (b_s S) 120 Mptr (Vptr (b_saved S) Ptrofs.zero);
  i_lims: Fld m (b_s S) 128 Mptr (Vptr (b_lims S) Ptrofs.zero);
  i_dl: exists (v: val), Fld m (b_s S) 136 Mint32 v;
  i_phs: Fld m (b_s S) 144 Mptr (Vptr (b_phs S) Ptrofs.zero);
  i_mrk: Fld m (b_s S) 152 Mptr (Vptr (b_mrk S) Ptrofs.zero);
  i_rsn: Fld m (b_s S) 160 Mptr (Vptr (b_rsn S) Ptrofs.zero);
  i_lvl: Fld m (b_s S) 168 Mptr (Vptr (b_lvl S) Ptrofs.zero);
  i_lt: Fld m (b_s S) 176 Mptr (Vptr (b_lt S) Ptrofs.zero);
  i_ltlen: exists (v: val), Fld m (b_s S) 184 Mint32 v;
  i_rlits: Fld m (b_s S) 192 Mptr (Vptr (b_rlits S) Ptrofs.zero);
  i_rcap: Fld m (b_s S) 200 Mint32 (vint (Z.of_nat rc));
  i_rtop: exists (v: val), Fld m (b_s S) 204 Mint32 v;
  i_rbeg: Fld m (b_s S) 208 Mptr (Vptr (b_rbeg S) Ptrofs.zero);
  i_rlen: Fld m (b_s S) 216 Mptr (Vptr (b_rlen S) Ptrofs.zero);
  i_rpos: Fld m (b_s S) 224 Mptr (Vptr (b_rpos S) Ptrofs.zero);
  i_nr: exists (v: val), Fld m (b_s S) 232 Mint32 v;
  i_rcap_small: Z.of_nat rc < 1073741824;
  i_starts: Arr m (b_cstart S) (Datatypes.S (length lss))
    (fun (i: nat) => Z.of_nat (starts S i));
  i_lits: Arr m (b_clits S) (nclits S) (fun (q: nat) => key (lits S q));
  i_avals: exists (t: nat -> Z), Arr m (b_vals S) (2 * N) t;
  i_apool: exists (t: nat -> Z), Arr m (b_wpool S) (2 * npool S) t;
  i_awoff: Arr m (b_woff S) (2 * N) tw;
  i_awlen: exists (t: nat -> Z), Arr m (b_wlen S) (2 * N) t;
  i_awcap: Arr m (b_wcap S) (2 * N) tc;
  i_atr: exists (t: nat -> Z), Arr m (b_tr S) N t;
  i_ashorts: exists (t: nat -> Z), Arr m (b_shorts S) (length lss) t;
  i_aalls: exists (t: nat -> Z), Arr m (b_alls S) (2 * N) t /\
    forall (k: nat), (k < 2 * N)%nat -> Small (t k);
  i_asaved: exists (t: nat -> Z), Arr m (b_saved S) N t;
  i_alims: exists (t: nat -> Z), Arr m (b_lims S) N t;
  i_aphs: exists (t: nat -> Z), Arr m (b_phs S) N t;
  i_amrk: exists (t: nat -> Z), Arr m (b_mrk S) (2 * N) t;
  i_arsn: exists (t: nat -> Z), Arr m (b_rsn S) N t;
  i_alvl: exists (t: nat -> Z), Arr m (b_lvl S) N t;
  i_alt: exists (t: nat -> Z), Arr m (b_lt S) N t;
  i_arlits: exists (t: nat -> Z), Arr m (b_rlits S) rc t;
  i_arbeg: exists (t: nat -> Z), Arr m (b_rbeg S) N t;
  i_arlen: exists (t: nat -> Z), Arr m (b_rlen S) N t;
  i_arpos: exists (t: nat -> Z), Arr m (b_rpos S) N t
}.

(* The shape S with the watch lists laid out as offs and caps. *)
Definition with_room (S: Shape) (o c: nat -> nat): Shape :=
mkShape (b_s S) (b_cstart S) (b_clits S) (b_vals S) (b_wpool S) (b_woff S) (b_wlen S)
  (b_wcap S) (b_tr S) (b_shorts S) (b_alls S) (b_saved S) (b_lims S) (b_phs S) (b_mrk S)
  (b_rsn S) (b_lvl S) (b_lt S) (b_rlits S) (b_rbeg S) (b_rlen S) (b_rpos S) (starts S)
  (lits S) (nclits S) o c (npool S).

(* The initial context is the indexed one, with its short clauses. *)
Lemma initial_of_idx: forall (lss: list (list Lit)) (ls: list Lit) (nv rc: nat),
  initial_of lss ls nv rc =
  mkCtx (tmake None) (icm (idx lss (length lss))) (iwl (idx lss (length lss)))
    (tmake (Pos 0%nat)) 0%nat 0%nat
    (ish (idx lss (length lss))) (fill (tmake (Pos 0%nat)) 0%nat ls) (length ls) 0%nat []
    (tmake no_reason) (tmake 0%nat) 0%nat (tmake false) (tmake None) nv (tmake [])
    (tmake 0%nat) 0%nat rc.
Proof.
  intros lss ls nv rc. unfold initial_of, idx. rewrite firstn_all.
  now destruct (index 0%nat lss (tmake None) (tmake []) []) as [[cm wl] sh].
Qed.

(* The positions of the clauses cover the literals from position 0 to the end. *)
Lemma cover_range: forall (st: nat -> nat) (n q: nat),
  st 0%nat = 0%nat ->
  (forall (i: nat), (i < n)%nat -> (st i <= st (Datatypes.S i))%nat) ->
  (q < st n)%nat -> exists (i: nat), (i < n)%nat /\ (st i <= q < st (Datatypes.S i))%nat.
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
    + exists n. split.
      * lia.
      * lia.
Qed.

(* The literals of the clauses lss are those at the positions of the clause literals. *)
Lemma cover: forall (S: Shape) (lss: list (list Lit)) (l: Lit),
  (forall (i: nat), (i < length lss)%nat ->
    (starts S i <= starts S (Datatypes.S i) <= nclits S)%nat /\
    nth i lss [] =
      map (lits S) (seq (starts S i) (starts S (Datatypes.S i) - starts S i))) ->
  starts S 0%nat = 0%nat -> starts S (length lss) = nclits S ->
  (exists (q: nat), (q < nclits S)%nat /\ lits S q = l) <->
  exists (cs: list Lit), In cs lss /\ In l cs.
Proof.
  intros S lss l Hclauses H0 Hend. split.
  - intros [q [Hq <-]]. rewrite <- Hend in Hq.
    destruct (cover_range (starts S) (length lss) q H0) as [i [Hi Hrange]].
    + intros i Hi. now apply Hclauses.
    + assumption.
    + exists (nth i lss []). split.
      * now apply nth_In.
      * destruct (Hclauses i Hi) as [_ ->]. apply in_map. apply in_seq. lia.
  - intros [cs [Hcs Hl]]. apply In_nth with (d := []) in Hcs as [i [Hi <-]].
    destruct (Hclauses i Hi) as [Hrange Heq].
    rewrite Heq in Hl. apply in_map_iff in Hl as [q [<- Hq]]. apply in_seq in Hq.
    exists q.
    split.
    + lia.
    + reflexivity.
Qed.

(* When the literals of every clause have atoms below N, so do all clause literals. *)
Lemma lits_below: forall (S: Shape) (N: nat) (lss: list (list Lit)),
  (forall (i: nat), (i < length lss)%nat ->
    (starts S i <= starts S (Datatypes.S i) <= nclits S)%nat /\
    nth i lss [] =
      map (lits S) (seq (starts S i) (starts S (Datatypes.S i) - starts S i))) ->
  starts S 0%nat = 0%nat -> starts S (length lss) = nclits S ->
  (forall (i: nat) (l: Lit), (i < length lss)%nat -> In l (nth i lss []) ->
     (extract l < N)%nat) ->
  forall (q: nat), (q < nclits S)%nat -> (extract (lits S q) < N)%nat.
Proof.
  intros S N lss Hclauses H0 Hend Hat q Hq.
  assert (Hq': exists (q': nat), (q' < nclits S)%nat /\ lits S q' = lits S q).
  { exists q. split.
    - assumption.
    - reflexivity. }
  destruct (proj1 (cover S lss (lits S q) Hclauses H0 Hend) Hq') as [cs [Hcs Hl]].
  apply In_nth with (d := []) in Hcs as [i [Hi <-]]. now apply (Hat i).
Qed.

(* What init is given about its input besides the memory: the clause layout, the sizes,
   and the bounds of the room of the watch lists. *)
Record InitInput (S: Shape) (N: nat) (lss: list (list Lit)) (tw tc: nat -> Z): Prop := {
  in_clauses: forall (i: nat), (i < length lss)%nat ->
    (starts S i <= starts S (Datatypes.S i) <= nclits S)%nat /\
    nth i lss [] =
      map (lits S) (seq (starts S i) (starts S (Datatypes.S i) - starts S i));
  in_first: starts S 0%nat = 0%nat;
  in_end: starts S (length lss) = nclits S;
  in_n: Z.of_nat N < 268435456;
  in_nclits: Z.of_nat (nclits S) < 1073741824;
  in_lss: Z.of_nat (length lss) < 1073741824;
  in_npool: Z.of_nat (npool S) < 1073741824;
  in_keys: forall (q: nat), (q < nclits S)%nat -> key (lits S q) < 1073741824;
  in_room: forall (k: nat), (k < 2 * N)%nat -> Small (tw k) /\ Small (tc k);
}.

(* The memory during init: the fields and the arrays, with the contents of the tables
   and fields that init sets as parameters. *)
Record Setup (m: mem) (S: Shape) (N: nat) (lss: list (list Lit)) (rc: nat)
  (tw tc tv tp twl ttr tsh ta tsv tl tph tm trs tlv tlt trl trb trn trp: nat -> Z)
  (vt vq vn vl vc vd vlt vrt vnr: val): Prop := {
  se_nodup: NoDup (iblocks S);
  se_nv: Fld m (b_s S) 0 Mint32 (vint (Z.of_nat N));
  se_ncl: Fld m (b_s S) 4 Mint32 (vint (Z.of_nat (length lss)));
  se_cstart: Fld m (b_s S) 8 Mptr (Vptr (b_cstart S) Ptrofs.zero);
  se_clits: Fld m (b_s S) 16 Mptr (Vptr (b_clits S) Ptrofs.zero);
  se_vals: Fld m (b_s S) 24 Mptr (Vptr (b_vals S) Ptrofs.zero);
  se_wpool: Fld m (b_s S) 32 Mptr (Vptr (b_wpool S) Ptrofs.zero);
  se_npool: Fld m (b_s S) 40 Mint32 (vint (Z.of_nat (npool S)));
  se_woff: Fld m (b_s S) 48 Mptr (Vptr (b_woff S) Ptrofs.zero);
  se_wlen: Fld m (b_s S) 56 Mptr (Vptr (b_wlen S) Ptrofs.zero);
  se_wcap: Fld m (b_s S) 64 Mptr (Vptr (b_wcap S) Ptrofs.zero);
  se_tr: Fld m (b_s S) 72 Mptr (Vptr (b_tr S) Ptrofs.zero);
  se_tlen: Fld m (b_s S) 80 Mint32 vt;
  se_qhead: Fld m (b_s S) 84 Mint32 vq;
  se_shorts: Fld m (b_s S) 88 Mptr (Vptr (b_shorts S) Ptrofs.zero);
  se_nshorts: Fld m (b_s S) 96 Mint32 vn;
  se_alls: Fld m (b_s S) 104 Mptr (Vptr (b_alls S) Ptrofs.zero);
  se_nlits: Fld m (b_s S) 112 Mint32 vl;
  se_cur: Fld m (b_s S) 116 Mint32 vc;
  se_saved: Fld m (b_s S) 120 Mptr (Vptr (b_saved S) Ptrofs.zero);
  se_lims: Fld m (b_s S) 128 Mptr (Vptr (b_lims S) Ptrofs.zero);
  se_dl: Fld m (b_s S) 136 Mint32 vd;
  se_phs: Fld m (b_s S) 144 Mptr (Vptr (b_phs S) Ptrofs.zero);
  se_mrk: Fld m (b_s S) 152 Mptr (Vptr (b_mrk S) Ptrofs.zero);
  se_rsn: Fld m (b_s S) 160 Mptr (Vptr (b_rsn S) Ptrofs.zero);
  se_lvl: Fld m (b_s S) 168 Mptr (Vptr (b_lvl S) Ptrofs.zero);
  se_lt: Fld m (b_s S) 176 Mptr (Vptr (b_lt S) Ptrofs.zero);
  se_ltlen: Fld m (b_s S) 184 Mint32 vlt;
  se_rlits: Fld m (b_s S) 192 Mptr (Vptr (b_rlits S) Ptrofs.zero);
  se_rcap: Fld m (b_s S) 200 Mint32 (vint (Z.of_nat rc));
  se_rtop: Fld m (b_s S) 204 Mint32 vrt;
  se_rbeg: Fld m (b_s S) 208 Mptr (Vptr (b_rbeg S) Ptrofs.zero);
  se_rlen: Fld m (b_s S) 216 Mptr (Vptr (b_rlen S) Ptrofs.zero);
  se_rpos: Fld m (b_s S) 224 Mptr (Vptr (b_rpos S) Ptrofs.zero);
  se_nr: Fld m (b_s S) 232 Mint32 vnr;
  se_rcap_small: Z.of_nat rc < 1073741824;
  se_astarts: Arr m (b_cstart S) (Datatypes.S (length lss))
    (fun (i: nat) => Z.of_nat (starts S i));
  se_alits: Arr m (b_clits S) (nclits S) (fun (q: nat) => key (lits S q));
  se_avals: Arr m (b_vals S) (2 * N) tv;
  se_apool: Arr m (b_wpool S) (2 * npool S) tp;
  se_awoff: Arr m (b_woff S) (2 * N) tw;
  se_awlen: Arr m (b_wlen S) (2 * N) twl;
  se_awcap: Arr m (b_wcap S) (2 * N) tc;
  se_atr: Arr m (b_tr S) N ttr;
  se_ashorts: Arr m (b_shorts S) (length lss) tsh;
  se_aalls: Arr m (b_alls S) (2 * N) ta;
  se_asaved: Arr m (b_saved S) N tsv;
  se_alims: Arr m (b_lims S) N tl;
  se_aphs: Arr m (b_phs S) N tph;
  se_amrk: Arr m (b_mrk S) (2 * N) tm;
  se_arsn: Arr m (b_rsn S) N trs;
  se_alvl: Arr m (b_lvl S) N tlv;
  se_alt: Arr m (b_lt S) N tlt;
  se_arlits: Arr m (b_rlits S) rc trl;
  se_arbeg: Arr m (b_rbeg S) N trb;
  se_arlen: Arr m (b_rlen S) N trn;
  se_arpos: Arr m (b_rpos S) N trp;
}.

(* What init gives: 0 to reject the input, or 1 with the initial context in memory. *)
Definition InitPost (S: Shape) (N: nat) (lss: list (list Lit)) (rc: nat) (m': mem)
  (v: val): Prop :=
  v = vint 0 \/
  (v = vint 1 /\ (1 <= N)%nat /\ exists (offs caps: nat -> nat) (acc: list Lit),
     Rep m' (with_room S offs caps) N lss (initial_of lss acc N rc) [] /\
     (forall (i: nat), (i < length lss)%nat -> NoDup (nth i lss [])) /\
     forall (l: Lit), In l acc <-> exists (cs: list Lit), In cs lss /\ In l cs).

(* The zero table. *)
Definition zeros: nat -> Z := fun (_: nat) => 0.

(* The phases of init, each proved in a lemma of its own: clearing the tables, setting
   the fields, the checks, and indexing the clauses. *)
Definition init_clear: statement := drop_stmts 2 (fn_body f_init).
Definition init_fields: statement := drop_stmts 9 (fn_body f_init).
Definition init_checks: statement := drop_stmts 17 (fn_body f_init).
Definition init_index: statement := drop_stmts 20 (fn_body f_init).

(* The shape with the watch lists laid out as the caller asked, in tw and tc. *)
Definition room_shape (S: Shape) (tw tc: nat -> Z): Shape :=
  with_room S (fun (k: nat) => Z.to_nat (tw k)) (fun (k: nat) => Z.to_nat (tc k)).

(* After the checks: the memory represents the context ictx with the clause literals acc
   to decide on, no watches yet, no marks, levels and reasons, and the watch lists laid
   out as the caller asked. *)
Lemma setup_rep: forall (m: mem) (S: Shape) (N: nat) (lss: list (list Lit)) (rc: nat)
  (tw tc tp tsh ta tsv tl tlt trl trb trn trp: nat -> Z) (acc: list Lit),
  InitInput S N lss tw tc -> (1 <= N)%nat ->
  Setup m S N lss rc tw tc zeros tp zeros zeros tsh ta tsv tl zeros zeros zeros zeros tlt
    trl trb trn trp (vint 0) (vint 0) (vint 0) (vint (Z.of_nat (length acc))) (vint 0)
    (vint 0) (vint 0) (vint 0) (vint 0) ->
  (forall (i: nat) (l: Lit), (i < length lss)%nat -> In l (nth i lss []) ->
     (extract l < N)%nat) ->
  NoDup acc -> (length acc <= 2 * N)%nat ->
  (forall (l: Lit), In l acc <-> exists (q: nat), (q < nclits S)%nat /\ lits S q = l) ->
  (forall (k: nat), (k < length acc)%nat -> ta k = key (nth k acc (Pos 0%nat))) ->
  Fits tw tc (2 * N) (Z.of_nat (npool S)) -> InOrder tw tc (2 * N) ->
  Rep m (room_shape S tw tc) N lss
    (ictx lss (fill (tmake (Pos 0%nat)) 0%nat acc) (length acc) N rc 0) [].
Proof.
  intros m S N lss rc tw tc tp tsh ta tsv tl tlt trl trb trn trp acc HIn HN1 HSe Hat
    Hndacc Hlacc Hacc Hta Hroom Horder.
  destruct HIn as [Hclauses H0 Hend HN Hncl Hlss Hnp Hkeys Hsmall].
  destruct HSe as [Hnd Fnv Fncl Fcs Fcl Fvals Fpool Fnp Fwoff Fwlen Fwcap
    Ftr Ftlen Fqh Fsh Fns Falls Fnl Fcur Fsv Flims Fdl Fphs Fmrk Frsn Flvl Flt Fltlen
    Frl Frcap Frtop Frb Frn Frp Fnr Hrc Ast Alits Avals Apool Awoff Awlen Awcap Atr Ash
    Aalls Asaved Alims Aphs Amrk Arsn Alvl Alt Arl Arb Arn Arp].
  pose proof Hnd as Hnd'. unfold iblocks in Hnd'.
  set (al := fill (tmake (Pos 0%nat)) 0%nat acc).
  assert (Hal: forall (k: nat), (k < length acc)%nat ->
                 tget al k = nth k acc (Pos 0%nat)).
  { intros k Hk. subst al. rewrite <- (Nat.add_0_l k), fill_spec by assumption.
    reflexivity. }
  pose proof (lits_below S N lss Hclauses H0 Hend Hat) as Hlat.
  split.
  - (* Every field holds what the shape and ictx say, but the following ones. *)
    constructor; try assumption.
    + (* the clauses, at their positions of clits *)
      exists (fun (q: nat) => key (lits S q)). split.
      * assumption.
      * split.
        -- intros q Hq. exists (lits S q). split.
           ++ reflexivity.
           ++ apply Hlat. assumption.
        -- intros i Hi. cbn [ictx cmap]. rewrite idx_cm by lia.
           replace (i <? length lss)%nat with true by (symmetry; now apply Nat.ltb_lt).
           destruct (Hclauses i Hi) as [_ Heq]. rewrite Heq. f_equal. apply map_ext.
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
      exists tsh. split.
      * assumption.
      * intros q Hq. cbn [ictx shorts length] in Hq. lia.
    + (* the literals to decide on *)
      exists ta. split.
      * assumption.
      * intros k Hk. cbn [ictx alls nlits] in *. rewrite Hta, Hal by assumption.
        reflexivity.
    + (* no saved cursor *)
      exists tsv. split.
      * assumption.
      * intros k Hk. cbn [ictx saved length] in Hk. lia.
    + (* no decision *)
      exists tl. split.
      * assumption.
      * intros k Hk. cbn [length] in Hk. lia.
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
      cbn [length]. lia.
    + (* no lower literals of an analysis *)
      exists tlt. split.
      * assumption.
      * intros k Hk. cbn [length] in Hk. lia.
    + (* no reason clauses: their literals *)
      exists trl. split.
      * assumption.
      * intros j k Hj. cbn [ictx nr] in Hj. lia.
    + (* their starts *)
      exists trb. split.
      * assumption.
      * intros j Hj. cbn [ictx nr] in Hj. lia.
    + (* their lengths *)
      exists trn. split.
      * assumption.
      * intros j Hj. cbn [ictx nr] in Hj. lia.
    + (* their trail positions *)
      exists trp. split.
      * assumption.
      * intros j Hj. cbn [ictx nr] in Hj. lia.
    + (* no decision *)
      reflexivity.
    + (* no reasons *)
      intros a Ha. cbn [ictx rsn]. rewrite tget_tmake. cbn [ReasonBelow]. apply I.
    + (* all levels 0 *)
      intros a Ha. cbn [ictx lvl]. rewrite tget_tmake. lia.
    + (* no lower literals *)
      cbn [length]. lia.
    + intros y [].
    + (* no reason clauses *)
      cbn [ictx nr]. lia.
    + cbn [ictx nr rcl reasons_size]. lia.
    + intros j y Hj. cbn [ictx nr] in Hj. lia.
    + intros j Hj. cbn [ictx nr] in Hj. lia.
  - (* the pool holds the empty watch lists *)
    exists tp. split.
    + assumption.
    + intros k q Hk Hq. unfold idx in Hq. cbn in Hq. rewrite tget_tmake in Hq. cbn in Hq.
      lia.
Qed.


(* The last phase: indexing the clauses, which sets the watches and the short clauses:

     {{ Rep (ictx ... 0) /\ the array of short clauses }}
       int ns = index_clauses(s);                              (index_clauses_correct)
       if (ns < 0) return 0;
     {{ result = 0 (out of room) }}
     {{ Rep (ictx ... (length lss)) /\ the short clauses are in their array }}
       s->nshorts = ns;                                              (rep_store_shorts)
       return 1;
     {{ result = 1 /\ Rep (initial_of lss acc N rc) }}                               *)
Lemma init_index_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (rc: nat)
  (tw tc: nat -> Z) (acc: list Lit) (tsh: nat -> Z) (le: temp_env) (m: mem),
  (1 <= N)%nat ->
  (forall (i: nat), (i < length lss)%nat -> NoDup (nth i lss [])) ->
  (forall (l: Lit), In l acc <-> exists (cs: list Lit), In cs lss /\ In l cs) ->
  Rep m (room_shape S tw tc) N lss
    (ictx lss (fill (tmake (Pos 0%nat)) 0%nat acc) (length acc) N rc 0) [] ->
  Arr m (b_shorts S) (length lss) tsh ->
  le ! _s = Some (sptr S) ->
  Exec ge le m init_index (Returns f_init (InitPost S N lss rc)).
Proof.
  intros S N lss rc tw tc acc tsh le m HN1 Hndc Hacc HRep0 Ash Hs.
  set (S' := room_shape S tw tc) in *.
  set (al := fill (tmake (Pos 0%nat)) 0%nat acc) in *.
  pose proof (r_lss_small _ _ _ _ _ _ _ (proj1 HRep0)) as Hlss.
  unfold init_index, f_init. cbn [fn_body drop_stmts].
  (* int ns = index_clauses(s); *)
  run. call index_clauses_fun. eapply call_weaken.
  - apply (index_clauses_correct S' N lss al (length acc) rc tsh m). split.
    + assumption.
    + split.
      * assumption.
      * assumption.
  - intros m1 v Hv. normal. run.
    destruct Hv as [-> | (tsh' & -> & [HRep1 Hpool1] & Ash1 & Htsh1)].
    + (* out of room: if (ns < 0) return 0; *)
      eapply (exec_if_cmp _ _ _ Clt _ _ (-1) 0).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * change (zcmp Clt (-1) 0) with true. cbv beta iota. eapply exec_return.
        -- ev.
        -- ret. exists (vint 0). split.
           ++ apply result_int.
           ++ now left.
    + (* the short clauses ns: s->nshorts = ns; return 1; *)
      pose proof (idx_lists lss (length lss) (le_n _)) as (_ & Hshc & Hshl).
      eapply (exec_if_cmp _ _ _ Clt _ _ _ 0).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * replace (zcmp Clt (Z.of_nat (length (ish (idx lss (length lss))))) 0) with false
          by (symmetry; cbn [zcmp]; apply Z.ltb_ge; lia).
        cbv beta iota. keep_mem m1.
        pose proof (Rep.r_nodup _ _ _ _ _ _ _ HRep1) as Hnd.
        pose proof (Rep.r_nshorts _ _ _ _ _ _ _ HRep1) as Fns1.
        unfold S', room_shape, with_room in *.
        cbn [b_s b_shorts b_wpool] in Fns1, Ash1, Hnd, Hpool1.
        run. eapply exec_store.
        -- evl.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- fofs. bound.
        -- fofs. cbn [cast_int_int].
           destruct (fld_storable m1 (b_s S) 96 Mint32 _
                       (vint (Z.of_nat (length (ish (idx lss (length lss)))))) Fns1)
             as [m2 Hst2].
           exists m2. split.
           ++ apply Hst2.
           ++ normal.
              pose proof (rep_store_shorts m1 m2 _ N lss _ [] _ tsh' HRep1 Ash1 Htsh1
                            Hshl Hshc Hst2) as HRep2.
              eapply exec_return.
              ** ev.
              ** exists (vint 1). split.
                 --- apply result_int.
                 --- right. split.
                     +++ reflexivity.
                     +++ split.
                         *** assumption.
                         *** exists (fun (k: nat) => Z.to_nat (tw k)),
                               (fun (k: nat) => Z.to_nat (tc k)), acc.
                             split.
                             ---- rewrite initial_of_idx. split.
                                  ++++ apply HRep2.
                                  ++++ destruct Hpool1 as [tp [Apool1 Hpool1]].
                                       exists tp. split.
                                       **** apply (arr_store_other _ _ _ _ _ _ _ _ _
                                                     Apool1 Hst2).
                                            neq Hnd.
                                       **** assumption.
                             ---- split; assumption.
Qed.

(* The checks, after the tables and fields are cleared:

     {{ Setup (cleared) }}
       if (!check_clauses(s)) return 0;                           (check_clauses_correct)
     {{ result = 0: a literal out of range or twice in a clause }}
       if (!check_lits(s)) return 0;                                (check_lits_correct)
     {{ result = 0: alls is not the literals of the clauses, each once }}
       if (!check_room(s)) return 0;                                (check_room_correct)
     {{ result = 0: the watch lists do not fit }}
     {{ Rep (ictx ... 0) }}                                                  (setup_rep)
       ...                                                     (init_index_correct)  *)
Lemma init_checks_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (rc: nat)
  (tw tc tp tsh ta tsv tl tlt trl trb trn trp: nat -> Z) (zl: Z) (le: temp_env)
  (m: mem),
  InitInput S N lss tw tc -> (1 <= N)%nat ->
  Setup m S N lss rc tw tc zeros tp zeros zeros tsh ta tsv tl zeros zeros zeros zeros tlt
    trl trb trn trp (vint 0) (vint 0) (vint 0) (vint zl) (vint 0) (vint 0) (vint 0)
    (vint 0) (vint 0) ->
  Small zl -> (forall (k: nat), (k < 2 * N)%nat -> Small (ta k)) ->
  le ! _s = Some (sptr S) ->
  Exec ge le m init_checks (Returns f_init (InitPost S N lss rc)).
Proof.
  intros S N lss rc tw tc tp tsh ta tsv tl tlt trl trb trn trp zl le m HIn HN1 HSe Hzl
    Hta Hs.
  pose proof HIn as HIn'.
  destruct HIn' as [Hclauses H0 Hend HN Hncl Hlss Hnp Hkeys Hsmall].
  destruct HSe as [Hnd Fnv Fncl Fcs Fcl Fvals Fpool Fnp Fwoff Fwlen Fwcap
    Ftr Ftlen Fqh Fsh Fns Falls Fnl Fcur Fsv Flims Fdl Fphs Fmrk Frsn Flvl Flt Fltlen
    Frl Frcap Frtop Frb Frn Frp Fnr Hrc Ast Alits Avals Apool Awoff Awlen Awcap Atr Ash
    Aalls Asaved Alims Aphs Amrk Arsn Alvl Alt Arl Arb Arn Arp].
  pose proof Hnd as Hnd'. unfold iblocks in Hnd'.
  unfold init_checks, f_init. cbn [fn_body drop_stmts].
  (* if (!check_clauses(s)) return 0; *)
  run. call check_clauses_fun. eapply call_weaken.
  - apply (check_clauses_correct S N lss zeros m). repeat (split; [assumption | ]).
    intros k Hk. reflexivity.
  - intros m1 v Hv. normal. run.
    destruct Hv as [-> | (-> & Hat & Hndc & (tm1 & Amrk1 & Hm1) & Hun1)].
    + (* a literal out of range or twice in a clause: return 0; *)
      eapply (exec_if_int _ _ _ _ 1).
      * ev.
      * reflexivity.
      * unfold Small. lia.
      * change (negb (Z.eqb 1 0)) with true. cbv beta iota. eapply exec_return.
        -- ev.
        -- ret. exists (vint 0). split.
           ++ apply result_int.
           ++ now left.
    + eapply (exec_if_int _ _ _ _ 0).
      * ev.
      * reflexivity.
      * unfold Small. lia.
      * change (negb (Z.eqb 0 0)) with false. cbv beta iota.
        transfer Hun1 Hnd'. keep_mem m1.
        (* the literals of the clauses have atoms below N *)
        pose proof (lits_below S N lss Hclauses H0 Hend Hat) as Hlat.
        (* if (!check_lits(s)) return 0; *)
        run. call check_lits_fun. eapply call_weaken.
        -- apply (check_lits_correct S N lss zl ta tm1 m1). constructor; assumption.
        -- intros m2 v ((tm2 & Amrk2) & Hun2 & Hv). normal. transfer Hun2 Hnd'.
           keep_mem m2. run.
           destruct Hv
             as [-> | (-> & Amrk0 & acc & Hzacc & Hndacc & Hlacc & Hacc & Hta2)].
           ++ (* alls is not the clause literals, once each: return 0; *)
              eapply (exec_if_int _ _ _ _ 1).
              ** ev.
              ** reflexivity.
              ** unfold Small. lia.
              ** change (negb (Z.eqb 1 0)) with true. cbv beta iota. eapply exec_return.
                 --- ev.
                 --- ret. exists (vint 0). split.
                     +++ apply result_int.
                     +++ now left.
           ++ eapply (exec_if_int _ _ _ _ 0).
              ** ev.
              ** reflexivity.
              ** unfold Small. lia.
              ** change (negb (Z.eqb 0 0)) with false. cbv beta iota. apply exec_skip.
                 normal. rewrite Hzacc in Fnl.
                 (* if (!check_room(s)) return 0; *)
                 run. call check_room_fun. eapply call_weaken.
                 --- apply (check_room_correct S N tw tc).
                     repeat (split; [assumption | ]). assumption.
                 --- intros m4 v [-> Hv]. normal. run.
                     destruct Hv as [-> | (-> & Hroom & Horder)].
                     +++ (* the watch lists do not fit: return 0; *)
                         eapply (exec_if_int _ _ _ _ 1).
                         *** ev.
                         *** reflexivity.
                         *** unfold Small. lia.
                         *** change (negb (Z.eqb 1 0)) with true. cbv beta iota.
                             eapply exec_return.
                             ---- ev.
                             ---- ret. exists (vint 0). split.
                                  ++++ apply result_int.
                                  ++++ now left.
                     +++ (* the memory represents ictx: index the clauses *)
                         eapply (exec_if_int _ _ _ _ 0).
                         *** ev.
                         *** reflexivity.
                         *** unfold Small. lia.
                         *** change (negb (Z.eqb 0 0)) with false. cbv beta iota.
                             apply exec_skip. normal.
                             apply (init_index_correct S N lss rc tw tc acc tsh).
                             ---- assumption.
                             ---- assumption.
                             ---- intros l. rewrite Hacc. now apply cover.
                             ---- apply (setup_rep _ S N lss rc tw tc tp tsh ta tsv tl
                                           tlt trl trb trn trp acc).
                                  ++++ assumption.
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

     {{ Setup (tables cleared) }}
       s->tlen = 0;
       s->qhead = 0;
       s->nshorts = 0;
       s->cur = 0;
       s->dl = 0;
       s->ltlen = 0;
       s->rtop = 0;
       s->nr = 0;
     {{ Setup (tables cleared, fields 0) }}
       ...                                                      (init_checks_correct) *)
Lemma init_fields_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (rc: nat)
  (tw tc tp tsh ta tsv tl tlt trl trb trn trp: nat -> Z) (vt vq vn: val) (zl: Z)
  (vc vd vlt vrt vnr: val) (le: temp_env) (m: mem),
  InitInput S N lss tw tc -> (1 <= N)%nat ->
  Setup m S N lss rc tw tc zeros tp zeros zeros tsh ta tsv tl zeros zeros zeros zeros tlt
    trl trb trn trp vt vq vn (vint zl) vc vd vlt vrt vnr ->
  Small zl -> (forall (k: nat), (k < 2 * N)%nat -> Small (ta k)) ->
  le ! _s = Some (sptr S) ->
  Exec ge le m init_fields (Returns f_init (InitPost S N lss rc)).
Proof.
  intros S N lss rc tw tc tp tsh ta tsv tl tlt trl trb trn trp vt vq vn zl vc vd vlt vrt
    vnr le m HIn HN1 HSe Hzl Hta Hs.
  destruct HSe as [Hnd Fnv Fncl Fcs Fcl Fvals Fpool Fnp Fwoff Fwlen Fwcap
    Ftr Ftlen Fqh Fsh Fns Falls Fnl Fcur Fsv Flims Fdl Fphs Fmrk Frsn Flvl Flt Fltlen
    Frl Frcap Frtop Frb Frn Frp Fnr Hrc Ast Alits Avals Apool Awoff Awlen Awcap Atr Ash
    Aalls Asaved Alims Aphs Amrk Arsn Alvl Alt Arl Arb Arn Arp].
  pose proof Hnd as Hnd'. unfold iblocks in Hnd'.
  unfold init_fields, f_init. cbn [fn_body drop_stmts].
  (* s->tlen = 0; *)
  run. eapply exec_store.
  - evl.
  - ev.
  - reflexivity.
  - reflexivity.
  - fofs. bound.
  - fofs. store_fld Ftlen Hnd'.
    (* s->qhead = 0; *)
    run. eapply exec_store.
    + evl.
    + ev.
    + reflexivity.
    + reflexivity.
    + fofs. bound.
    + fofs. store_fld Fqh Hnd'.
      (* s->nshorts = 0; *)
      run. eapply exec_store.
      * evl.
      * ev.
      * reflexivity.
      * reflexivity.
      * fofs. bound.
      * fofs. store_fld Fns Hnd'.
        (* s->cur = 0; *)
        run. eapply exec_store.
        -- evl.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- fofs. bound.
        -- fofs. store_fld Fcur Hnd'.
           (* s->dl = 0; *)
           run. eapply exec_store.
           ++ evl.
           ++ ev.
           ++ reflexivity.
           ++ reflexivity.
           ++ fofs. bound.
           ++ fofs. store_fld Fdl Hnd'.
              (* s->ltlen = 0; *)
              run. eapply exec_store.
              ** evl.
              ** ev.
              ** reflexivity.
              ** reflexivity.
              ** fofs. bound.
              ** fofs. store_fld Fltlen Hnd'.
                 (* s->rtop = 0; *)
                 run. eapply exec_store.
                 --- evl.
                 --- ev.
                 --- reflexivity.
                 --- reflexivity.
                 --- fofs. bound.
                 --- fofs. store_fld Frtop Hnd'.
                     (* s->nr = 0; *)
                     run. eapply exec_store.
                     +++ evl.
                     +++ ev.
                     +++ reflexivity.
                     +++ reflexivity.
                     +++ fofs. bound.
                     +++ fofs. store_fld Fnr Hnd'.
                         cbn [Val.load_result] in Ftlen, Fqh, Fns, Fcur, Fdl, Fltlen,
                           Frtop, Fnr.
                         apply (init_checks_correct S N lss rc tw tc tp tsh ta tsv tl
                                  tlt trl trb trn trp zl).
                         *** assumption.
                         *** assumption.
                         *** constructor; assumption.
                         *** assumption.
                         *** assumption.
                         *** tmp.
Qed.

(* Clearing the tables that the initial context has empty:

     {{ Setup }}
       zero(s->vals, n);                                                  (zero_correct)
       zero(s->tr, s->nv);
       zero(s->phs, s->nv);
       zero(s->mrk, n);
       zero(s->wlen, n);
       zero(s->rsn, s->nv);
       zero(s->lvl, s->nv);
     {{ Setup (these seven tables are 0) }}
       ...                                                      (init_fields_correct) *)
Lemma init_clear_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (rc: nat)
  (tw tc tv tp twl ttr tsh ta tsv tl tph tm trs tlv tlt trl trb trn trp: nat -> Z)
  (vt vq vn: val) (zl: Z) (vc vd vlt vrt vnr: val) (le: temp_env) (m: mem),
  InitInput S N lss tw tc -> (1 <= N)%nat ->
  Setup m S N lss rc tw tc tv tp twl ttr tsh ta tsv tl tph tm trs tlv tlt trl trb trn trp
    vt vq vn (vint zl) vc vd vlt vrt vnr ->
  Small zl -> (forall (k: nat), (k < 2 * N)%nat -> Small (ta k)) ->
  le ! _s = Some (sptr S) ->
  le ! _n = Some (vint (Z.of_nat (2 * N))) ->
  Exec ge le m init_clear (Returns f_init (InitPost S N lss rc)).
Proof.
  intros S N lss rc tw tc tv tp twl ttr tsh ta tsv tl tph tm trs tlv tlt trl trb trn trp
    vt vq vn zl vc vd vlt vrt vnr le m HIn HN1 HSe Hzl Hta Hs Hn.
  pose proof (in_n _ _ _ _ _ HIn) as HN. pose proof (in_lss _ _ _ _ _ HIn) as Hlss.
  destruct HSe as [Hnd Fnv Fncl Fcs Fcl Fvals Fpool Fnp Fwoff Fwlen Fwcap
    Ftr Ftlen Fqh Fsh Fns Falls Fnl Fcur Fsv Flims Fdl Fphs Fmrk Frsn Flvl Flt Fltlen
    Frl Frcap Frtop Frb Frn Frp Fnr Hrc Ast Alits Avals Apool Awoff Awlen Awcap Atr Ash
    Aalls Asaved Alims Aphs Amrk Arsn Alvl Alt Arl Arb Arn Arp].
  pose proof Hnd as Hnd'. unfold iblocks in Hnd'.
  unfold init_clear, f_init. cbn [fn_body drop_stmts].
  (* zero(s->vals, n); *)
  run. call zero_fun. eapply call_weaken.
  - apply (zero_correct _ (2 * N) tv). split.
    + assumption.
    + lia.
  - intros m1 v1 [Avals1 Hun1]. normal. transfer Hun1 Hnd'. keep_mem m1.
    (* zero(s->tr, s->nv); *)
    run. call zero_fun. eapply call_weaken.
    + apply (zero_correct _ N ttr). split.
      * assumption.
      * lia.
    + intros m2 v2 [Atr2 Hun2]. normal. transfer Hun2 Hnd'. keep_mem m2.
      (* zero(s->phs, s->nv); *)
      run. call zero_fun. eapply call_weaken.
      * apply (zero_correct _ N tph). split.
        -- assumption.
        -- lia.
      * intros m3 v3 [Aphs3 Hun3]. normal. transfer Hun3 Hnd'. keep_mem m3.
        (* zero(s->mrk, n); *)
        run. call zero_fun. eapply call_weaken.
        -- apply (zero_correct _ (2 * N) tm). split.
           ++ assumption.
           ++ lia.
        -- intros m4 v4 [Amrk4 Hun4]. normal. transfer Hun4 Hnd'. keep_mem m4.
           (* zero(s->wlen, n); *)
           run. call zero_fun. eapply call_weaken.
           ++ apply (zero_correct _ (2 * N) twl). split.
              ** assumption.
              ** lia.
           ++ intros m5 v5 [Awlen5 Hun5]. normal. transfer Hun5 Hnd'. keep_mem m5.
              (* zero(s->rsn, s->nv); *)
              run. call zero_fun. eapply call_weaken.
              ** apply (zero_correct _ N trs). split.
                 --- assumption.
                 --- lia.
              ** intros m6 v6 [Arsn6 Hun6]. normal. transfer Hun6 Hnd'. keep_mem m6.
                 (* zero(s->lvl, s->nv); *)
                 run. call zero_fun. eapply call_weaken.
                 --- apply (zero_correct _ N tlv). split.
                     +++ assumption.
                     +++ lia.
                 --- intros m7 v7 [Alvl7 Hun7]. normal. transfer Hun7 Hnd'. keep_mem m7.
                     apply (init_fields_correct S N lss rc tw tc tp tsh ta tsv tl tlt trl
                              trb trn trp vt vq vn zl vc vd vlt vrt vnr).
                     +++ assumption.
                     +++ assumption.
                     +++ constructor; assumption.
                     +++ assumption.
                     +++ assumption.
                     +++ tmp.
Qed.

(* init rejects an empty set of atoms, and sets up the solver in four phases otherwise:

     {{ IRep m S N lss rc tw tc }}
       if (s->nv < 1) return 0;
     {{ result = 0 }}
       int n = 2 * s->nv;
       ...                                                         (init_clear_correct)
     {{ InitPost }}                                                                *)
Theorem init_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (rc: nat)
  (tw tc: nat -> Z),
  InitInput S N lss tw tc ->
  {{ m | IRep m S N lss rc tw tc }}
    f_init(sptr S)
  {{ m', v | InitPost S N lss rc m' v }}.
Proof.
  intros S N lss rc tw tc HIn m HI.
  pose proof (in_n _ _ _ _ _ HIn) as HN.
  destruct HI as [Hnd Fnv Fncl Fcs Fcl Fvals Fpool Fnp Fwoff Fwlen Fwcap Ftr
    [vt Ftlen] [vq Fqh] Fsh [vn Fns] Falls [zl [Hzl Fnl]] [vc Fcur] Fsv Flims [vd Fdl]
    Fphs Fmrk Frsn Flvl Flt [vlt Fltlen] Frl Frcap [vrt Frtop] Frb Frn Frp [vnr Fnr] Hrc
    Ast Alits [tv Avals] [tp Apool] Awoff [twl Awlen] Awcap [ttr Atr] [tsh Ash]
    [ta [Aalls Hta]] [tsv Asaved] [tl Alims] [tph Aphs] [tm Amrk] [trs Arsn] [tlv Alvl]
    [tlt Alt] [trl Arl] [trb Arb] [trn Arn] [trp Arp]].
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_init. cbn [fn_body fn_return].
    (* if (s->nv < 1) return 0; *)
    run. eapply (exec_if_cmp _ _ _ Clt _ _ _ 1).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + unfold Small. lia.
    + unfold Small. lia.
    + destruct (Nat.lt_ge_cases N 1) as [HN0 | HN1].
      * (* no atoms: return 0; *)
        replace (zcmp Clt (Z.of_nat N) 1) with true
          by (symmetry; cbn [zcmp]; apply Z.ltb_lt; lia).
        cbv beta iota. eapply exec_return.
        -- ev.
        -- ret. exists (vint 0). split.
           ++ apply result_int.
           ++ now left.
      * (* int n = 2 * s->nv; and the four phases *)
        replace (zcmp Clt (Z.of_nat N) 1) with false
          by (symmetry; cbn [zcmp]; apply Z.ltb_ge; lia).
        assert (Hmul: Int.mul (Int.repr 2) (Int.repr (Z.of_nat N))
                      = Int.repr (Z.of_nat (2 * N))).
        { rewrite mul_repr. f_equal. lia. }
        cbv beta iota. apply exec_skip. normal. apply exec_seq. apply exec_seq.
        eapply exec_set.
        -- ev.
        -- apply seqk_normal. eapply exec_set.
           ++ ev.
           ++ apply seqk_normal.
              apply (init_clear_correct S N lss rc tw tc tv tp twl ttr tsh ta tsv tl tph
                       tm trs tlv tlt trl trb trn trp vt vq vn zl vc vd vlt vrt vnr).
              ** assumption.
              ** assumption.
              ** constructor; assumption.
              ** assumption.
              ** assumption.
              ** tmp.
              ** cbn [cast_int_int]. ints. tmp.
Qed.

Lemma init_fun: exists (b: block),
  Genv.find_symbol ge _init = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_init).
Proof. apply find_fun. reflexivity. Qed.
