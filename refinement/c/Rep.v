(* The C solver (../solver.c) represents a context of Propagate.v, with the positions of
   its decisions: Rep says how its memory holds them. The store lemmas (rep_store_...)
   say what each store of the C code does to the represented context. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs Ctypes Cop
  Clight ClightBigstep.
From RocqSAT Require Import Lit Assignment.
From RocqSAT.refinement Require Import Table Lookup Watches Propagate Analysis Step
  CStep SolverStep.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common.
Import ListNotations.

Definition ge: genv := Clight.globalenv prog.

(* Hoare triples for the functions of the program (Triple in Logic.v):
     {{ m | P }} f(a1, ..., an) {{ m', v | Q }}
   from a memory m with P, calling f on a1 ... an terminates in a memory m' returning v
   with Q. *)
Notation "{{ m | P }} f ( x , .. , y ) {{ m' , v | Q }}" :=
  (Triple ge (fun m => P) f (cons x .. (cons y nil) ..) (fun m m' v => Q))
  (at level 0, m name, m' name, v name, f constr at level 0, x constr at level 99,
   y constr at level 99, P at level 200, Q at level 200, format
   "'[hv' {{  m  |  P  }} '/  ' f ( x ,  .. ,  y ) '/' {{  m' ,  v  |  Q  }} ']'").

(* Triples for two calls in a row (Triple2 in Logic.v), each on one argument:
     {{ m | P }} f(x); g(y) {{ m', r | Q }}
   from a memory m with P, f(x) terminates; if it returned 0, r = Rejected, and
   otherwise g(y) terminates in a memory m' returning v, and r = Returned v; Q holds. *)
Notation "{{ m | P }} f ( x ) ; g ( y ) {{ m' , r | Q }}" :=
  (Triple2 ge (fun m => P) f (cons x nil) g (cons y nil) (fun m' r => Q))
  (at level 0, m name, m' name, r name, f constr at level 0, g constr at level 0,
   x constr at level 99, y constr at level 99, P at level 200, Q at level 200, format
   "'[hv' {{  m  |  P  }} '/  ' f ( x ) ;  g ( y ) '/' {{  m' ,  r  |  Q  }} ']'").

(* A function of the program can be called through its name. *)
Lemma find_fun: forall (id: ident) (fd: fundef),
  (prog_defmap prog) ! id = Some (Gfun fd) ->
  exists (b: block),
    Genv.find_symbol ge id = Some b /\ Genv.find_funct_ptr ge b = Some fd.
Proof.
  intros id fd Hdef. apply Genv.find_def_symbol in Hdef as [b [Hsym Hdef]].
  exists b. split.
  - assumption.
  - unfold Genv.find_funct_ptr. now rewrite (Hdef: Genv.find_def ge b = Some (Gfun fd)).
Qed.

(* The blocks of the solver, the fixed layout of its clauses, and the fixed room of its
   watch lists: clause i has its literals at positions starts i .. starts (i + 1) of the
   nclits literals in block clits, at first lits, and the watch list of the literal with
   key k has room for caps k watchers from watcher offs k of the pool on. Blocks lt and
   rlits hold the lower literals of an analysis and the literals of the reason clauses;
   rbeg, rlen and rpos where each reason clause starts, its length and the trail position
   of the literal it asserted. *)
Record Shape: Type := mkShape {
  b_s: block;
  b_cstart: block;
  b_clits: block;
  b_vals: block;
  b_wpool: block;
  b_woff: block;
  b_wlen: block;
  b_wcap: block;
  b_tr: block;
  b_shorts: block;
  b_alls: block;
  b_saved: block;
  b_lims: block;
  b_phs: block;
  b_mrk: block;
  b_rsn: block;
  b_lvl: block;
  b_lt: block;
  b_rlits: block;
  b_rbeg: block;
  b_rlen: block;
  b_rpos: block;
  starts: nat -> nat;
  lits: nat -> Lit;
  nclits: nat;
  offs: nat -> nat;
  caps: nat -> nat;
  npool: nat
}.

(* The pointer to the solver struct s, the first argument of every C function. *)
Definition sptr (S: Shape): val := Vptr (b_s S) Ptrofs.zero.

(* Watcher w of the pool t is e: entry 2 w holds its clause, and 2 w + 1 its blocker. *)
Definition WatcherAt (t: nat -> Z) (w: nat) (e: Watcher): Prop :=
  t (2 * w)%nat = Z.of_nat (fst e) /\ t (2 * w + 1)%nat = key (snd e).

(* The pool t holds the watch lists wl, except the watchers q of the list of key k with
   skip k q. *)
Definition PoolOf (S: Shape) (N: nat) (t: nat -> Z) (wl: WatchLists)
  (skip: nat -> nat -> Prop): Prop :=
  forall (k q: nat), (k < 2 * N)%nat -> (q < length (tget wl k))%nat -> ~ skip k q ->
    WatcherAt t (offs S k + q) (nth q (tget wl k) (0%nat, Pos 0%nat)).

(* The pool t with watcher w set to e: its clause at entry 2 w, its blocker at 2 w + 1. *)
Definition set_watcher (t: nat -> Z) (w: nat) (e: Watcher): nat -> Z :=
  fun (q: nat) => if Nat.eqb (2 * w + 1) q then key (snd e)
                  else if Nat.eqb (2 * w) q then Z.of_nat (fst e) else t q.

Lemma set_watcher_same: forall (t: nat -> Z) (w: nat) (e: Watcher),
  WatcherAt (set_watcher t w e) w e.
Proof.
  intros t w e. unfold WatcherAt, set_watcher. rewrite !Nat.eqb_refl. split.
  - replace (Nat.eqb (2 * w + 1) (2 * w)) with false by
      (symmetry; apply Nat.eqb_neq; lia).
    reflexivity.
  - reflexivity.
Qed.

Lemma set_watcher_other: forall (t: nat -> Z) (w a: nat) (e e': Watcher), a <> w ->
  WatcherAt t a e' -> WatcherAt (set_watcher t w e) a e'.
Proof.
  intros t w a e e' Hne [H1 H2]. unfold WatcherAt, set_watcher. rewrite <- H1, <- H2.
  split.
  - replace (Nat.eqb (2 * w + 1) (2 * a)) with false by
      (symmetry; apply Nat.eqb_neq; lia).
    replace (Nat.eqb (2 * w) (2 * a)) with false by (symmetry; apply Nat.eqb_neq; lia).
    reflexivity.
  - replace (Nat.eqb (2 * w + 1) (2 * a + 1)) with false
      by (symmetry; apply Nat.eqb_neq; lia).
    replace (Nat.eqb (2 * w) (2 * a + 1)) with false by
      (symmetry; apply Nat.eqb_neq; lia).
    reflexivity.
Qed.

(* Storing watcher e as watcher w of the pool: its clause, then its blocker. *)
Lemma arr_store_watcher: forall (m m1 m2: mem) (b: block) (n w: nat) (t: nat -> Z)
  (e: Watcher),
  Arr m b (2 * n) t -> (w < n)%nat ->
  Mem.store Mint32 m b (4 * Z.of_nat (2 * w)) (vint (Z.of_nat (fst e))) = Some m1 ->
  Mem.store Mint32 m1 b (4 * Z.of_nat (2 * w + 1)) (vint (key (snd e))) = Some m2 ->
  Arr m2 b (2 * n) (set_watcher t w e).
Proof.
  intros m m1 m2 b n w t e A Hw Hst1 Hst2.
  pose proof (arr_store m m1 b (2 * n) (2 * w) t _ A ltac:(lia) Hst1) as A1.
  apply (arr_store m1 m2 b (2 * n) (2 * w + 1) _ _ A1 ltac:(lia) Hst2).
Qed.

(* The keys t of block clits hold the clauses of cm, with atoms below N: clause i < ncl
   has the literals at positions starts i .. starts (i + 1). *)
Definition ClausesIn (S: Shape) (N ncl: nat) (t: nat -> Z) (cm: ClauseMap): Prop :=
  (forall (q: nat), (q < nclits S)%nat -> exists (l: Lit), t q = key l /\
    (extract l < N)%nat) /\
  forall (i: nat), (i < ncl)%nat ->
    tget cm i = Some
                        (map (fun (q: nat) => lit_of (t q)) (seq (starts S i) (starts S
                          (Datatypes.S i) - starts S i))).

(* The value C keeps for the literal with key k (entry k of s->vals): the value of its
   atom k / 2, negated for a negative literal (odd k). *)
Definition key_value (v: Values) (k: nat): Z :=
  if Nat.even k then enc_value (tget v (Nat.div2 k))
  else - enc_value (tget v (Nat.div2 k)).

(* Setting the value of atom a changes the entries of its two literals. *)
Lemma key_value_set: forall (v: Values) (a: nat) (o: option bool) (j: nat),
  key_value (tset v a o) j =
    if Nat.eq_dec a (Nat.div2 j) then
      (if Nat.even j then enc_value o else - enc_value o)
    else key_value v j.
Proof.
  intros v a o j. unfold key_value. rewrite tget_tset.
  destruct (Nat.eq_dec a (Nat.div2 j)); reflexivity.
Qed.

(* A mark as C keeps it (entry k of s->mrk): 1 or 0. *)
Definition enc_mark (b: bool): Z := if b then 1 else 0.

(* A reason as C keeps it (entry a of s->rsn): 0 for none, i + 1 for input clause i, and
   -(j + 1) for reason clause j. *)
Definition enc_reason (r: Reason): Z :=
match r with
| no_reason => 0
| input i   => Z.of_nat i + 1
| learnt j  => - (Z.of_nat j + 1)
end.

(* A reason with a clause that C can find: an input clause below ncl, or one of the N
   reason clauses there is room for. *)
Definition ReasonBelow (ncl N: nat) (r: Reason): Prop :=
match r with
| no_reason => True
| input i   => (i < ncl)%nat
| learnt j  => (j < N)%nat
end.

(* The keys t of block rlits hold the first n reason clauses of rc, one after the other:
   clause j from position reasons_size rc j on. *)
Definition ReasonsIn (t: nat -> Z) (rc: Table (list Lit)) (n: nat): Prop :=
  forall (j k: nat), (j < n)%nat -> (k < length (tget rc j))%nat ->
    t (reasons_size rc j + k)%nat = key (nth k (tget rc j) (Pos 0%nat)).

(* The memory m holds, for N atoms and the length of the clauses lss, the context x, the
   positions lims of its decisions, and the lower literals lt of an analysis in progress
   (none between steps: RepB); all but the watch lists, which Rep adds. The r_ fields at
   an offset of block s are the fields of struct solver (../solver/solver.h), at the
   offsets CompCert gives them on x86-64: an int takes 4 bytes, a pointer 8 bytes, at an
   offset that is a multiple of 8 (so after ncl at 4, cstart is at 8). The a_ fields are
   the arrays these pointers point to, and the rest are facts about the context. *)
Record RepL (m: mem) (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (lt: list Lit): Prop := {
  r_nodup: NoDup [b_s S; b_cstart S; b_clits S; b_vals S; b_wpool S; b_woff S; b_wlen S;
    b_wcap S; b_tr S; b_shorts S; b_alls S; b_saved S; b_lims S; b_phs S; b_mrk S;
    b_rsn S; b_lvl S; b_lt S; b_rlits S; b_rbeg S; b_rlen S; b_rpos S];
  r_nv: Fld m (b_s S) 0 Mint32 (vint (Z.of_nat N));
  r_ncl: Fld m (b_s S) 4 Mint32 (vint (Z.of_nat (length lss)));
  r_cstart: Fld m (b_s S) 8 Mptr (Vptr (b_cstart S) Ptrofs.zero);
  r_clits: Fld m (b_s S) 16 Mptr (Vptr (b_clits S) Ptrofs.zero);
  r_vals: Fld m (b_s S) 24 Mptr (Vptr (b_vals S) Ptrofs.zero);
  r_wpool: Fld m (b_s S) 32 Mptr (Vptr (b_wpool S) Ptrofs.zero);
  r_npool: Fld m (b_s S) 40 Mint32 (vint (Z.of_nat (npool S)));
  r_woff: Fld m (b_s S) 48 Mptr (Vptr (b_woff S) Ptrofs.zero);
  r_wlen: Fld m (b_s S) 56 Mptr (Vptr (b_wlen S) Ptrofs.zero);
  r_wcap: Fld m (b_s S) 64 Mptr (Vptr (b_wcap S) Ptrofs.zero);
  r_tr: Fld m (b_s S) 72 Mptr (Vptr (b_tr S) Ptrofs.zero);
  r_tlen: Fld m (b_s S) 80 Mint32 (vint (Z.of_nat (tlen x)));
  r_qhead: Fld m (b_s S) 84 Mint32 (vint (Z.of_nat (qhead x)));
  r_shorts: Fld m (b_s S) 88 Mptr (Vptr (b_shorts S) Ptrofs.zero);
  r_nshorts: Fld m (b_s S) 96 Mint32 (vint (Z.of_nat (length (shorts x))));
  r_alls: Fld m (b_s S) 104 Mptr (Vptr (b_alls S) Ptrofs.zero);
  r_nlits: Fld m (b_s S) 112 Mint32 (vint (Z.of_nat (nlits x)));
  r_cur: Fld m (b_s S) 116 Mint32 (vint (Z.of_nat (cur x)));
  r_saved: Fld m (b_s S) 120 Mptr (Vptr (b_saved S) Ptrofs.zero);
  r_lims: Fld m (b_s S) 128 Mptr (Vptr (b_lims S) Ptrofs.zero);
  r_dl: Fld m (b_s S) 136 Mint32 (vint (Z.of_nat (length lims)));
  r_phs: Fld m (b_s S) 144 Mptr (Vptr (b_phs S) Ptrofs.zero);
  a_starts: Arr m (b_cstart S) (Datatypes.S (length lss))
    (fun (i: nat) => Z.of_nat (starts S i));
  a_lits: exists (t: nat -> Z), Arr m (b_clits S) (nclits S) t /\
    ClausesIn S N (length lss) t (cmap x);
  a_vals: Arr m (b_vals S) (2 * N) (key_value (vals x));
  a_woff: Arr m (b_woff S) (2 * N) (fun (k: nat) => Z.of_nat (offs S k));
  a_wlen: Arr m (b_wlen S) (2 * N) (fun (k: nat) => Z.of_nat (length (tget (wls x) k)));
  a_wcap: Arr m (b_wcap S) (2 * N) (fun (k: nat) => Z.of_nat (caps S k));
  a_tr: Arr m (b_tr S) N (fun (j: nat) => key (tget (tr x) j));
  a_shorts: exists (t: nat -> Z), Arr m (b_shorts S) (length lss) t /\
    forall (q: nat), (q < length (shorts x))%nat ->
      t q = Z.of_nat (nth q (rev (shorts x)) 0%nat);
  a_alls: exists (t: nat -> Z), Arr m (b_alls S) (2 * N) t /\
    forall (k: nat), (k < nlits x)%nat -> t k = key (tget (alls x) k);
  a_saved: exists (t: nat -> Z), Arr m (b_saved S) N t /\
    forall (k: nat), (k < length (saved x))%nat ->
      t k = Z.of_nat (nth k (rev (saved x)) 0%nat);
  a_lims: exists (t: nat -> Z), Arr m (b_lims S) N t /\
    forall (k: nat), (k < length lims)%nat -> t k = Z.of_nat (nth k (rev lims) 0%nat);
  a_phs: Arr m (b_phs S) N (fun (a: nat) => enc_value (tget (phs x) a));
  r_cmap: forall (i: nat), (length lss <= i)%nat -> tget (cmap x) i = None;
  r_starts: forall (i: nat), (i < length lss)%nat ->
    (starts S i <= starts S (Datatypes.S i) <= nclits S)%nat;
  r_nvars: nvars x = N;
  r_n: Z.of_nat N < 268435456;
  r_nclits_small: Z.of_nat (nclits S) < 1073741824;
  r_lss_small: Z.of_nat (length lss) < 1073741824;
  r_pool_small: Z.of_nat (npool S) < 1073741824;
  r_room: forall (k: nat), (k < 2 * N)%nat -> (offs S k + caps S k <= npool S)%nat;
  r_apart: forall (k k': nat), (k < k' < 2 * N)%nat ->
    (offs S k + caps S k <= offs S k')%nat;
  r_wlen_le: forall (k: nat), (k < 2 * N)%nat ->
    (length (tget (wls x) k) <= caps S k)%nat;
  r_wls_cls: forall (k i: nat) (b: Lit), (k < 2 * N)%nat -> In (i, b) (tget (wls x) k) ->
    (i < length lss)%nat;
  r_wls_blk: forall (k i: nat) (b: Lit), (k < 2 * N)%nat -> In (i, b) (tget (wls x) k) ->
    (extract b < N)%nat;
  r_tlen_le: (tlen x <= N)%nat;
  r_qhead_le: (qhead x <= tlen x)%nat;
  r_tr_atoms: forall (j: nat), (j < tlen x)%nat -> (extract (tget (tr x) j) < N)%nat;
  r_shorts_le: (length (shorts x) <= length lss)%nat;
  r_shorts_cls: forall (i: nat), In i (shorts x) -> (i < length lss)%nat;
  r_nlits_le: (nlits x <= 2 * N)%nat;
  r_alls_atoms: forall (k: nat), (k < nlits x)%nat ->
    (extract (tget (alls x) k) < N)%nat;
  r_cur_le: (cur x <= nlits x)%nat;
  r_saved_le: forall (c: nat), In c (saved x) -> (c <= nlits x)%nat;
  r_saved_len: length (saved x) = length lims;
  r_dl_le: (length lims <= N)%nat;
  r_mrk: Fld m (b_s S) 152 Mptr (Vptr (b_mrk S) Ptrofs.zero);
  r_rsn: Fld m (b_s S) 160 Mptr (Vptr (b_rsn S) Ptrofs.zero);
  r_lvl: Fld m (b_s S) 168 Mptr (Vptr (b_lvl S) Ptrofs.zero);
  r_lt: Fld m (b_s S) 176 Mptr (Vptr (b_lt S) Ptrofs.zero);
  r_ltlen: Fld m (b_s S) 184 Mint32 (vint (Z.of_nat (length lt)));
  r_rlits: Fld m (b_s S) 192 Mptr (Vptr (b_rlits S) Ptrofs.zero);
  r_rcap: Fld m (b_s S) 200 Mint32 (vint (Z.of_nat (rcap x)));
  r_rtop: Fld m (b_s S) 204 Mint32 (vint (Z.of_nat (reasons_size (rcl x) (nr x))));
  r_rbeg: Fld m (b_s S) 208 Mptr (Vptr (b_rbeg S) Ptrofs.zero);
  r_rlen: Fld m (b_s S) 216 Mptr (Vptr (b_rlen S) Ptrofs.zero);
  r_rpos: Fld m (b_s S) 224 Mptr (Vptr (b_rpos S) Ptrofs.zero);
  r_nr: Fld m (b_s S) 232 Mint32 (vint (Z.of_nat (nr x)));
  a_mrk: Arr m (b_mrk S) (2 * N) (fun (k: nat) => enc_mark (tget (mrk x) k));
  a_rsn: Arr m (b_rsn S) N (fun (a: nat) => enc_reason (tget (rsn x) a));
  a_lvl: Arr m (b_lvl S) N (fun (a: nat) => Z.of_nat (tget (lvl x) a));
  a_lt: exists (t: nat -> Z), Arr m (b_lt S) N t /\
    forall (k: nat), (k < length lt)%nat -> t k = key (nth k lt (Pos 0%nat));
  a_rlits: exists (t: nat -> Z), Arr m (b_rlits S) (rcap x) t /\
    ReasonsIn t (rcl x) (nr x);
  a_rbeg: exists (t: nat -> Z), Arr m (b_rbeg S) N t /\
    forall (j: nat), (j < nr x)%nat -> t j = Z.of_nat (reasons_size (rcl x) j);
  a_rlen: exists (t: nat -> Z), Arr m (b_rlen S) N t /\
    forall (j: nat), (j < nr x)%nat -> t j = Z.of_nat (length (tget (rcl x) j));
  a_rpos: exists (t: nat -> Z), Arr m (b_rpos S) N t /\
    forall (j: nat), (j < nr x)%nat -> t j = Z.of_nat (tget (rps x) j);
  r_dl_eq: dl x = length lims;
  r_rsn_below: forall (a: nat), (a < N)%nat -> ReasonBelow (length lss) N
    (tget (rsn x) a);
  r_lvl_le: forall (a: nat), (a < N)%nat -> (tget (lvl x) a <= N)%nat;
  r_lt_le: (length lt <= N)%nat;
  r_lt_atoms: forall (y: Lit), In y lt -> (extract y < N)%nat;
  r_nr_le: (nr x <= N)%nat;
  r_rsize_le: (reasons_size (rcl x) (nr x) <= rcap x)%nat;
  r_rcap_small: Z.of_nat (rcap x) < 1073741824;
  r_rcl_atoms: forall (j: nat) (y: Lit), (j < nr x)%nat -> In y (tget (rcl x) j) ->
    (extract y < N)%nat;
  r_rps_le: forall (j: nat), (j < nr x)%nat -> (tget (rps x) j <= N)%nat
}.

(* Between steps, there is no analysis in progress. *)
Definition RepB (m: mem) (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat): Prop :=
  RepL m S N lss x lims [].

(* The blocks of the solver, all distinct. *)
Definition iblocks (S: Shape): list block :=
  [b_s S; b_cstart S; b_clits S; b_vals S; b_wpool S; b_woff S; b_wlen S; b_wcap S;
   b_tr S; b_shorts S; b_alls S; b_saved S; b_lims S; b_phs S; b_mrk S; b_rsn S;
   b_lvl S; b_lt S; b_rlits S; b_rbeg S; b_rlen S; b_rpos S].

(* With the watch lists in the pool. *)
Definition Rep (m: mem) (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat): Prop :=
  RepB m S N lss x lims /\
  exists (t: nat -> Z), Arr m (b_wpool S) (2 * npool S) t /\
    PoolOf S N t (wls x) (fun (_ _: nat) => False).

(* Updates of a context, one field at a time, as the stores of the C code make them. *)
Definition set_vals (x: Ctx) (v: Values): Ctx :=
  mkCtx v (cmap x) (wls x) (tr x) (tlen x) (qhead x) (shorts x) (alls x) (nlits x)
    (cur x)
    (saved x) (rsn x) (lvl x) (dl x) (mrk x) (phs x) (nvars x) (rcl x) (rps x) (nr x)
    (rcap x).

Definition set_tr (x: Ctx) (t: Table Lit): Ctx :=
  mkCtx (vals x) (cmap x) (wls x) t (tlen x) (qhead x) (shorts x) (alls x) (nlits x)
    (cur x) (saved x) (rsn x) (lvl x) (dl x) (mrk x) (phs x) (nvars x) (rcl x) (rps x)
    (nr x) (rcap x).

Definition set_tlen (x: Ctx) (n: nat): Ctx :=
  mkCtx (vals x) (cmap x) (wls x) (tr x) n (qhead x) (shorts x) (alls x) (nlits x)
    (cur x)
    (saved x) (rsn x) (lvl x) (dl x) (mrk x) (phs x) (nvars x) (rcl x) (rps x) (nr x)
    (rcap x).

Definition set_phs (x: Ctx) (v: Values): Ctx :=
  mkCtx (vals x) (cmap x) (wls x) (tr x) (tlen x) (qhead x) (shorts x) (alls x) (nlits x)
    (cur x) (saved x) (rsn x) (lvl x) (dl x) (mrk x) v (nvars x) (rcl x) (rps x) (nr x)
    (rcap x).

Definition set_qhead (x: Ctx) (n: nat): Ctx :=
  mkCtx (vals x) (cmap x) (wls x) (tr x) (tlen x) n (shorts x) (alls x) (nlits x) (cur x)
    (saved x) (rsn x) (lvl x) (dl x) (mrk x) (phs x) (nvars x) (rcl x) (rps x) (nr x)
    (rcap x).

(* The cursor c, the saved cursors st and the decision level d. *)
Definition set_level (x: Ctx) (c: nat) (st: list nat) (d: nat): Ctx :=
  mkCtx (vals x) (cmap x) (wls x) (tr x) (tlen x) (qhead x) (shorts x) (alls x) (nlits x)
    c st (rsn x) (lvl x) d (mrk x) (phs x) (nvars x) (rcl x) (rps x) (nr x) (rcap x).

Definition set_shorts (x: Ctx) (ss: list nat): Ctx :=
  mkCtx (vals x) (cmap x) (wls x) (tr x) (tlen x) (qhead x) ss (alls x) (nlits x) (cur x)
    (saved x) (rsn x) (lvl x) (dl x) (mrk x) (phs x) (nvars x) (rcl x) (rps x) (nr x)
    (rcap x).

Definition set_rsn (x: Ctx) (r: Table Reason): Ctx :=
  mkCtx (vals x) (cmap x) (wls x) (tr x) (tlen x) (qhead x) (shorts x) (alls x) (nlits x)
    (cur x) (saved x) r (lvl x) (dl x) (mrk x) (phs x) (nvars x) (rcl x) (rps x) (nr x)
    (rcap x).

Definition set_lvl (x: Ctx) (lv: Table nat): Ctx :=
  mkCtx (vals x) (cmap x) (wls x) (tr x) (tlen x) (qhead x) (shorts x) (alls x) (nlits x)
    (cur x) (saved x) (rsn x) lv (dl x) (mrk x) (phs x) (nvars x) (rcl x) (rps x) (nr x)
    (rcap x).

Definition set_mrk (x: Ctx) (mk: Table bool): Ctx :=
  mkCtx (vals x) (cmap x) (wls x) (tr x) (tlen x) (qhead x) (shorts x) (alls x) (nlits x)
    (cur x) (saved x) (rsn x) (lvl x) (dl x) mk (phs x) (nvars x) (rcl x) (rps x) (nr x)
    (rcap x).

(* The first n reason clauses. *)
Definition set_nr (x: Ctx) (n: nat): Ctx :=
  mkCtx (vals x) (cmap x) (wls x) (tr x) (tlen x) (qhead x) (shorts x) (alls x) (nlits x)
    (cur x) (saved x) (rsn x) (lvl x) (dl x) (mrk x) (phs x) (nvars x) (rcl x) (rps x) n
    (rcap x).

(* Storing the value o of atom a, for both its literals: s->vals[2a] = enc_value o and
   s->vals[2a + 1] = -enc_value o. *)
Lemma rep_store_vals {lt: list Lit}: forall (m m1 m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (a: nat) (o: option bool),
  RepL m S N lss x lims lt -> (a < N)%nat ->
  Mem.store Mint32 m (b_vals S) (4 * Z.of_nat (2 * a)) (vint (enc_value o)) = Some m1 ->
  Mem.store Mint32 m1 (b_vals S) (4 * Z.of_nat (2 * a + 1)) (vint (- enc_value o))
    = Some m' ->
  RepL m' S N lss (set_vals x (tset (vals x) a o)) lims lt.
Proof.
  intros m m1 m' S N lss x lims a o HRep Ha Hst1 Hst2.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  assert (Ha1: (2 * a < 2 * N)%nat) by lia.
  assert (Ha2: (2 * a + 1 < 2 * N)%nat) by lia.
  pose proof (arr_store m m1 (b_vals S) (2 * N) (2 * a) _ _ (a_vals _ _ _ _ _ _ _ HRep)
    Ha1
                Hst1) as Avals1.
  pose proof (arr_store m1 m' (b_vals S) (2 * N) (2 * a + 1) _ _ Avals1 Ha2 Hst2)
    as Avals.
  destruct HRep. unpack. carry Hst1 Hnd. carry Hst2 Hnd.
  (* Every field but the values is as before. *)
  constructor; try assumption.
  - repack.
  - (* the values: both literals of atom a now have the values of o *)
    cbn [set_vals vals]. eapply arr_ext.
    + apply Avals.
    + (* Entry j belongs to atom j / 2, and is that of its positive literal for even j:
         compare j with 2a and 2a + 1, through j = 2 (j / 2) + (j odd). *)
      intros j Hj. rewrite key_value_set. pose proof (Nat.div2_odd j) as Hdiv.
      rewrite <- Nat.negb_odd.
      destruct (Nat.odd j), (Nat.eq_dec a (Nat.div2 j)), (Nat.eqb_spec (2 * a + 1) j),
        (Nat.eqb_spec (2 * a) j); cbn [negb Nat.b2n] in *; (reflexivity || lia).
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
Qed.

(* Storing literal l at position j of the trail, from its end on: s->tr[j] = l. *)
Lemma rep_store_tr {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (j: nat) (l: Lit),
  RepL m S N lss x lims lt -> (tlen x <= j < N)%nat ->
  Mem.store Mint32 m (b_tr S) (4 * Z.of_nat j) (vint (key l)) = Some m' ->
  RepL m' S N lss (set_tr x (tset (tr x) j l)) lims lt.
Proof.
  intros m m' S N lss x lims j l HRep Hj Hst.
  assert (HjN: (j < N)%nat) by lia.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_tr_atoms _ _ _ _ _ _ _ HRep) as Hatoms.
  pose proof (arr_store m m' (b_tr S) N j _ _ (a_tr _ _ _ _ _ _ _ HRep) HjN Hst) as Atr.
  destruct HRep. unpack. carry Hst Hnd.
  (* Every field but the trail is as before. *)
  constructor; try assumption.
  - repack.
  - (* the trail: position j now holds l *)
    cbn [set_tr tr]. arr_tset.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* the trail up to its end is unchanged, as j is not below it *)
    intros j' Hj'. cbn [set_tr tr tlen] in *. rewrite tget_tset.
    destruct (Nat.eq_dec j j') as [-> | Hne].
    + lia.
    + apply Hatoms. assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
Qed.

(* Setting the length of the trail to n: s->tlen = n. *)
Lemma rep_store_tlen {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (n: nat),
  RepL m S N lss x lims lt -> (n <= N)%nat -> (qhead x <= n)%nat ->
  (forall (j: nat), (j < n)%nat -> (extract (tget (tr x) j) < N)%nat) ->
  Mem.store Mint32 m (b_s S) 80 (vint (Z.of_nat n)) = Some m' ->
  RepL m' S N lss (set_tlen x n) lims lt.
Proof.
  intros m m' S N lss x lims n HRep Hn Hq Hatoms Hst.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (fld_store m m' (b_s S) 80 Mint32 _ _ (r_tlen _ _ _ _ _ _ _ HRep) Hst)
    as Ftlen.
  cbn [Val.load_result] in Ftlen. destruct HRep. unpack. carry Hst Hnd.
  (* Every field is as before, but the length, its bounds and the atoms of the trail,
     which the hypotheses give. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
Qed.

(* Moving the head of the queue to n, within the trail: s->qhead = n. *)
Lemma rep_store_qhead {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (n: nat),
  RepL m S N lss x lims lt -> (n <= tlen x)%nat ->
  Mem.store Mint32 m (b_s S) 84 (vint (Z.of_nat n)) = Some m' ->
  RepL m' S N lss (set_qhead x n) lims lt.
Proof.
  intros m m' S N lss x lims n HRep Hn Hst.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (fld_store m m' (b_s S) 84 Mint32 _ _ (r_qhead _ _ _ _ _ _ _ HRep) Hst)
    as Fqh.
  cbn [Val.load_result] in Fqh. destruct HRep. unpack. carry Hst Hnd.
  (* Every field is as before, but the head of the queue, which the hypothesis bounds. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
Qed.

(* Cutting the trail to its first j literals, with an empty queue:
   s->tlen = j; s->qhead = j. (Each store alone may break qhead <= tlen.) *)
Lemma rep_store_cut {lt: list Lit}: forall (m m1 m2: mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (j: nat),
  RepL m S N lss x lims lt -> (j <= tlen x)%nat ->
  Mem.store Mint32 m (b_s S) 80 (vint (Z.of_nat j)) = Some m1 ->
  Mem.store Mint32 m1 (b_s S) 84 (vint (Z.of_nat j)) = Some m2 ->
  RepL m2 S N lss (set_qhead (set_tlen x j) j) lims lt.
Proof.
  intros m m1 m2 S N lss x lims j HRep Hj Hst1 Hst2.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_tlen_le _ _ _ _ _ _ _ HRep) as Htle.
  pose proof (r_tr_atoms _ _ _ _ _ _ _ HRep) as Hatoms.
  pose proof (r_qhead _ _ _ _ _ _ _ HRep) as Fqh.
  pose proof (fld_store m m1 (b_s S) 80 Mint32 _ _ (r_tlen _ _ _ _ _ _ _ HRep) Hst1)
    as Ftlen1.
  destruct HRep. unpack. carry Hst1 Hnd.
  pose proof (fld_store m1 m2 (b_s S) 84 Mint32 _ _ Fqh Hst2) as Fqh2.
  carry Hst2 Hnd. cbn [Val.load_result] in Ftlen1, Fqh2.
  (* Every field is as before, but the length and the head of the queue, now j. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* the length is within the old one *)
    cbn [set_qhead set_tlen tlen]. lia.
  - (* the queue is empty *)
    cbn [set_qhead set_tlen tlen qhead]. lia.
  - (* the trail up to j is a part of the old one *)
    intros j' Hj'. cbn [set_qhead set_tlen tlen tr] in *. apply Hatoms. lia.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
Qed.

(* The first entries of the reversal of a list are those of the reversal of its end. *)
Lemma nth_rev_skipn: forall {A: Type} (l: list A) (n j: nat) (d: A),
  (j < length (skipn n l))%nat -> nth j (rev l) d = nth j (rev (skipn n l)) d.
Proof.
  intros A l n j d Hj. rewrite <- (firstn_skipn n l) at 1. rewrite rev_app_distr.
  apply app_nth1. rewrite length_rev. assumption.
Qed.

(* Jumping back over the k + 1 newest decisions: the cursor c0 saved for the oldest of
   them comes back, and the length st of the saved cursors left is the decision level.
   s->cur = s->saved[d]; s->dl = d, for d = length st. *)
Lemma rep_store_level {lt: list Lit}: forall (m m1 m2: mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (k c0: nat) (st: list nat),
  RepL m S N lss x lims lt -> skipn k (saved x) = c0 :: st ->
  Mem.store Mint32 m (b_s S) 116 (vint (Z.of_nat c0)) = Some m1 ->
  Mem.store Mint32 m1 (b_s S) 136 (vint (Z.of_nat (length st))) = Some m2 ->
  RepL m2 S N lss (set_level x c0 st (length st)) (skipn (Datatypes.S k) lims) lt.
Proof.
  intros m m1 m2 S N lss x lims k c0 st HRep Hsv Hst1 Hst2.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_saved_le _ _ _ _ _ _ _ HRep) as Hsle.
  pose proof (r_saved_len _ _ _ _ _ _ _ HRep) as Hslen.
  pose proof (r_dl_le _ _ _ _ _ _ _ HRep) as Hdle.
  pose proof (a_saved _ _ _ _ _ _ _ HRep) as (tsv & Asaved & Htsv).
  pose proof (a_lims _ _ _ _ _ _ _ HRep) as (tl & Alims & Htl).
  pose proof (r_dl _ _ _ _ _ _ _ HRep) as Fdl.
  pose proof (fld_store m m1 (b_s S) 116 Mint32 _ _ (r_cur _ _ _ _ _ _ _ HRep) Hst1)
    as Fcur1.
  (* The saved cursors are those before position k, c0 and st; as many as decisions. *)
  assert (Hsplit: saved x = firstn k (saved x) ++ c0 :: st).
  { rewrite <- Hsv. symmetry. apply firstn_skipn. }
  assert (Hin: forall (c: nat), In c (c0 :: st) -> In c (saved x)).
  { intros c Hc. rewrite Hsplit. apply in_or_app. now right. }
  assert (Hlen: length st = length (skipn (Datatypes.S k) lims)).
  { rewrite length_skipn, <- Hslen.
    assert (Hk: length (skipn k (saved x)) = Datatypes.S (length st))
      by now rewrite Hsv.
    rewrite length_skipn in Hk. lia. }
  assert (Hst: st = skipn (Datatypes.S k) (saved x)).
  { rewrite <- (skipn_skipn 1 k), Hsv. reflexivity. }
  destruct HRep. unpack. carry Hst1 Hnd.
  pose proof (fld_store m1 m2 (b_s S) 136 Mint32 _ _ Fdl Hst2) as Fdl2.
  carry Hst2 Hnd. cbn [Val.load_result] in Fcur1, Fdl2.
  (* Every field is as before, but the cursor, the saved cursors and the decision
     positions, which lose their newest k + 1 entries; Hlen gives their number. *)
  constructor; try assumption.
  - (* the number of decisions *)
    rewrite <- Hlen. assumption.
  - repack.
  - repack.
  - repack.
  - (* the saved cursors: the first entries of the same array *)
    exists tsv. split.
    + assumption.
    + intros j Hj. cbn [set_level saved] in Hj |- *. rewrite Htsv.
      * rewrite Hst. f_equal. apply nth_rev_skipn. rewrite <- Hst. assumption.
      * rewrite Hslen. rewrite Hlen, length_skipn in Hj. lia.
  - (* the decision positions: the first entries of the same array *)
    exists tl. split.
    + assumption.
    + intros j Hj. rewrite Htl.
      * f_equal. apply nth_rev_skipn. assumption.
      * rewrite length_skipn in Hj. lia.
  - (* the cursor was saved, so it is within the literals to decide on *)
    cbn [set_level cur nlits]. apply Hsle. apply Hin. now left.
  - (* the cursors still saved *)
    intros c Hc. cbn [set_level saved nlits] in *. apply Hsle. apply Hin. now right.
  - (* the decisions within the atoms *)
    rewrite length_skipn. lia.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
Qed.

(* Moving the cursor to c, within the literals to decide on: s->cur = c. *)
Lemma rep_store_cur {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (c: nat),
  RepL m S N lss x lims lt -> (c <= nlits x)%nat ->
  Mem.store Mint32 m (b_s S) 116 (vint (Z.of_nat c)) = Some m' ->
  RepL m' S N lss (with_cursor x c) lims lt.
Proof.
  intros m m' S N lss x lims c HRep Hc Hst.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (fld_store m m' (b_s S) 116 Mint32 _ _ (r_cur _ _ _ _ _ _ _ HRep) Hst)
    as Fcur.
  cbn [Val.load_result] in Fcur. destruct HRep. unpack. carry Hst Hnd.
  (* Every field is as before, but the cursor, which the hypothesis bounds. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
Qed.

(* Opening a decision level at cursor c: the cursor moves to c and is saved, and the
   position of the decision, the end of the trail, is recorded.
   s->cur = c; s->saved[s->dl] = c; s->lims[s->dl] = s->tlen; s->dl = s->dl + 1. *)
Lemma rep_store_open {lt: list Lit}: forall (m m1 m2 m3 m4: mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (c: nat),
  RepL m S N lss x lims lt -> (c <= nlits x)%nat -> (length lims < N)%nat ->
  Mem.store Mint32 m (b_s S) 116 (vint (Z.of_nat c)) = Some m1 ->
  Mem.store Mint32 m1 (b_saved S) (4 * Z.of_nat (length lims)) (vint (Z.of_nat c)) =
    Some m2 ->
  Mem.store Mint32 m2 (b_lims S) (4 * Z.of_nat (length lims))
    (vint (Z.of_nat (tlen x))) = Some m3 ->
  Mem.store Mint32 m3 (b_s S) 136 (vint (Z.of_nat (Datatypes.S (length lims)))) =
    Some m4 ->
  RepL m4 S N lss (open_level x c) (tlen x :: lims) lt.
Proof.
  intros m m1 m2 m3 m4 S N lss x lims c HRep Hc Hroom Hst1 Hst2 Hst3 Hst4.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_saved_le _ _ _ _ _ _ _ HRep) as Hsle.
  pose proof (r_saved_len _ _ _ _ _ _ _ HRep) as Hslen.
  pose proof (a_saved _ _ _ _ _ _ _ HRep) as (tsv & Asaved & Htsv).
  pose proof (a_lims _ _ _ _ _ _ _ HRep) as (tl & Alims & Htl).
  pose proof (r_dl _ _ _ _ _ _ _ HRep) as Fdl.
  pose proof (fld_store m m1 (b_s S) 116 Mint32 _ _ (r_cur _ _ _ _ _ _ _ HRep) Hst1)
    as Fcur1.
  destruct HRep. unpack. carry Hst1 Hnd.
  pose proof (arr_store m1 m2 (b_saved S) N (length lims) tsv _ Asaved Hroom Hst2)
    as Asaved2.
  carry Hst2 Hnd.
  pose proof (arr_store m2 m3 (b_lims S) N (length lims) tl _ Alims Hroom Hst3)
    as Alims3.
  carry Hst3 Hnd.
  pose proof (fld_store m3 m4 (b_s S) 136 Mint32 _ _ Fdl Hst4) as Fdl4.
  carry Hst4 Hnd. cbn [Val.load_result] in Fcur1, Fdl4.
  (* Every field is as before, but the cursor, the saved cursors and the decision
     positions, which get c and tlen x as their last entries; the hypothesis bounds the
     new number of decisions. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - (* the saved cursors: c is the new last entry *)
    eexists. split.
    + apply Asaved2.
    + intros j Hj. cbn [open_level saved length rev] in Hj |- *.
      destruct (Nat.eq_dec (length lims) j) as [<- | Hne].
      * rewrite Nat.eqb_refl, <- Hslen, <- length_rev, nth_middle. reflexivity.
      * replace (Nat.eqb (length lims) j) with false
          by (symmetry; now apply Nat.eqb_neq).
        rewrite app_nth1 by (rewrite length_rev; lia). apply Htsv. lia.
  - (* the decision positions: tlen x is the new last entry *)
    eexists. split.
    + apply Alims3.
    + intros j Hj. cbn [length rev] in Hj |- *.
      destruct (Nat.eq_dec (length lims) j) as [<- | Hne].
      * rewrite Nat.eqb_refl, <- length_rev, nth_middle. reflexivity.
      * replace (Nat.eqb (length lims) j) with false
          by (symmetry; now apply Nat.eqb_neq).
        rewrite app_nth1 by (rewrite length_rev; lia). apply Htl. lia.
  - (* the saved cursors are within the literals to decide on *)
    intros c' [<- | Hin].
    + assumption.
    + now apply Hsle.
  - (* one saved cursor per decision *)
    cbn [open_level saved length]. lia.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* one decision more *)
    cbn [open_level dl length]. f_equal. assumption.
Qed.

(* A store to the pool, whose entries RepL does not describe (Rep does, by PoolOf). *)
Lemma rep_store_pool {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (ofs: Z) (v: val),
  RepL m S N lss x lims lt -> Mem.store Mint32 m (b_wpool S) ofs v = Some m' ->
  RepL m' S N lss x lims lt.
Proof.
  intros m m' S N lss x lims ofs v HRep Hst.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  destruct HRep. unpack. carry Hst Hnd.
  (* Every field is as before. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
Qed.

(* Setting the watch list of l to ws, which the pool holds, by its length:
   s->wlen[l] = length ws. *)
Lemma rep_store_watching {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (l: Lit) (ws: list Watcher),
  RepL m S N lss x lims lt -> (extract l < N)%nat ->
  (length ws <= caps S (lit_key l))%nat ->
  (forall (i: nat) (b: Lit), In (i, b) ws -> (i < length lss)%nat /\ (extract b < N)%nat)
    ->
  Mem.store Mint32 m (b_wlen S) (4 * Z.of_nat (lit_key l))
    (vint (Z.of_nat (length ws))) = Some m' ->
  RepL m' S N lss (set_watching x l ws) lims lt.
Proof.
  intros m m' S N lss x lims l ws HRep Hl Hroom Hws Hst.
  assert (Hk: (lit_key l < 2 * N)%nat) by (destruct l; simpl in *; lia).
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_wlen_le _ _ _ _ _ _ _ HRep) as Hwle.
  pose proof (r_wls_cls _ _ _ _ _ _ _ HRep) as Hwcls.
  pose proof (r_wls_blk _ _ _ _ _ _ _ HRep) as Hwblk.
  pose proof (arr_store m m' (b_wlen S) (2 * N) (lit_key l) _ _ (a_wlen _ _ _ _ _ _ _
    HRep)
                Hk Hst) as Awlen.
  destruct HRep. unpack. carry Hst Hnd.
  (* Every field is as before, but the watch lists and their bounds. *)
  constructor; try assumption.
  - repack.
  - (* the lengths: the list of l is ws *)
    eapply arr_ext.
    + apply Awlen.
    + intros j Hj. cbn [set_watching wls]. rewrite tget_tset.
      destruct (Nat.eq_dec (lit_key l) j) as [<- | Hne].
      * rewrite Nat.eqb_refl. reflexivity.
      * replace (Nat.eqb (lit_key l) j) with false by (symmetry; now apply Nat.eqb_neq).
        reflexivity.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* every watch list fits in its room *)
    intros k Hk'. cbn [set_watching wls]. rewrite tget_tset.
    destruct (Nat.eq_dec (lit_key l) k) as [<- | Hne].
    + assumption.
    + apply Hwle. assumption.
  - (* every watch list holds clauses *)
    intros k j b Hk' Hj. cbn [set_watching wls] in Hj. rewrite tget_tset in Hj.
    destruct (Nat.eq_dec (lit_key l) k) as [<- | Hne].
    + apply (Hws j b). assumption.
    + apply (Hwcls k j b); assumption.
  - (* with blockers of atoms below N *)
    intros k j b Hk' Hj. cbn [set_watching wls] in Hj. rewrite tget_tset in Hj.
    destruct (Nat.eq_dec (lit_key l) k) as [<- | Hne].
    + apply (Hws j b). assumption.
    + apply (Hwblk k j b); assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
Qed.

(* Appending the watcher of clause i with blocker b to the watch list of l, by its
   length: s->wlen[l] = n + 1, where n is the old length. *)
Lemma rep_store_wlen {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (l: Lit) (i: nat) (b: Lit),
  RepL m S N lss x lims lt -> (extract l < N)%nat ->
  (length (watching (wls x) l) < caps S (lit_key l))%nat -> (i < length lss)%nat ->
  (extract b < N)%nat ->
  Mem.store Mint32 m (b_wlen S) (4 * Z.of_nat (lit_key l))
    (vint (Z.of_nat (Datatypes.S (length (watching (wls x) l))))) = Some m' ->
  RepL m' S N lss (set_watching x l (watching (wls x) l ++ [(i, b)])) lims lt.
Proof.
  intros m m' S N lss x lims l i b HRep Hl Hroom Hi Hb Hst.
  assert (Hk: (lit_key l < 2 * N)%nat) by (destruct l; simpl in *; lia).
  assert (Hlen: length (watching (wls x) l ++ [(i, b)])
                = Datatypes.S (length (watching (wls x) l))).
  { rewrite length_app. cbn [length]. lia. }
  apply (rep_store_watching m m' S N lss x lims l).
  - assumption.
  - assumption.
  - lia.
  - (* the watchers of the list of l, and that of clause i *)
    intros j c Hj. apply in_app_or in Hj as [Hj | [Heq | []]].
    + split.
      * apply (r_wls_cls _ _ _ _ _ _ _ HRep (lit_key l) j c); assumption.
      * apply (r_wls_blk _ _ _ _ _ _ _ HRep (lit_key l) j c); assumption.
    + injection Heq as <- <-. split.
      * assumption.
      * assumption.
  - rewrite Hlen. assumption.
Qed.

(* Replacing entry d of ls by y. *)
Definition set_nth (d: nat) (y: Lit) (ls: list Lit): list Lit :=
  firstn d ls ++ y :: skipn (Datatypes.S d) ls.

(* The clauses start in order. *)
Lemma starts_le {lt: list Lit}: forall (m: mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat),
  RepL m S N lss x lims lt ->
  forall (i j: nat), (i <= j <= length lss)%nat -> (starts S i <= starts S j)%nat.
Proof.
  intros m S N lss x lims HRep i j Hij. induction j as [|j IH].
  - assert (i = 0%nat) as -> by lia. lia.
  - destruct (Nat.eq_dec i (Datatypes.S j)) as [-> | Hne].
    + lia.
    + destruct (r_starts _ _ _ _ _ _ _ HRep j) as [Hj _].
      * lia.
      * assert (starts S i <= starts S j)%nat by (apply IH; lia). lia.
Qed.

(* Updating a table at position a + d updates entry d of the range from a on. *)
Lemma map_seq_set: forall (f: nat -> Lit) (y: Lit) (n a d: nat), (d < n)%nat ->
  map (fun (q: nat) => if Nat.eqb (a + d) q then y else f q) (seq a n) =
  set_nth d y (map f (seq a n)).
Proof.
  intros f y n. induction n as [|n IH]; intros a d Hd.
  - lia.
  - cbn [seq map]. destruct d as [|d].
    + unfold set_nth. cbn [firstn skipn app]. rewrite Nat.add_0_r, Nat.eqb_refl. f_equal.
      apply map_ext_in. intros q Hq. apply in_seq in Hq.
      replace (Nat.eqb a q) with false by
        (symmetry; apply Nat.eqb_neq; lia). reflexivity.
    + replace (Nat.eqb (a + Datatypes.S d) a) with false
        by (symmetry; apply Nat.eqb_neq; lia).
      unfold set_nth. cbn [firstn skipn app]. f_equal.
      replace (a + Datatypes.S d)%nat with (Datatypes.S a + d)%nat by lia.
      apply IH. lia.
Qed.

(* Storing literal y as literal d of clause i: s->clits[starts i + d] = y. *)
Lemma rep_store_clits {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (i d: nat) (ls: list Lit) (y: Lit),
  RepL m S N lss x lims lt -> (i < length lss)%nat -> tget (cmap x) i = Some ls ->
  (d < length ls)%nat -> (extract y < N)%nat ->
  Mem.store Mint32 m (b_clits S) (4 * Z.of_nat (starts S i + d)) (vint (key y)) =
    Some m' ->
  RepL m' S N lss (set_clause x i (set_nth d y ls)) lims lt.
Proof.
  intros m m' S N lss x lims i d ls y HRep Hi Hls Hd Hy Hst.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_cmap _ _ _ _ _ _ _ HRep) as Hnone.
  destruct (r_starts _ _ _ _ _ _ _ HRep i Hi) as [Hsi Hsn].
  pose proof (starts_le _ _ _ _ _ _ HRep) as Hle.
  destruct (a_lits _ _ _ _ _ _ _ HRep) as (t & At & Hatoms & Hcl).
  (* The literals of clause i are those from starts i on *)
  assert (Hlen: length ls = (starts S (Datatypes.S i) - starts S i)%nat).
  { rewrite (Hcl i Hi) in Hls. injection Hls as <-. now rewrite length_map, length_seq. }
  pose proof
    (arr_store m m' (b_clits S) (nclits S) (starts S i + d) t _ At ltac:(lia) Hst)
    as At'.
  destruct HRep. unpack. carry Hst Hnd.
  (* Every field is as before, but the literals of clause i. *)
  constructor; try assumption.
  - exists (fun (q: nat) => if Nat.eqb (starts S i + d) q then key y else t q). split.
    + assumption.
    + split.
      * (* the atoms of the new literal and of the others *)
        intros q Hq. destruct (Nat.eqb (starts S i + d) q).
        -- now exists y.
        -- now apply Hatoms.
      * (* clause i has y in place d, and the others their literals *)
        intros j Hj. cbn [set_clause cmap]. rewrite tget_tset.
        destruct (Nat.eq_dec i j) as [<- | Hne].
        -- rewrite (Hcl i Hi) in Hls. injection Hls as <-. f_equal. symmetry.
           transitivity
             (map (fun (q: nat) => if Nat.eqb (starts S i + d) q then y else lit_of
               (t q))
             (seq (starts S i) (starts S (Datatypes.S i) - starts S i))).
           ++ apply map_ext. intros q. destruct (Nat.eqb (starts S i + d) q).
              ** apply lit_of_key.
              ** reflexivity.
           ++ apply (map_seq_set (fun (q: nat) => lit_of (t q))). lia.
        -- rewrite
          (Hcl j Hj). f_equal. apply map_ext_in. intros q Hq. apply in_seq in Hq.
           destruct (r_starts0 j Hj) as [Hsj _].
           replace (Nat.eqb (starts S i + d) q) with false; [reflexivity|].
           symmetry. apply Nat.eqb_neq. intros Heq.
           destruct (Nat.lt_ge_cases j i) as [Hji | Hij].
           ++ assert (starts S (Datatypes.S j) <= starts S i)%nat by (apply Hle; lia).
              lia.
           ++ assert (starts S (Datatypes.S i) <= starts S j)%nat by (apply Hle; lia).
              lia.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* the clauses past the last are still none *)
    intros j Hj. cbn [set_clause cmap]. rewrite tget_tset_other by lia. now apply Hnone.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
Qed.

(* Setting clause i to the literals it has keeps the representation. *)
Lemma rep_clause_same {lt: list Lit}: forall (m: mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (i: nat) (ls: list Lit),
  RepL m S N lss x lims lt -> tget (cmap x) i = Some ls ->
    RepL m S N lss (set_clause x i ls) lims lt.
Proof.
  intros m S N lss x lims i ls HRep Hls.
  assert (Hsame: forall (j: nat), tget (tset (cmap x) i (Some ls)) j = tget (cmap x) j).
  { intros j. rewrite tget_tset. destruct (Nat.eq_dec i j) as [<- | Hne].
    - now rewrite Hls.
    - reflexivity. }
  destruct HRep. constructor; try assumption.
  - destruct a_lits0 as (t & At & Hatoms & Hcl). exists t. split.
    + assumption.
    + split.
      * assumption.
      * intros j Hj. cbn [set_clause cmap]. rewrite Hsame. now apply Hcl.
  - intros j Hj. cbn [set_clause cmap]. rewrite Hsame. now apply r_cmap0.
Qed.

(* Setting clause i twice is setting it to the second literals. *)
Lemma rep_clause_twice {lt: list Lit}: forall (m: mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (i: nat) (ls1 ls2: list Lit),
  RepL m S N lss (set_clause (set_clause x i ls1) i ls2) lims lt ->
  RepL m S N lss (set_clause x i ls2) lims lt.
Proof.
  intros m S N lss x lims i ls1 ls2 HRep.
  assert
    (Hsame: forall (j: nat), tget (tset (tset (cmap x) i (Some ls1)) i
      (Some ls2)) j = tget
      (tset (cmap x) i (Some ls2)) j).
  { intros j. rewrite !tget_tset. now destruct (Nat.eq_dec i j). }
  destruct HRep. constructor; try assumption.
  - destruct a_lits0 as (t & At & Hatoms & Hcl). exists t. split.
    + assumption.
    + split.
      * assumption.
      * intros j Hj. cbn [set_clause cmap]. rewrite <- Hsame. now apply Hcl.
  - intros j Hj. cbn [set_clause cmap]. rewrite <- Hsame. now apply r_cmap0.
Qed.

(* Setting the short clauses to ss, which the array of short clauses tsh holds (newest
   last): s->nshorts = length ss. *)
Lemma rep_store_shorts {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (ss: list nat) (tsh: nat -> Z),
  RepL m S N lss x lims lt -> Arr m (b_shorts S) (length lss) tsh ->
  (forall (q: nat), (q < length ss)%nat -> tsh q = Z.of_nat (nth q (rev ss) 0%nat)) ->
  (length ss <= length lss)%nat -> (forall (i: nat), In i ss -> (i < length lss)%nat) ->
  Mem.store Mint32 m (b_s S) 96 (vint (Z.of_nat (length ss))) = Some m' ->
  RepL m' S N lss (set_shorts x ss) lims lt.
Proof.
  intros m m' S N lss x lims ss tsh HRep Ash Htsh Hle Hcls Hst.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (fld_store m m' (b_s S) 96 Mint32 _ _ (r_nshorts _ _ _ _ _ _ _ HRep) Hst)
    as Fns.
  cbn [Val.load_result] in Fns. destruct HRep. unpack. carry Hst Hnd.
  (* Every field is as before, but the short clauses, which the hypotheses describe. *)
  constructor; try assumption.
  - repack.
  - (* the array of short clauses *)
    exists tsh. split.
    + assumption.
    + intros q Hq. apply Htsh. assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
Qed.

(* A store to the array of short clauses while the context has none. *)
Lemma rep_store_short_entry {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (ts: nat -> Z) (k: nat) (z: Z),
  RepL m S N lss x lims lt -> shorts x = [] -> Arr m (b_shorts S) (length lss) ts ->
  (k < length lss)%nat ->
  Mem.store Mint32 m (b_shorts S) (4 * Z.of_nat k) (vint z) = Some m' ->
  RepL m' S N lss x lims lt.
Proof.
  intros m m' S N lss x lims ts k z HRep Hsh Ats Hk Hst.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (arr_store m m' (b_shorts S) (length lss) k ts z Ats Hk Hst) as Ats'.
  destruct HRep. unpack. carry Hst Hnd.
  (* Every field is as before; there are still no short clauses. *)
  constructor; try assumption.
  - repack.
  - exists (fun (j: nat) => if Nat.eqb k j then z else ts j). split.
    + assumption.
    + intros q Hq. rewrite Hsh in Hq. cbn [length] in Hq. lia.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
Qed.

(* Storing the phase o of atom a: s->phs[a] = enc_value o. *)
Lemma rep_store_phs {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (a: nat) (o: option bool),
  RepL m S N lss x lims lt -> (a < N)%nat ->
  Mem.store Mint32 m (b_phs S) (4 * Z.of_nat a) (vint (enc_value o)) = Some m' ->
  RepL m' S N lss (set_phs x (tset (phs x) a o)) lims lt.
Proof.
  intros m m' S N lss x lims a o HRep Ha Hst.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (arr_store m m' (b_phs S) N a _ _ (a_phs _ _ _ _ _ _ _ HRep) Ha Hst) as
    Aphs.
  destruct HRep. unpack. carry Hst Hnd.
  (* Every field but the phases is as before. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* the phases: atom a now has the phase o *)
    cbn [set_phs phs]. arr_tset.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
Qed.

(* Marking (b = true) or unmarking the literal with key k: s->mrk[k] = enc_mark b. *)
Lemma rep_store_mrk {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (k: nat) (b: bool),
  RepL m S N lss x lims lt -> (k < 2 * N)%nat ->
  Mem.store Mint32 m (b_mrk S) (4 * Z.of_nat k) (vint (enc_mark b)) = Some m' ->
  RepL m' S N lss (set_mrk x (tset (mrk x) k b)) lims lt.
Proof.
  intros m m' S N lss x lims k b HRep Hk Hst.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (arr_store m m' (b_mrk S) (2 * N) k _ _ (a_mrk _ _ _ _ _ _ _ HRep) Hk Hst)
    as Amrk.
  destruct HRep. unpack. carry Hst Hnd.
  (* Every field but the marks is as before. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* the marks: key k now has mark b *)
    cbn [set_mrk mrk]. arr_tset.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
Qed.

(* Storing the reason r of atom a: s->rsn[a] = enc_reason r. *)
Lemma rep_store_rsn {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (a: nat) (r: Reason),
  RepL m S N lss x lims lt -> (a < N)%nat -> ReasonBelow (length lss) N r ->
  Mem.store Mint32 m (b_rsn S) (4 * Z.of_nat a) (vint (enc_reason r)) = Some m' ->
  RepL m' S N lss (set_rsn x (tset (rsn x) a r)) lims lt.
Proof.
  intros m m' S N lss x lims a r HRep Ha Hr Hst.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_rsn_below _ _ _ _ _ _ _ HRep) as Hbelow.
  pose proof (arr_store m m' (b_rsn S) N a _ _ (a_rsn _ _ _ _ _ _ _ HRep) Ha Hst) as
    Arsn.
  destruct HRep. unpack. carry Hst Hnd.
  (* Every field but the reasons is as before. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* the reasons: atom a now has reason r *)
    cbn [set_rsn rsn]. arr_tset.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* the reasons have clauses that C can find, r too *)
    intros a' Ha'. cbn [set_rsn rsn]. rewrite tget_tset.
    destruct (Nat.eq_dec a a') as [<- | Hne].
    + assumption.
    + apply Hbelow. assumption.
Qed.

(* Storing the level d of atom a: s->lvl[a] = d. *)
Lemma rep_store_lvl {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (a d: nat),
  RepL m S N lss x lims lt -> (a < N)%nat -> (d <= N)%nat ->
  Mem.store Mint32 m (b_lvl S) (4 * Z.of_nat a) (vint (Z.of_nat d)) = Some m' ->
  RepL m' S N lss (set_lvl x (tset (lvl x) a d)) lims lt.
Proof.
  intros m m' S N lss x lims a d HRep Ha Hd Hst.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_lvl_le _ _ _ _ _ _ _ HRep) as Hlvl.
  pose proof (arr_store m m' (b_lvl S) N a _ _ (a_lvl _ _ _ _ _ _ _ HRep) Ha Hst) as
    Alvl.
  destruct HRep. unpack. carry Hst Hnd.
  (* Every field but the levels is as before. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* the levels: atom a now has level d *)
    cbn [set_lvl lvl]. arr_tset.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* the levels are at most N, d too *)
    intros a' Ha'. cbn [set_lvl lvl]. rewrite tget_tset.
    destruct (Nat.eq_dec a a') as [<- | Hne].
    + assumption.
    + apply Hlvl. assumption.
Qed.

(* Appending y to the lower literals of the analysis: s->lt[n] = y; s->ltlen = n + 1, for
   n = length lt. *)
Lemma rep_store_lt {lt: list Lit}: forall (m m1 m2: mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (y: Lit),
  RepL m S N lss x lims lt -> (length lt < N)%nat -> (extract y < N)%nat ->
  Mem.store Mint32 m (b_lt S) (4 * Z.of_nat (length lt)) (vint (key y)) = Some m1 ->
  Mem.store Mint32 m1 (b_s S) 184 (vint (Z.of_nat (Datatypes.S (length lt)))) = Some m2
    ->
  RepL m2 S N lss x lims (lt ++ [y]).
Proof.
  intros m m1 m2 S N lss x lims y HRep Hlen Hy Hst1 Hst2.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_lt_atoms _ _ _ _ _ _ _ HRep) as Hatoms.
  pose proof (a_lt _ _ _ _ _ _ _ HRep) as (tlt & Alt & Htlt).
  pose proof (r_ltlen _ _ _ _ _ _ _ HRep) as Fltlen.
  pose proof (arr_store m m1 (b_lt S) N (length lt) _ _ Alt Hlen Hst1) as Alt1.
  destruct HRep. unpack. carry Hst1 Hnd.
  pose proof (fld_store m1 m2 (b_s S) 184 Mint32 _ _ Fltlen Hst2) as Fltlen2.
  carry Hst2 Hnd. cbn [Val.load_result] in Fltlen2.
  (* Every field but the lower literals is as before. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* their number *)
    rewrite length_app. cbn [length]. rewrite Nat.add_1_r. assumption.
  - (* y is the new last entry *)
    eexists. split.
    + apply Alt1.
    + intros k Hk. rewrite length_app in Hk. cbn [length] in Hk.
      destruct (Nat.eq_dec (length lt) k) as [<- | Hne].
      * rewrite Nat.eqb_refl, nth_middle. reflexivity.
      * replace (Nat.eqb (length lt) k) with false by (symmetry; now apply Nat.eqb_neq).
        rewrite app_nth1 by lia. apply Htlt. lia.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* at most N of them *)
    rewrite length_app. cbn [length]. lia.
  - (* with atoms below N, y too *)
    intros y' Hy'. apply in_app_or in Hy' as [Hy' | [<- | []]].
    + apply Hatoms. assumption.
    + assumption.
Qed.

(* Ending the analysis: s->ltlen = 0. *)
Lemma rep_store_ltlen_zero {lt: list Lit}: forall (m m': mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat),
  RepL m S N lss x lims lt -> Mem.store Mint32 m (b_s S) 184 (vint 0) = Some m' ->
  RepB m' S N lss x lims.
Proof.
  intros m m' S N lss x lims HRep Hst.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (fld_store m m' (b_s S) 184 Mint32 _ _ (r_ltlen _ _ _ _ _ _ _ HRep) Hst)
    as Fltlen.
  cbn [Val.load_result] in Fltlen. destruct HRep. unpack. carry Hst Hnd.
  (* Every field but the lower literals is as before, and there are none. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - eexists. split.
    + eassumption.
    + intros k Hk. cbn [length] in Hk. lia.
  - repack.
  - repack.
  - repack.
  - repack.
  - cbn [length]. lia.
  - intros y [].
Qed.

(* Dropping the reason clauses from n on, n <= nr x: s->rtop = s->rbeg[n]; s->nr = n. *)
Lemma rep_store_pop {lt: list Lit}: forall (m m1 m2: mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (n: nat),
  RepL m S N lss x lims lt -> (n <= nr x)%nat ->
  Mem.store Mint32 m (b_s S) 204 (vint (Z.of_nat (reasons_size (rcl x) n))) = Some m1 ->
  Mem.store Mint32 m1 (b_s S) 232 (vint (Z.of_nat n)) = Some m2 ->
  RepL m2 S N lss (set_nr x n) lims lt.
Proof.
  intros m m1 m2 S N lss x lims n HRep Hn Hst1 Hst2.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_rsize_le _ _ _ _ _ _ _ HRep) as Hsize.
  pose proof (r_rcl_atoms _ _ _ _ _ _ _ HRep) as Hatoms.
  pose proof (r_rps_le _ _ _ _ _ _ _ HRep) as Hrps.
  pose proof (a_rlits _ _ _ _ _ _ _ HRep) as (trl & Arl & Htrl).
  pose proof (a_rbeg _ _ _ _ _ _ _ HRep) as (tb & Arb & Htb).
  pose proof (a_rlen _ _ _ _ _ _ _ HRep) as (tn & Arn & Htn).
  pose proof (a_rpos _ _ _ _ _ _ _ HRep) as (tp & Arp & Htp).
  pose proof (r_nr _ _ _ _ _ _ _ HRep) as Fnr.
  pose proof (fld_store m m1 (b_s S) 204 Mint32 _ _ (r_rtop _ _ _ _ _ _ _ HRep) Hst1)
    as Frtop.
  destruct HRep. unpack. carry Hst1 Hnd.
  pose proof (fld_store m1 m2 (b_s S) 232 Mint32 _ _ Fnr Hst2) as Fnr2.
  carry Hst2 Hnd. cbn [Val.load_result] in Frtop, Fnr2.
  (* Every field is as before, but the reason clauses, which keep their first n. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* their literals *)
    exists trl. split.
    + assumption.
    + intros j k Hj Hk. apply Htrl.
      * cbn [set_nr nr] in Hj. lia.
      * assumption.
  - (* their starts *)
    exists tb. split.
    + assumption.
    + intros j Hj. apply Htb. cbn [set_nr nr] in Hj. lia.
  - (* their lengths *)
    exists tn. split.
    + assumption.
    + intros j Hj. apply Htn. cbn [set_nr nr] in Hj. lia.
  - (* their trail positions *)
    exists tp. split.
    + assumption.
    + intros j Hj. apply Htp. cbn [set_nr nr] in Hj. lia.
  - (* at most N of them *)
    cbn [set_nr nr]. lia.
  - (* within the room, as the first n take less than all *)
    cbn [set_nr nr rcl rcap]. transitivity (reasons_size (rcl x) (nr x)).
    + apply reasons_size_le. assumption.
    + assumption.
  - (* their atoms *)
    intros j y Hj Hy. apply (Hatoms j y).
    + cbn [set_nr nr] in Hj. lia.
    + assumption.
  - (* their trail positions are at most N *)
    intros j Hj. apply Hrps. cbn [set_nr nr] in Hj. lia.
Qed.

(* Setting the marks to what they are keeps the representation. *)
Lemma rep_mrk_same {lt: list Lit}: forall (m: mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat),
  RepL m S N lss x lims lt -> RepL m S N lss (set_mrk x (mrk x)) lims lt.
Proof. intros m S N lss x lims HRep. destruct HRep. constructor; assumption. Qed.

(* Keeping all the reason clauses keeps the representation. *)
Lemma rep_nr_same {lt: list Lit}: forall (m: mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (n: nat),
  RepL m S N lss x lims lt -> n = nr x -> RepL m S N lss (set_nr x n) lims lt.
Proof. intros m S N lss x lims n HRep ->. destruct HRep. constructor; assumption. Qed.

(* Pushing reason clause nr x after its literals, start, length and trail position were
   stored in the blocks rlits, rbeg, rlen and rpos, with nothing else changed:
   s->rtop = reasons_size; s->nr = nr x + 1, for x' = add_reason x c. *)
Lemma rep_store_push {lt: list Lit}: forall (m m1 m2 m3: mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (c: list Lit)
    (trl tb tn tp: nat -> Z),
  RepL m S N lss x lims lt -> (nr x < N)%nat ->
  (reasons_size (rcl x) (nr x) + length c <= rcap x)%nat ->
  (forall (y: Lit), In y c -> (extract y < N)%nat) ->
  Mem.unchanged_on
    (fun (b: block)
      (_: Z) => b <> b_rlits S /\ b <> b_rbeg S /\ b <> b_rlen S /\ b <> b_rpos S) m m1
        ->
  Arr m1 (b_rlits S) (rcap x) trl -> ReasonsIn trl (rcl (add_reason x c))
    (nr (add_reason x c)) ->
  Arr m1 (b_rbeg S) N tb ->
  (forall (j: nat), (j <= nr x)%nat -> tb j = Z.of_nat (reasons_size (rcl x) j)) ->
  Arr m1 (b_rlen S) N tn ->
  (forall (j: nat), (j <= nr x)%nat -> tn j = Z.of_nat (length (tget (rcl (add_reason x
    c)) j))) ->
  Arr m1 (b_rpos S) N tp ->
  (forall (j: nat), (j <= nr x)%nat -> tp j = Z.of_nat (tget (rps (add_reason x c)) j))
    ->
  Mem.store Mint32 m1 (b_s S) 204
    (vint (Z.of_nat (reasons_size (rcl x) (nr x) + length c))) = Some m2 ->
  Mem.store Mint32 m2 (b_s S) 232 (vint (Z.of_nat (Datatypes.S (nr x)))) = Some m3 ->
  RepL m3 S N lss (add_reason x c) lims lt.
Proof.
  intros m m1 m2 m3 S N lss x lims c trl tb tn tp HRep Hnr Hroom Hc Hun Arl Htrl Arb Htb
    Arn Htn Arp Htp Hst2 Hst3.
  pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
  pose proof (r_tlen_le _ _ _ _ _ _ _ HRep) as Htlen.
  pose proof (r_rcl_atoms _ _ _ _ _ _ _ HRep) as Hatoms.
  pose proof (r_rps_le _ _ _ _ _ _ _ HRep) as Hrps.
  pose proof (r_nr _ _ _ _ _ _ _ HRep) as Fnr.
  pose proof (r_rtop _ _ _ _ _ _ _ HRep) as Frtop.
  (* The size of the reason clauses with c. *)
  assert (Hsize: reasons_size (rcl (add_reason x c)) (nr (add_reason x c))
                 = (reasons_size (rcl x) (nr x) + length c)%nat).
  { cbn [add_reason rcl nr reasons_size]. rewrite reasons_size_tset by lia.
    rewrite tget_tset_same. reflexivity. }
  destruct HRep. unpack. transfer Hun Hnd. keep_mem m1.
  pose proof (fld_store m1 m2 (b_s S) 204 Mint32 _ _ Frtop Hst2) as Frtop2.
  carry Hst2 Hnd.
  pose proof (fld_store m2 m3 (b_s S) 232 Mint32 _ _ Fnr Hst3) as Fnr3.
  carry Hst3 Hnd. cbn [Val.load_result] in Frtop2, Fnr3. rewrite <- Hsize in Frtop2.
  (* Every field is as before, but the reason clauses, which get c; Hnr bounds their
     number. *)
  constructor; try assumption.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - repack.
  - (* their literals *)
    exists trl. split.
    + assumption.
    + assumption.
  - (* their starts *)
    exists tb. split.
    + assumption.
    + intros j Hj. cbn [add_reason nr rcl] in Hj |- *. rewrite reasons_size_tset by lia.
      apply Htb. lia.
  - (* their lengths *)
    exists tn. split.
    + assumption.
    + intros j Hj. apply Htn. cbn [add_reason nr] in Hj. lia.
  - (* their trail positions *)
    exists tp. split.
    + assumption.
    + intros j Hj. apply Htp. cbn [add_reason nr] in Hj. lia.
  - (* within the room *)
    rewrite Hsize. cbn [add_reason rcap]. assumption.
  - (* their atoms, those of c too *)
    intros j y Hj Hy. cbn [add_reason nr rcl] in Hj, Hy. rewrite tget_tset in Hy.
    destruct (Nat.eq_dec (nr x) j) as [<- | Hne].
    + apply Hc. assumption.
    + apply (Hatoms j y).
      * lia.
      * assumption.
  - (* their trail positions are at most N, the end of the trail too *)
    intros j Hj. cbn [add_reason nr rps] in Hj |- *. rewrite tget_tset.
    destruct (Nat.eq_dec (nr x) j) as [<- | Hne].
    + assumption.
    + apply Hrps. lia.
Qed.

(* The value C keeps for a literal: the value of its atom, negated for a negative
   literal. *)
Lemma enc_lookup: forall (v: Values) (l: Lit),
  enc_value (lookup v l) =
    if is_pos l then enc_value (tget v (extract l))
    else - enc_value (tget v (extract l)).
Proof.
  intros v l. unfold lookup. destruct (tget v (extract l)) as [[|]|], (is_pos l);
    reflexivity.
Qed.

(* Entry key l of s->vals is the value of l. *)
Lemma key_value_lookup: forall (v: Values) (l: Lit),
  key_value v (lit_key l) = enc_value (lookup v l).
Proof.
  intros v [p|p]; rewrite enc_lookup; unfold key_value; cbn [lit_key extract is_pos].
  - rewrite Nat.even_mul. cbn [orb]. now rewrite Nat.div2_double.
  - rewrite Nat.even_succ, Nat.odd_mul, Nat.odd_2. cbn [andb].
    now rewrite Nat.div2_succ_double.
Qed.

(* The key of a literal with an atom below N is small. *)
(* N < 2^28, so keys are below 2^29. *)
Lemma key_small: forall (l: Lit) (N: nat), (extract l < N)%nat ->
  Z.of_nat N < 268435456 -> 0 <= key l < 536870912.
Proof. intros l N Hl HN. unfold key. destruct l; simpl in *; lia. Qed.

(* The key of a literal with an atom below N is below 2 N. *)
Lemma lit_key_lt: forall (l: Lit) (N: nat), (extract l < N)%nat ->
  (lit_key l < 2 * N)%nat.
Proof. intros [p|p] N Hl; cbn [lit_key extract] in *; lia. Qed.

(* Comparisons C makes on the value of a literal. *)
Lemma enc_undef: forall (v: Values) (l: Lit),
  Z.eqb (enc_value (lookup v l)) 0 = lookup_undef v l.
Proof. intros v l. unfold lookup_undef. now destruct (lookup v l) as [[|]|]. Qed.

Lemma enc_true: forall (v: Values) (l: Lit),
  Z.eqb (enc_value (lookup v l)) 1 = lookup_true v l.
Proof. intros v l. unfold lookup_true. now destruct (lookup v l) as [[|]|]. Qed.

Lemma enc_not_false: forall (v: Values) (l: Lit),
  negb (Z.eqb (enc_value (lookup v l)) (-1)) = not_false v l.
Proof. intros v l. unfold not_false. now destruct (lookup v l) as [[|]|]. Qed.

Lemma enc_small: forall (o: option bool), Small (enc_value o).
Proof. intros o. unfold Small. destruct o as [[|]|]; simpl; lia. Qed.

(* A literal or none, as C returns it. *)
Definition enc_lit (o: option Lit): Z :=
match o with
| Some l => key l
| None   => -1
end.

(* A count or none, as C returns it. *)
Definition enc_count (o: option nat): Z :=
match o with
| Some n => Z.of_nat n
| None   => -1
end.

(* Scanning a list by index: the first entry that passes the test is what find
   returns. *)
Lemma find_nth: forall {A: Type} (p: A -> bool) (l: list A) (d: A) (k: nat),
  (k < length l)%nat -> (forall (k': nat), (k' < k)%nat -> p (nth k' l d) = false) ->
  p (nth k l d) = true ->
  find p l = Some (nth k l d).
Proof.
  intros A p l d.
  induction l as [|a l IH]; intros k Hk Hbefore Hk_true; simpl in Hk |- *.
  - lia.
  - destruct k as [|k].
    + simpl in Hk_true. now rewrite Hk_true.
    + replace (p a) with false by (symmetry; apply (Hbefore 0%nat); lia). apply IH.
      * lia.
      * intros k' Hk'. apply (Hbefore (Datatypes.S k')). lia.
      * assumption.
Qed.

Lemma find_none_nth: forall {A: Type} (p: A -> bool) (l: list A) (d: A),
  (forall (k: nat), (k < length l)%nat -> p (nth k l d) = false) -> find p l = None.
Proof.
  intros A p l d. induction l as [|a l IH]; intros Hall; simpl in Hall |- *.
  - reflexivity.
  - replace (p a) with false by (symmetry; apply (Hall 0%nat); lia). apply IH.
    intros k Hk. apply (Hall (Datatypes.S k)). lia.
Qed.

(* A test holds for all entries of a range of a table exactly when it holds for each. *)
Lemma forallb_range_true: forall {A: Type} (p: A -> bool) (f: nat -> A) (a n: nat),
  (forall (q: nat), (a <= q < a + n)%nat -> p (f q) = true) ->
  forallb p (map f (seq a n)) = true.
Proof.
  intros A p f a n Hall. apply forallb_forall. intros y Hy.
  apply in_map_iff in Hy as [q [<- Hq]]. apply in_seq in Hq. apply Hall. assumption.
Qed.

Lemma forallb_range_false: forall {A: Type} (p: A -> bool) (f: nat -> A) (a n q: nat),
  (a <= q < a + n)%nat -> p (f q) = false -> forallb p (map f (seq a n)) = false.
Proof.
  intros A p f a n q Hq Hfalse. destruct (forallb p (map f (seq a n))) eqn:Hall.
  - rewrite forallb_forall in Hall. rewrite Hall in Hfalse.
    + discriminate.
    + apply in_map. apply in_seq. lia.
  - reflexivity.
Qed.

(* The literals of the clauses have atoms below N. *)
Lemma clause_atoms {lt: list Lit}: forall (m: mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat) (i: nat) (ls: list Lit) (l: Lit),
  RepL m S N lss x lims lt -> tget (cmap x) i = Some ls -> In l ls ->
    (extract l < N)%nat.
Proof.
  intros m S N lss x lims i ls l HRep Hi Hl.
  destruct (a_lits _ _ _ _ _ _ _ HRep) as (t & _ & Hatoms & Hcl).
  destruct (Nat.lt_ge_cases i (length lss)) as [Hlt | Hge].
  - rewrite (Hcl i Hlt) in Hi. injection Hi as <-. apply in_map_iff in Hl as [q [<- Hq]].
    apply in_seq in Hq. destruct (r_starts _ _ _ _ _ _ _ HRep i Hlt) as [_ Hle].
    destruct (Hatoms q) as [l0 [-> Hl0]].
    + lia.
    + now rewrite lit_of_key.
  - rewrite (r_cmap _ _ _ _ _ _ _ HRep i Hge) in Hi. discriminate.
Qed.

(* Literal d of clause i is the key at position starts i + d of block clits. *)
Lemma clause_lit {lt: list Lit}: forall (m: mem) (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (t: nat -> Z) (i d: nat) (cls: list Lit),
  RepL m S N lss x lims lt -> ClausesIn S N (length lss) t (cmap x) ->
    (i < length lss)%nat ->
  tget (cmap x) i = Some cls -> (d < length cls)%nat ->
  (starts S i + d < nclits S)%nat /\
    t (starts S i + d)%nat = key (nth d cls (Pos 0%nat)) /\
  (extract (nth d cls (Pos 0%nat)) < N)%nat.
Proof.
  intros m S N lss x lims t i d cls HRep [Hatoms Hcl] Hi Hcls Hd.
  destruct (r_starts _ _ _ _ _ _ _ HRep i Hi) as [Hsi Hsn].
  rewrite (Hcl i Hi) in Hcls. injection Hcls as <-.
  rewrite length_map, length_seq in Hd.
  assert (Hq: (starts S i + d < nclits S)%nat) by lia.
  destruct (Hatoms (starts S i + d)%nat Hq) as [l [Hl Hla]].
  assert (Hnth: nth d (map (fun (q: nat) => lit_of (t q))
                   (seq (starts S i) (starts S (Datatypes.S i) - starts S i)))
                     (Pos 0%nat) = l).
  - rewrite nth_indep with (d' := lit_of (t 0%nat)) by
      (rewrite length_map, length_seq; lia).
    pose proof
                  (map_nth (fun (q: nat) => lit_of (t q)) (seq (starts S i) (starts S
                    (Datatypes.S i) - starts S i)) 0%nat d) as
                    Hmap.
    cbv beta in Hmap. rewrite Hmap, seq_nth by lia. rewrite Hl. apply lit_of_key.
  - rewrite Hnth. split.
    + assumption.
    + split.
      * assumption.
      * assumption.
Qed.

(* The length of clause i is the length of its range. *)
Lemma clause_length: forall (m: mem) (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (t: nat -> Z) (i: nat) (cls: list Lit),
  ClausesIn S N (length lss) t (cmap x) -> (i < length lss)%nat ->
    tget (cmap x) i = Some cls ->
  length cls = (starts S (Datatypes.S i) - starts S i)%nat.
Proof.
  intros m S N lss x lims t i cls [_ Hcl] Hi Hcls. rewrite (Hcl i Hi) in Hcls.
  injection Hcls as <-. now rewrite length_map, length_seq.
Qed.

(* A list from a position before its end starts with the entry there. *)
Lemma skipn_nth: forall {A: Type} (l: list A) (d: A) (k: nat),
  (k < length l)%nat -> skipn k l = nth k l d :: skipn (Datatypes.S k) l.
Proof.
  intros A l d. induction l as [|a l IH]; intros k Hk; simpl in Hk.
  - lia.
  - destruct k as [|k].
    + reflexivity.
    + simpl. apply IH. lia.
Qed.

(* C compares literals by their keys. *)
Lemma key_eqb: forall (a b: Lit), Z.eqb (key a) (key b) = (a =? b).
Proof.
  intros a b. destruct (a =? b) eqn:Hab.
  - apply Lit.eqb_eq in Hab as ->. apply Z.eqb_refl.
  - apply Lit.eqb_neq in Hab. apply Z.eqb_neq. intros Hk. apply Hab. apply lit_key_inj.
    unfold key in Hk. lia.
Qed.

(* Scanning a range of a table: the first entry that passes the test is what find
   returns. *)
Lemma find_range_some: forall {A: Type} (p: A -> bool) (f: nat -> A) (a n q: nat),
  (a <= q < a + n)%nat -> (forall (q': nat), (a <= q' < q)%nat -> p (f q') = false) ->
  p (f q) = true ->
  find p (map f (seq a n)) = Some (f q).
Proof.
  intros A p f a n. revert a.
  induction n as [|n IH]; intros a q Hq Hbefore Hq_true; simpl.
  - lia.
  - destruct (Nat.eq_dec a q) as [-> | Hne].
    + now rewrite Hq_true.
    + rewrite Hbefore by lia. apply IH.
      * lia.
      * intros q' Hq'. apply Hbefore. lia.
      * assumption.
Qed.

Lemma find_range_none: forall {A: Type} (p: A -> bool) (f: nat -> A) (a n: nat),
  (forall (q: nat), (a <= q < a + n)%nat -> p (f q) = false) ->
  find p (map f (seq a n)) = None.
Proof.
  intros A p f a n. revert a. induction n as [|n IH]; intros a Hall; simpl.
  - reflexivity.
  - rewrite Hall by lia. apply IH. intros q Hq. apply Hall. lia.
Qed.

(* The trail of the solver in memory holds the assignment pm: its length (field tlen,
   at 80), and its literals oldest first. *)
Definition TrailIn (m: mem) (S: Shape) (N: nat) (pm: PA): Prop :=
  Fld m (b_s S) 80 Mint32 (vint (Z.of_nat (PA.length pm))) /\
  exists (t: nat -> Z), Arr m (b_tr S) N t /\
    forall (j: nat), (j < PA.length pm)%nat ->
      t j = key (nth j (trail_lits pm) (Pos 0%nat)).
