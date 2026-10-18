(* The C solver (../solver.c) represents a context of Propagate.v, with the positions of
   its decisions: Rep says how its memory holds them. The store lemmas (rep_store_...)
   say what each store of the C code does to the represented context. *)
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
From RocqSAT Require Import Assignment.
From RocqSAT.refinement Require Import Table.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import Heur.
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement Require Import Analysis.
From RocqSAT.refinement Require Import Step.
From RocqSAT.refinement Require Import SolverStep.
From RocqSAT.refinement.c Require Import Arrays.
From RocqSAT.refinement.c Require Import Logic.
From RocqSAT.refinement.c Require Import Common.
From RocqSAT.refinement.c Require Import solver.

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

(* The global id names the internal function f. *)
Abbreviation FunAt id f :=
  (exists (b: block), Genv.find_symbol ge id = Some b /\
     Genv.find_funct_ptr ge b = Some (Internal f)).

(* Every block but b0 (the region a function that writes only b0 leaves unchanged). *)
Abbreviation AllBut b0 := (fun (b: block) (_: Z) => b <> b0).

(* The name of a function defined in the program finds it. *)
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
   of the literal it asserted; act, heap, hpos and dlit the arrays of the heuristic. *)
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
  b_act: block;
  b_heap: block;
  b_hpos: block;
  b_dlit: block;
  starts: nat -> nat;
  lits: nat -> Lit;
  nclits: nat;
  offs: nat -> nat;
  caps: nat -> nat;
  npool: nat
}.

(* The pointer to the solver struct s, the first argument of every C function. *)
Definition sptr (sh: Shape): val := Vptr (b_s sh) Ptrofs.zero.

(* Watcher w of the pool t is e: entry 2 w holds its clause, and 2 w + 1 its blocker. *)
Definition WatcherAt (t: nat -> Z) (w: nat) (e: Watcher): Prop :=
  t (2 * w)%nat = Z.of_nat (fst e) /\ t (2 * w + 1)%nat = key (snd e).

(* The pool t holds the watch lists wl, except the watchers q of the list of key k with
   skip k q. *)
Definition PoolOf (sh: Shape) (N: nat) (t: nat -> Z) (wl: WatchLists)
  (skip: nat -> nat -> Prop): Prop :=
  forall (k q: nat), (k < 2 * N)%nat -> (q < length (tget wl k))%nat -> ~ skip k q ->
    WatcherAt t (offs sh k + q) (nth q (tget wl k) (0%nat, Pos 0%nat)).

(* The watch pool of sh holds t; t holds all the watch lists wl. *)
Abbreviation PoolArr m sh t := (Arr m (b_wpool sh) (2 * npool sh) t).
Abbreviation PoolFree sh N t wl := (PoolOf sh N t wl (fun (_ _: nat) => False)).

(* The pool t with watcher w set to e: its clause at entry 2 w, its blocker at 2 w + 1. *)
Definition set_watcher (t: nat -> Z) (w: nat) (e: Watcher): nat -> Z :=
  fun (q: nat) => if Nat.eqb (2 * w + 1) q then key (snd e)
                  else if Nat.eqb (2 * w) q then Z.of_nat (fst e) else t q.

(* Watcher w of set_watcher t w e is e. *)
Lemma set_watcher_same: forall (t: nat -> Z) (w: nat) (e: Watcher),
  WatcherAt (set_watcher t w e) w e.
Proof.
  intros t w e. unfold WatcherAt, set_watcher. rewrite !Nat.eqb_refl. split.
  - replace (Nat.eqb (2 * w + 1) (2 * w)) with false by
      (symmetry; apply Nat.eqb_neq; lia).
    reflexivity.
  - reflexivity.
Qed.

(* set_watcher t w e keeps the other watchers. *)
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
  Mem.store Mint32 m b (4 * Z.of_nat (2 * w)) (vnat (fst e)) = Some m1 ->
  Mem.store Mint32 m1 b (4 * Z.of_nat (2 * w + 1)) (vint (key (snd e))) = Some m2 ->
  Arr m2 b (2 * n) (set_watcher t w e).
Proof.
  intros m m1 m2 b n w t e A Hw Hst1 Hst2.
  pose proof (arr_store (k := (2 * w)) A ltac:(lia) Hst1) as A1.
  apply (arr_store (k := (2 * w + 1)) A1 ltac:(lia) Hst2).
Qed.

(* The positions starts i .. starts (i + 1) of the literals of clause i in block clits. *)
Abbreviation clause_range sh i := (seq (starts sh i) (starts sh (S i) - starts sh i)).

(* The keys t of block clits hold the clauses of cm, with atoms below N: clause i < ncl
   has the literals at the positions of its range. *)
Definition ClausesIn (sh: Shape) (N ncl: nat) (t: nat -> Z) (cm: ClauseMap): Prop :=
  (forall (q: nat), (q < nclits sh)%nat -> exists (l: Lit), t q = key l /\
    (extract l < N)%nat) /\
  forall (i: nat), (i < ncl)%nat ->
    tget cm i = Some (map (fun (q: nat) => lit_of (t q)) (clause_range sh i)).

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

(* A literal or none, as C returns it. *)
Definition enc_lit (o: option Lit): Z :=
match o with
| Some l => key l
| None   => -1
end.

(* A heap position or none, as C keeps it (entry a of s->hpos): -1 for none. *)
Definition enc_pos (o: option nat): Z :=
match o with
| Some i => Z.of_nat i
| None   => -1
end.

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

(* The offsets of the fields of struct solver (../../solver/solver.h), as CompCert lays
   them out on x86-64: an int takes 4 bytes, a pointer 8 bytes, at an offset that is a
   multiple of 8 (so after ncl at 4, cstart is at 8). *)
Abbreviation o_nv := 0 (only parsing).
Abbreviation o_ncl := 4 (only parsing).
Abbreviation o_cstart := 8 (only parsing).
Abbreviation o_clits := 16 (only parsing).
Abbreviation o_vals := 24 (only parsing).
Abbreviation o_wpool := 32 (only parsing).
Abbreviation o_npool := 40 (only parsing).
Abbreviation o_woff := 48 (only parsing).
Abbreviation o_wlen := 56 (only parsing).
Abbreviation o_wcap := 64 (only parsing).
Abbreviation o_tr := 72 (only parsing).
Abbreviation o_tlen := 80 (only parsing).
Abbreviation o_qhead := 84 (only parsing).
Abbreviation o_shorts := 88 (only parsing).
Abbreviation o_nshorts := 96 (only parsing).
Abbreviation o_alls := 104 (only parsing).
Abbreviation o_nlits := 112 (only parsing).
Abbreviation o_cur := 116 (only parsing).
Abbreviation o_saved := 120 (only parsing).
Abbreviation o_lims := 128 (only parsing).
Abbreviation o_dl := 136 (only parsing).
Abbreviation o_phs := 144 (only parsing).
Abbreviation o_mrk := 152 (only parsing).
Abbreviation o_rsn := 160 (only parsing).
Abbreviation o_lvl := 168 (only parsing).
Abbreviation o_lt := 176 (only parsing).
Abbreviation o_ltlen := 184 (only parsing).
Abbreviation o_rlits := 192 (only parsing).
Abbreviation o_rcap := 200 (only parsing).
Abbreviation o_rtop := 204 (only parsing).
Abbreviation o_rbeg := 208 (only parsing).
Abbreviation o_rlen := 216 (only parsing).
Abbreviation o_rpos := 224 (only parsing).
Abbreviation o_nr := 232 (only parsing).
Abbreviation o_act := 240 (only parsing).
Abbreviation o_inc := 248 (only parsing).
Abbreviation o_heap := 256 (only parsing).
Abbreviation o_hpos := 264 (only parsing).
Abbreviation o_hsize := 272 (only parsing).
Abbreviation o_dlit := 280 (only parsing).

(* Field o of struct s holds the int n, or a pointer to block b. *)
Abbreviation IntAt m sh o n := (Fld m (b_s sh) o Mint32 (vnat n)).
Abbreviation PtrAt m sh o b := (Fld m (b_s sh) o Mptr (Vptr b Ptrofs.zero)).

(* The blocks of the solver, which RepL says are distinct. *)
Abbreviation solver_blocks sh :=
  [b_s sh; b_cstart sh; b_clits sh; b_vals sh; b_wpool sh; b_woff sh; b_wlen sh;
   b_wcap sh; b_tr sh; b_shorts sh; b_alls sh; b_saved sh; b_lims sh; b_phs sh;
   b_mrk sh; b_rsn sh; b_lvl sh; b_lt sh; b_rlits sh; b_rbeg sh; b_rlen sh; b_rpos sh;
   b_act sh; b_heap sh; b_hpos sh; b_dlit sh].

(* The array t holds the stack s (newest first in the model) oldest first. *)
Abbreviation StackIn t s :=
  (forall (q: nat), (q < length s)%nat -> t q = Z.of_nat (nth q (rev s) 0)%nat).

(* How the memory m holds the context x, for N atoms and the clauses lss, in three
   parts: the layout, which never changes; the fields and arrays that hold the tables of
   x; and the bounds that keep the C code within its arrays and its ints. Between steps,
   Rep adds the watch lists and that no analysis is in progress. *)

(* The layout: the blocks of the solver are distinct, the fields of struct solver point
   to them, and the parts that never change (the number of atoms, the clauses' starts,
   the room of the watch lists) are in memory and fit their bounds. *)
Record Layout {m: mem} {sh: Shape} {N: nat} {lss: list (list Lit)}: Prop := {
  r_nodup: NoDup (solver_blocks sh);
  r_nv: IntAt m sh o_nv N;
  r_ncl: IntAt m sh o_ncl (length lss);
  r_cstart: PtrAt m sh o_cstart (b_cstart sh);
  r_clits: PtrAt m sh o_clits (b_clits sh);
  r_vals: PtrAt m sh o_vals (b_vals sh);
  r_wpool: PtrAt m sh o_wpool (b_wpool sh);
  r_npool: IntAt m sh o_npool (npool sh);
  r_woff: PtrAt m sh o_woff (b_woff sh);
  r_wlen: PtrAt m sh o_wlen (b_wlen sh);
  r_wcap: PtrAt m sh o_wcap (b_wcap sh);
  r_tr: PtrAt m sh o_tr (b_tr sh);
  r_shorts: PtrAt m sh o_shorts (b_shorts sh);
  r_alls: PtrAt m sh o_alls (b_alls sh);
  r_saved: PtrAt m sh o_saved (b_saved sh);
  r_lims: PtrAt m sh o_lims (b_lims sh);
  r_phs: PtrAt m sh o_phs (b_phs sh);
  a_starts: Arr m (b_cstart sh) (S (length lss))
    (fun (i: nat) => Z.of_nat (starts sh i));
  a_woff: Arr m (b_woff sh) (2 * N) (fun (k: nat) => Z.of_nat (offs sh k));
  a_wcap: Arr m (b_wcap sh) (2 * N) (fun (k: nat) => Z.of_nat (caps sh k));
  r_starts: forall (i: nat), (i < length lss)%nat ->
    (starts sh i <= starts sh (S i) <= nclits sh)%nat;
  r_n: Z.of_nat N < atom_bound;
  r_nclits_small: Z.of_nat (nclits sh) < small_bound;
  r_lss_small: Z.of_nat (length lss) < small_bound;
  r_pool_small: Z.of_nat (npool sh) < small_bound;
  r_room: forall (k: nat), (k < 2 * N)%nat -> (offs sh k + caps sh k <= npool sh)%nat;
  r_apart: forall (k k': nat), (k < k' < 2 * N)%nat ->
    (offs sh k + caps sh k <= offs sh k')%nat;
  r_mrk: PtrAt m sh o_mrk (b_mrk sh);
  r_rsn: PtrAt m sh o_rsn (b_rsn sh);
  r_lvl: PtrAt m sh o_lvl (b_lvl sh);
  r_lt: PtrAt m sh o_lt (b_lt sh);
  r_rlits: PtrAt m sh o_rlits (b_rlits sh);
  r_rbeg: PtrAt m sh o_rbeg (b_rbeg sh);
  r_rlen: PtrAt m sh o_rlen (b_rlen sh);
  r_rpos: PtrAt m sh o_rpos (b_rpos sh);
  r_act: PtrAt m sh o_act (b_act sh);
  r_heap: PtrAt m sh o_heap (b_heap sh);
  r_hpos: PtrAt m sh o_hpos (b_hpos sh);
  r_dlit: PtrAt m sh o_dlit (b_dlit sh)
}.
Arguments Layout : clear implicits.

(* The tables of x in memory: each int field of struct solver holds the value of x, and
   each array the encoding of its table. *)
Record Holds {m: mem} {sh: Shape} {N: nat} {lss: list (list Lit)} {x: Ctx}: Prop := {
  r_tlen: IntAt m sh o_tlen (tlen x);
  r_qhead: IntAt m sh o_qhead (qhead x);
  r_nshorts: IntAt m sh o_nshorts (length (shorts x));
  r_nlits: IntAt m sh o_nlits (nlits x);
  r_cur: IntAt m sh o_cur (cur x);
  r_dl: IntAt m sh o_dl (length (lims x));
  a_lits: exists (t: nat -> Z), Arr m (b_clits sh) (nclits sh) t /\
    ClausesIn sh N (length lss) t (cmap x);
  a_vals: Arr m (b_vals sh) (2 * N) (key_value (vals x));
  a_wlen: Arr m (b_wlen sh) (2 * N) (fun (k: nat) => Z.of_nat (length (tget (wls x) k)));
  a_tr: Arr m (b_tr sh) N (fun (j: nat) => key (tget (tr x) j));
  a_shorts: exists (t: nat -> Z),
    Arr m (b_shorts sh) (length lss) t /\ StackIn t (shorts x);
  a_alls: exists (t: nat -> Z), Arr m (b_alls sh) (2 * N) t /\
    forall (k: nat), (k < nlits x)%nat -> t k = key (tget (alls x) k);
  a_saved: exists (t: nat -> Z), Arr m (b_saved sh) N t /\ StackIn t (saved x);
  a_lims: exists (t: nat -> Z), Arr m (b_lims sh) N t /\ StackIn t (lims x);
  a_phs: Arr m (b_phs sh) N (fun (a: nat) => enc_value (tget (phs x) a));
  r_ltlen: IntAt m sh o_ltlen (length (lower x));
  r_rcap: IntAt m sh o_rcap (rcap x);
  r_rtop: IntAt m sh o_rtop (reasons_size (rcl x) (nr x));
  r_nr: IntAt m sh o_nr (nr x);
  a_mrk: Arr m (b_mrk sh) (2 * N) (fun (k: nat) => enc_mark (tget (mrk x) k));
  a_rsn: Arr m (b_rsn sh) N (fun (a: nat) => enc_reason (tget (rsn x) a));
  a_lvl: Arr m (b_lvl sh) N (fun (a: nat) => Z.of_nat (tget (lvl x) a));
  a_lt: exists (t: nat -> Z), Arr m (b_lt sh) N t /\
    forall (k: nat), (k < length (lower x))%nat ->
      t k = key (nth k (lower x) (Pos 0%nat));
  a_rlits: exists (t: nat -> Z), Arr m (b_rlits sh) (rcap x) t /\
    ReasonsIn t (rcl x) (nr x);
  a_rbeg: exists (t: nat -> Z), Arr m (b_rbeg sh) N t /\
    forall (j: nat), (j < nr x)%nat -> t j = Z.of_nat (reasons_size (rcl x) j);
  a_rlen: exists (t: nat -> Z), Arr m (b_rlen sh) N t /\
    forall (j: nat), (j < nr x)%nat -> t j = Z.of_nat (length (tget (rcl x) j));
  a_rpos: exists (t: nat -> Z), Arr m (b_rpos sh) N t /\
    forall (j: nat), (j < nr x)%nat -> t j = Z.of_nat (tget (rps x) j);
  r_inc: Fld m (b_s sh) o_inc Mint32 (vint (inc (hr x)));
  r_hsize: IntAt m sh o_hsize (hsize (hr x));
  a_act: Arr m (b_act sh) N (fun (a: nat) => tget (act (hr x)) a);
  a_heap: Arr m (b_heap sh) N (fun (i: nat) => Z.of_nat (tget (heap (hr x)) i));
  a_hpos: Arr m (b_hpos sh) N (fun (a: nat) => enc_pos (tget (hpos (hr x)) a));
  a_dlit: Arr m (b_dlit sh) N (fun (a: nat) => enc_lit (tget (dlit (hr x)) a))
}.
Arguments Holds : clear implicits.

(* The bounds of x, which do not mention memory: indices stay within the arrays and values
   within the ints of the C code. *)
Record Bounded {sh: Shape} {N: nat} {lss: list (list Lit)} {x: Ctx}: Prop := {
  r_cmap: forall (i: nat), (length lss <= i)%nat -> tget (cmap x) i = None;
  r_nvars: nvars x = N;
  r_wlen_le: forall (k: nat), (k < 2 * N)%nat ->
    (length (tget (wls x) k) <= caps sh k)%nat;
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
  r_saved_len: length (saved x) = length (lims x);
  r_dl_le: (length (lims x) <= N)%nat;
  r_dl_eq: dl x = length (lims x);
  r_rsn_below: forall (a: nat), (a < N)%nat -> ReasonBelow (length lss) N
    (tget (rsn x) a);
  r_lvl_le: forall (a: nat), (a < N)%nat -> (tget (lvl x) a <= N)%nat;
  r_lt_le: (length (lower x) <= N)%nat;
  r_lt_atoms: forall (y: Lit), In y (lower x) -> (extract y < N)%nat;
  r_nr_le: (nr x <= N)%nat;
  r_rsize_le: (reasons_size (rcl x) (nr x) <= rcap x)%nat;
  r_rcap_small: Z.of_nat (rcap x) < small_bound;
  r_rcl_atoms: forall (j: nat) (y: Lit), (j < nr x)%nat -> In y (tget (rcl x) j) ->
    (extract y < N)%nat;
  r_rps_le: forall (j: nat), (j < nr x)%nat -> (tget (rps x) j <= N)%nat;
  r_heur: HeurOk N (hr x)
}.
Arguments Bounded : clear implicits.

(* The memory m holds the context x: its layout, its tables and its bounds. Each part is
   also a coercion, so the facts of a part apply to RepL directly: r_tlen_le HRep. *)
Record RepL {m: mem} {sh: Shape} {N: nat} {lss: list (list Lit)} {x: Ctx}: Prop := {
  r_layout :> Layout m sh N lss;
  r_holds :> Holds m sh N lss x;
  r_bounds :> Bounded sh N lss x
}.
(* RepL takes its arguments explicitly; its projections infer them from the record:
   r_n HRep. *)
Arguments RepL : clear implicits.

(* The blocks of the solver, as a list to pass to the specs of helper functions. *)
Definition iblocks (sh: Shape): list block := solver_blocks sh.

(* Between steps: no analysis in progress, and the watch lists in the pool. *)
Definition Rep (m: mem) (sh: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx): Prop :=
  RepL m sh N lss x /\ lower x = [] /\
  exists (t: nat -> Z), PoolArr m sh t /\ PoolFree sh N t (wls x).

(* The three shapes of what a C function promises, from the memory m of the call to the
   memory m' at its return, with result v: *)
(* it stores nothing and returns r; *)
Abbreviation Reads m m' v r := (m' = m /\ v = r).
(* it changes the represented context to x', and nothing outside the frame B; *)
Abbreviation Changes sh N lss B x' m m' :=
  (RepL m' sh N lss x' /\ Mem.unchanged_on B m m').
(* it returns r, and changes the represented context to x' within the frame B. *)
Abbreviation Gives sh N lss B x' r m m' v := (v = r /\ Changes sh N lss B x' m m').

(* x with the cursor c, the saved cursors st, the decision level d and the decision
   positions ls. *)
Definition set_level (x: Ctx) (c: nat) (st: list nat) (d: nat) (ls: list nat): Ctx :=
  mkCtx (vals x) (cmap x) (wls x) (tr x) (tlen x) (qhead x) (shorts x) (alls x) (nlits x)
    c st ls (rsn x) (lvl x) d (mrk x) (lower x) (phs x) (nvars x) (rcl x) (rps x) (nr x)
    (rcap x) (hr x).

(* The watchers ws have clauses below ncl and blockers of atoms below N. *)
Abbreviation WatchersBelow ncl N ws :=
  (forall (i: nat) (b: Lit), In (i, b) ws -> (i < ncl)%nat /\ (extract b < N)%nat).

(* Replacing entry d of ls by y. *)
Definition set_nth (d: nat) (y: Lit) (ls: list Lit): list Lit :=
  firstn d ls ++ y :: skipn (S d) ls.

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
    + replace (Nat.eqb (a + S d) a) with false
        by (symmetry; apply Nat.eqb_neq; lia).
      unfold set_nth. cbn [firstn skipn app]. f_equal.
      replace (a + S d)%nat with (S a + d)%nat by lia.
      apply IH. lia.
Qed.

(* The store lemmas: what a store of the C code does to the context x that the memory
   represents, for N atoms and the clauses lss of the shape sh. *)
Section Stores.
  Context {sh: Shape} {N: nat} {lss: list (list Lit)} {x: Ctx}.

  (* Storing the value o of atom a, for both its literals: s->vals[2a] = enc_value o and
     s->vals[2a + 1] = -enc_value o. *)
  Lemma rep_store_vals: forall (m m1 m': mem) (a: nat) (o: option bool),
    RepL m sh N lss x -> (a < N)%nat ->
    Mem.store Mint32 m (b_vals sh) (4 * Z.of_nat (2 * a)) (vint (enc_value o)) =
      Some m1 ->
    Mem.store Mint32 m1 (b_vals sh) (4 * Z.of_nat (2 * a + 1)) (vint (- enc_value o))
      = Some m' ->
    RepL m' sh N lss (x <| vals := tset (vals x) a o |>).
  Proof.
    intros m m1 m' a o HRep Ha Hst1 Hst2.
    pose proof (r_nodup HRep) as Hnd.
    assert (Ha1: (2 * a < 2 * N)%nat) by lia.
    assert (Ha2: (2 * a + 1 < 2 * N)%nat) by lia.
    pose proof (arr_store (a_vals HRep) Ha1 Hst1) as Avals1.
    pose proof (arr_store Avals1 Ha2 Hst2) as Avals.
    destruct HRep as [[] [] []]. carry Hst1 Hnd. carry Hst2 Hnd.
    (* Every field but the values is as before. *)
    constructor; constructor; try assumption; try repack.
    - (* the values: both literals of atom a now have the values of o *)
      cbn [set_vals vals]. eapply arr_ext.
      + apply Avals.
      + (* Entry j belongs to atom j / 2, and is that of its positive literal for even j:
           compare j with 2a and 2a + 1, through j = 2 (j / 2) + (j odd). *)
        intros j Hj. rewrite key_value_set. pose proof (Nat.div2_odd j) as Hdiv.
        rewrite <- Nat.negb_odd.
        destruct (Nat.odd j), (Nat.eq_dec a (Nat.div2 j)), (Nat.eqb_spec (2 * a + 1) j),
          (Nat.eqb_spec (2 * a) j); cbn [negb Nat.b2n] in *; (reflexivity || lia).
  Qed.

  (* Storing literal l at position j of the trail, from its end on: s->tr[j] = l. *)
  Lemma rep_store_tr: forall (m m': mem) (j: nat) (l: Lit),
    RepL m sh N lss x -> (tlen x <= j < N)%nat ->
    Mem.store Mint32 m (b_tr sh) (4 * Z.of_nat j) (vint (key l)) = Some m' ->
    RepL m' sh N lss (x <| tr := tset (tr x) j l |>).
  Proof.
    intros m m' j l HRep Hj Hst.
    assert (HjN: (j < N)%nat) by lia.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (r_tr_atoms HRep) as Hatoms.
    pose proof (arr_store (a_tr HRep) HjN Hst) as Atr.
    destruct HRep as [[] [] []]. carry Hst Hnd.
    (* Every field but the trail is as before. *)
    constructor; constructor; try assumption; try repack.
    - (* the trail: position j now holds l *)
      cbn [set_tr tr]. arr_tset.
    - (* the trail up to its end is unchanged, as j is not below it *)
      intros j' Hj'. cbn [set_tr tr tlen] in *. rewrite tget_tset.
      destruct (Nat.eq_dec j j') as [-> | Hne].
      + lia.
      + apply Hatoms. assumption.
  Qed.

  (* Setting the length of the trail to n: s->tlen = n. *)
  Lemma rep_store_tlen: forall (m m': mem) (n: nat),
    RepL m sh N lss x -> (n <= N)%nat -> (qhead x <= n)%nat ->
    (forall (j: nat), (j < n)%nat -> (extract (tget (tr x) j) < N)%nat) ->
    Mem.store Mint32 m (b_s sh) o_tlen (vnat n) = Some m' ->
    RepL m' sh N lss (x <| tlen := n |>).
  Proof.
    intros m m' n HRep Hn Hq Hatoms Hst.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (fld_store (r_tlen HRep) Hst) as Ftlen.
    cbn [Val.load_result] in Ftlen. destruct HRep as [[] [] []]. carry Hst Hnd.
    (* Every field is as before, but the length, its bounds and the atoms of the trail,
       which the hypotheses give. *)
    constructor; constructor; try assumption; try repack.
  Qed.

  (* Moving the head of the queue to n, within the trail: s->qhead = n. *)
  Lemma rep_store_qhead: forall (m m': mem) (n: nat),
    RepL m sh N lss x -> (n <= tlen x)%nat ->
    Mem.store Mint32 m (b_s sh) o_qhead (vnat n) = Some m' ->
    RepL m' sh N lss (x <| qhead := n |>).
  Proof.
    intros m m' n HRep Hn Hst.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (fld_store (r_qhead HRep) Hst) as Fqh.
    cbn [Val.load_result] in Fqh. destruct HRep as [[] [] []]. carry Hst Hnd.
    (* Every field is as before, but the head of the queue, which the hypothesis
       bounds. *)
    constructor; constructor; try assumption; try repack.
  Qed.

  (* Cutting the trail to its first j literals, with an empty queue:
     s->tlen = j; s->qhead = j. (Each store alone may break qhead <= tlen.) *)
  Lemma rep_store_cut: forall (m m1 m2: mem) (j: nat),
    RepL m sh N lss x -> (j <= tlen x)%nat ->
    Mem.store Mint32 m (b_s sh) o_tlen (vnat j) = Some m1 ->
    Mem.store Mint32 m1 (b_s sh) o_qhead (vnat j) = Some m2 ->
    RepL m2 sh N lss (x <| tlen := j |> <| qhead := j |>).
  Proof.
    intros m m1 m2 j HRep Hj Hst1 Hst2.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (r_tlen_le HRep) as Htle.
    pose proof (r_tr_atoms HRep) as Hatoms.
    pose proof (r_qhead HRep) as Fqh.
    pose proof (fld_store (r_tlen HRep) Hst1) as Ftlen1.
    destruct HRep as [[] [] []]. carry Hst1 Hnd.
    pose proof (fld_store Fqh Hst2) as Fqh2.
    carry Hst2 Hnd. cbn [Val.load_result] in Ftlen1, Fqh2.
    (* Every field is as before, but the length and the head of the queue, now j. *)
    constructor; constructor; try assumption; try repack.
    - (* the length is within the old one *)
      cbn [set_qhead set_tlen tlen]. lia.
    - (* the queue is empty *)
      cbn [set_qhead set_tlen tlen qhead]. lia.
    - (* the trail up to j is a part of the old one *)
      intros j' Hj'. cbn [set_qhead set_tlen tlen tr] in *. apply Hatoms. lia.
  Qed.

  (* Moving the cursor to c, within the literals to decide on: s->cur = c. *)
  Lemma rep_store_cur: forall (m m': mem) (c: nat),
    RepL m sh N lss x -> (c <= nlits x)%nat ->
    Mem.store Mint32 m (b_s sh) o_cur (vnat c) = Some m' ->
    RepL m' sh N lss (x <| cur := c |>).
  Proof.
    intros m m' c HRep Hc Hst.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (fld_store (r_cur HRep) Hst) as Fcur.
    cbn [Val.load_result] in Fcur. destruct HRep as [[] [] []]. carry Hst Hnd.
    (* Every field is as before, but the cursor, which the hypothesis bounds. *)
    constructor; constructor; try assumption; try repack.
  Qed.

  (* Opening a decision level at the cursor: the cursor is saved, and the position of the
     decision, the end of the trail, is recorded.
     s->saved[s->dl] = s->cur; s->lims[s->dl] = s->tlen; s->dl = s->dl + 1. *)
  Lemma rep_store_open_cur: forall (m m2 m3 m4: mem),
    RepL m sh N lss x -> (length (lims x) < N)%nat ->
    Mem.store Mint32 m (b_saved sh) (4 * Z.of_nat (length (lims x))) (vnat (cur x)) =
      Some m2 ->
    Mem.store Mint32 m2 (b_lims sh) (4 * Z.of_nat (length (lims x)))
      (vnat (tlen x)) = Some m3 ->
    Mem.store Mint32 m3 (b_s sh) o_dl (vnat (S (length (lims x)))) =
      Some m4 ->
    RepL m4 sh N lss (open_level x (cur x)).
  Proof.
    intros m m2 m3 m4 HRep Hroom Hst2 Hst3 Hst4.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (r_saved_le HRep) as Hsle.
    pose proof (r_saved_len HRep) as Hslen.
    pose proof (a_saved HRep) as (tsv & Asaved & Htsv).
    pose proof (a_lims HRep) as (tl & Alims & Htl).
    pose proof (r_dl HRep) as Fdl.
    destruct HRep as [[] [] []]. unpack.
    pose proof (arr_store Asaved Hroom Hst2) as Asaved2.
    carry Hst2 Hnd.
    pose proof (arr_store Alims Hroom Hst3) as Alims3.
    carry Hst3 Hnd.
    pose proof (fld_store Fdl Hst4) as Fdl4.
    carry Hst4 Hnd. cbn [Val.load_result] in Fdl4.
    (* Every field is as before, but the saved cursors and the decision positions, which
       get the cursor and tlen x as their last entries; the hypothesis bounds the new
       number of decisions. *)
    constructor; constructor; try assumption; try repack.
    - (* the saved cursors: the cursor is the new last entry *)
      eexists. split.
      + apply Asaved2.
      + intros j Hj. cbn [open_level saved length rev] in Hj |- *.
        destruct (Nat.eq_dec (length (lims x)) j) as [<- | Hne].
        * rewrite Nat.eqb_refl, <- Hslen, <- length_rev, nth_middle. reflexivity.
        * replace (Nat.eqb (length (lims x)) j) with false
            by (symmetry; now apply Nat.eqb_neq).
          rewrite app_nth1 by (rewrite length_rev; lia). apply Htsv. lia.
    - (* the decision positions: tlen x is the new last entry *)
      eexists. split.
      + apply Alims3.
      + intros j Hj. cbn [open_level lims length rev] in Hj |- *.
        destruct (Nat.eq_dec (length (lims x)) j) as [<- | Hne].
        * rewrite Nat.eqb_refl, <- length_rev, nth_middle. reflexivity.
        * replace (Nat.eqb (length (lims x)) j) with false
            by (symmetry; now apply Nat.eqb_neq).
          rewrite app_nth1 by (rewrite length_rev; lia). apply Htl. lia.
    - (* the saved cursors are within the literals to decide on *)
      intros c' [<- | Hin].
      + assumption.
      + now apply Hsle.
    - (* one saved cursor per decision *)
      cbn [open_level saved lims length]. lia.
    - (* one decision more *)
      cbn [open_level dl lims length]. f_equal. assumption.
  Qed.

  (* A store to the pool, whose entries RepL does not describe (Rep does, by PoolOf). *)
  Lemma rep_store_pool: forall (m m': mem) (ofs: Z) (v: val),
    RepL m sh N lss x -> Mem.store Mint32 m (b_wpool sh) ofs v = Some m' ->
    RepL m' sh N lss x.
  Proof.
    intros m m' ofs v HRep Hst.
    pose proof (r_nodup HRep) as Hnd.
    destruct HRep as [[] [] []]. carry Hst Hnd.
    (* Every field is as before. *)
    constructor; constructor; try assumption; try repack.
  Qed.

  (* Setting the watch list of l to ws, which the pool holds, by its length:
     s->wlen[l] = length ws. *)
  Lemma rep_store_watching: forall (m m': mem) (l: Lit) (ws: list Watcher),
    RepL m sh N lss x -> (extract l < N)%nat ->
    (length ws <= caps sh (lit_key l))%nat ->
    WatchersBelow (length lss) N ws ->
    Mem.store Mint32 m (b_wlen sh) (4 * Z.of_nat (lit_key l))
      (vnat (length ws)) = Some m' ->
    RepL m' sh N lss (set_watching x l ws).
  Proof.
    intros m m' l ws HRep Hl Hroom Hws Hst.
    assert (Hk: (lit_key l < 2 * N)%nat) by (destruct l; simpl in *; lia).
    pose proof (r_nodup HRep) as Hnd.
    pose proof (r_wlen_le HRep) as Hwle.
    pose proof (r_wls_cls HRep) as Hwcls.
    pose proof (r_wls_blk HRep) as Hwblk.
    pose proof (arr_store (a_wlen HRep) Hk Hst) as Awlen.
    destruct HRep as [[] [] []]. carry Hst Hnd.
    (* Every field is as before, but the watch lists and their bounds. *)
    constructor; constructor; try assumption; try repack.
    - (* the lengths: the list of l is ws *)
      eapply arr_ext.
      + apply Awlen.
      + intros j Hj. cbn [set_watching wls]. rewrite tget_tset.
        destruct (Nat.eq_dec (lit_key l) j) as [<- | Hne].
        * rewrite Nat.eqb_refl. reflexivity.
        * replace (Nat.eqb (lit_key l) j) with false by (symmetry; now apply Nat.eqb_neq).
          reflexivity.
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
  Qed.

  (* Appending the watcher of clause i with blocker b to the watch list of l, by its
     length: s->wlen[l] = n + 1, where n is the old length. *)
  Lemma rep_store_wlen: forall (m m': mem) (l: Lit) (i: nat) (b: Lit),
    RepL m sh N lss x -> (extract l < N)%nat ->
    (length (watching (wls x) l) < caps sh (lit_key l))%nat -> (i < length lss)%nat ->
    (extract b < N)%nat ->
    Mem.store Mint32 m (b_wlen sh) (4 * Z.of_nat (lit_key l))
      (vnat (S (length (watching (wls x) l)))) = Some m' ->
    RepL m' sh N lss (set_watching x l (watching (wls x) l ++ [(i, b)])).
  Proof.
    intros m m' l i b HRep Hl Hroom Hi Hb Hst.
    assert (Hk: (lit_key l < 2 * N)%nat) by (destruct l; simpl in *; lia).
    assert (Hlen: length (watching (wls x) l ++ [(i, b)])
                  = S (length (watching (wls x) l))).
    { rewrite length_app. cbn [length]. lia. }
    apply (rep_store_watching m m' l).
    - assumption.
    - assumption.
    - lia.
    - (* the watchers of the list of l, and that of clause i *)
      intros j c Hj. apply in_app_or in Hj as [Hj | [Heq | []]].
      + split.
        * apply (r_wls_cls HRep (lit_key l) j c); assumption.
        * apply (r_wls_blk HRep (lit_key l) j c); assumption.
      + injection Heq as <- <-. split; assumption.
    - rewrite Hlen. assumption.
  Qed.

  (* The clauses start in order. *)
  Lemma starts_le: forall (m: mem),
    RepL m sh N lss x ->
    forall (i j: nat), (i <= j <= length lss)%nat -> (starts sh i <= starts sh j)%nat.
  Proof.
    intros m HRep i j Hij. induction j as [|j IH].
    - assert (i = 0%nat) as -> by lia. lia.
    - destruct (Nat.eq_dec i (S j)) as [-> | Hne].
      + lia.
      + destruct (r_starts HRep j) as [Hj _].
        * lia.
        * assert (starts sh i <= starts sh j)%nat by (apply IH; lia). lia.
  Qed.

  (* Storing literal y as literal d of clause i: s->clits[starts i + d] = y. *)
  Lemma rep_store_clits: forall (m m': mem) (i d: nat) (ls: list Lit) (y: Lit),
    RepL m sh N lss x -> (i < length lss)%nat -> tget (cmap x) i = Some ls ->
    (d < length ls)%nat -> (extract y < N)%nat ->
    Mem.store Mint32 m (b_clits sh) (4 * Z.of_nat (starts sh i + d)) (vint (key y)) =
      Some m' ->
    RepL m' sh N lss (set_clause x i (set_nth d y ls)).
  Proof.
    intros m m' i d ls y HRep Hi Hls Hd Hy Hst.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (r_cmap HRep) as Hnone.
    destruct (r_starts HRep i Hi) as [Hsi Hsn].
    pose proof (starts_le m HRep) as Hle.
    destruct (a_lits HRep) as (t & At & Hatoms & Hcl).
    (* The literals of clause i are those from starts i on *)
    assert (Hlen: length ls = (starts sh (S i) - starts sh i)%nat).
    { rewrite (Hcl i Hi) in Hls. injection Hls as <-.
      now rewrite length_map, length_seq. }
    pose proof (arr_store (k := (starts sh i + d)) At ltac:(lia) Hst) as At'.
    destruct HRep as [[] [] []]. carry Hst Hnd.
    (* Every field is as before, but the literals of clause i. *)
    constructor; constructor; try assumption; try repack.
    - exists (fun (q: nat) => if Nat.eqb (starts sh i + d) q then key y else t q). split.
      + assumption.
      + split.
        * (* the atoms of the new literal and of the others *)
          intros q Hq. destruct (Nat.eqb (starts sh i + d) q).
          -- now exists y.
          -- now apply Hatoms.
        * (* clause i has y in place d, and the others their literals *)
          intros j Hj. cbn [set_clause cmap]. rewrite tget_tset.
          destruct (Nat.eq_dec i j) as [<- | Hne].
          -- rewrite (Hcl i Hi) in Hls. injection Hls as <-. f_equal. symmetry.
             transitivity
               (map (fun (q: nat) => if Nat.eqb (starts sh i + d) q then y
                                     else lit_of (t q))
                    (clause_range sh i)).
             ++ apply map_ext. intros q. destruct (Nat.eqb (starts sh i + d) q).
                ** apply lit_of_key.
                ** reflexivity.
             ++ apply (map_seq_set (fun (q: nat) => lit_of (t q))). lia.
          -- rewrite (Hcl j Hj). f_equal. apply map_ext_in. intros q Hq.
             apply in_seq in Hq.
             destruct (r_starts0 j Hj) as [Hsj _].
             replace (Nat.eqb (starts sh i + d) q) with false; [reflexivity|].
             symmetry. apply Nat.eqb_neq. intros Heq.
             destruct (Nat.lt_ge_cases j i) as [Hji | Hij].
             ++ assert (starts sh (S j) <= starts sh i)%nat by (apply Hle; lia).
                lia.
             ++ assert (starts sh (S i) <= starts sh j)%nat by (apply Hle; lia).
                lia.
    - (* the clauses past the last are still none *)
      intros j Hj. cbn [set_clause cmap]. rewrite tget_tset_other by lia. now apply Hnone.
  Qed.

  (* Setting clause i to the literals it has keeps the representation. *)
  Lemma rep_clause_same: forall (m: mem) (i: nat) (ls: list Lit),
    RepL m sh N lss x -> tget (cmap x) i = Some ls ->
      RepL m sh N lss (set_clause x i ls).
  Proof.
    intros m i ls HRep Hls.
    assert (Hsame: forall (j: nat), tget (tset (cmap x) i (Some ls)) j = tget (cmap x) j).
    { intros j. rewrite tget_tset. destruct (Nat.eq_dec i j) as [<- | Hne].
      - now rewrite Hls.
      - reflexivity. }
    destruct HRep as [[] [] []]. constructor; constructor; try assumption; try repack.
    - destruct a_lits0 as (t & At & Hatoms & Hcl). exists t. split.
      + assumption.
      + split.
        * assumption.
        * intros j Hj. cbn [set_clause cmap]. rewrite Hsame. now apply Hcl.
    - intros j Hj. cbn [set_clause cmap]. rewrite Hsame. now apply r_cmap0.
  Qed.

  (* Setting clause i twice is setting it to the second literals. *)
  Lemma rep_clause_twice: forall (m: mem) (i: nat) (ls1 ls2: list Lit),
    RepL m sh N lss (set_clause (set_clause x i ls1) i ls2) ->
    RepL m sh N lss (set_clause x i ls2).
  Proof.
    intros m i ls1 ls2 HRep.
    assert (Hsame: forall (j: nat),
      tget (tset (tset (cmap x) i (Some ls1)) i (Some ls2)) j =
      tget (tset (cmap x) i (Some ls2)) j).
    { intros j. rewrite !tget_tset. now destruct (Nat.eq_dec i j). }
    destruct HRep as [[] [] []]. constructor; constructor; try assumption; try repack.
    - destruct a_lits0 as (t & At & Hatoms & Hcl). exists t. split.
      + assumption.
      + split.
        * assumption.
        * intros j Hj. cbn [set_clause cmap]. rewrite <- Hsame. now apply Hcl.
    - intros j Hj. cbn [set_clause cmap]. rewrite <- Hsame. now apply r_cmap0.
  Qed.

  (* Setting the short clauses to ss, which the array of short clauses tsh holds (newest
     last): s->nshorts = length ss. *)
  Lemma rep_store_shorts: forall (m m': mem) (ss: list nat) (tsh: nat -> Z),
    RepL m sh N lss x -> Arr m (b_shorts sh) (length lss) tsh ->
    StackIn tsh ss ->
    (length ss <= length lss)%nat -> (forall (i: nat), In i ss -> (i < length lss)%nat) ->
    Mem.store Mint32 m (b_s sh) o_nshorts (vnat (length ss)) = Some m' ->
    RepL m' sh N lss (x <| shorts := ss |>).
  Proof.
    intros m m' ss tsh HRep Ash Htsh Hle Hcls Hst.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (fld_store (r_nshorts HRep) Hst) as Fns.
    cbn [Val.load_result] in Fns. destruct HRep as [[] [] []]. carry Hst Hnd.
    (* Every field is as before, but the short clauses, which the hypotheses describe. *)
    constructor; constructor; try assumption; try repack.
  Qed.

  (* A store to the array of short clauses while the context has none. *)
  Lemma rep_store_short_entry: forall (m m': mem) (ts: nat -> Z) (k: nat) (z: Z),
    RepL m sh N lss x -> shorts x = [] -> Arr m (b_shorts sh) (length lss) ts ->
    (k < length lss)%nat ->
    Mem.store Mint32 m (b_shorts sh) (4 * Z.of_nat k) (vint z) = Some m' ->
    RepL m' sh N lss x.
  Proof.
    intros m m' ts k z HRep Hsh Ats Hk Hst.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (arr_store Ats Hk Hst) as Ats'.
    destruct HRep as [[] [] []]. carry Hst Hnd.
    (* Every field is as before; there are still no short clauses. *)
    constructor; constructor; try assumption; try repack.
    - exists (fun (j: nat) => if Nat.eqb k j then z else ts j). split.
      + assumption.
      + intros q Hq. rewrite Hsh in Hq. cbn [length] in Hq. lia.
  Qed.

  (* Storing the phase o of atom a: s->phs[a] = enc_value o. *)
  Lemma rep_store_phs: forall (m m': mem) (a: nat) (o: option bool),
    RepL m sh N lss x -> (a < N)%nat ->
    Mem.store Mint32 m (b_phs sh) (4 * Z.of_nat a) (vint (enc_value o)) = Some m' ->
    RepL m' sh N lss (x <| phs := tset (phs x) a o |>).
  Proof.
    intros m m' a o HRep Ha Hst.
    pose proof (r_nodup HRep) as Hnd.
    pose proof (arr_store (a_phs HRep) Ha Hst) as Aphs.
    destruct HRep as [[] [] []]. carry Hst Hnd.
    (* Every field but the phases is as before. *)
    constructor; constructor; try assumption; try repack.
    - (* the phases: atom a now has the phase o *)
      cbn [set_phs phs]. arr_tset.
  Qed.

End Stores.

(* Opening a decision level at cursor c: the cursor moves to c (rep_store_cur), and the
   level opens there (rep_store_open_cur).
   s->cur = c; s->saved[s->dl] = c; s->lims[s->dl] = s->tlen; s->dl = s->dl + 1. *)
Lemma rep_store_open {sh: Shape} {N: nat} {lss: list (list Lit)} {x: Ctx}:
  forall (m m1 m2 m3 m4: mem) (c: nat),
  RepL m sh N lss x -> (c <= nlits x)%nat -> (length (lims x) < N)%nat ->
  Mem.store Mint32 m (b_s sh) o_cur (vnat c) = Some m1 ->
  Mem.store Mint32 m1 (b_saved sh) (4 * Z.of_nat (length (lims x))) (vnat c) =
    Some m2 ->
  Mem.store Mint32 m2 (b_lims sh) (4 * Z.of_nat (length (lims x)))
    (vnat (tlen x)) = Some m3 ->
  Mem.store Mint32 m3 (b_s sh) o_dl (vnat (S (length (lims x)))) =
    Some m4 ->
  RepL m4 sh N lss (open_level x c).
Proof.
  intros m m1 m2 m3 m4 c HRep Hc Hroom Hst1 Hst2 Hst3 Hst4.
  pose proof (rep_store_cur m m1 c HRep Hc Hst1) as HRep1.
  apply (rep_store_open_cur m1 m2 m3 m4 (x := x <| cur := c |>)); assumption.
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

(* The key of a literal with an atom below N < 2^28 is below 2^29. *)
Lemma key_small: forall (l: Lit) (N: nat), (extract l < N)%nat ->
  Z.of_nat N < atom_bound -> 0 <= key l < key_bound.
Proof. intros l N Hl HN. unfold key. destruct l; simpl in *; lia. Qed.

(* The key of a literal with an atom below N is below 2 N. *)
Lemma lit_key_lt: forall (l: Lit) (N: nat), (extract l < N)%nat ->
  (lit_key l < 2 * N)%nat.
Proof. intros [p|p] N Hl; cbn [lit_key extract] in *; lia. Qed.

(* Comparisons C makes on the value of a literal: with 0 (undefined), 1 (true) and -1
   (not false). *)
Lemma enc_undef: forall (v: Values) (l: Lit),
  Z.eqb (enc_value (lookup v l)) 0 = lookup_undef v l.
Proof. intros v l. unfold lookup_undef. now destruct (lookup v l) as [[|]|]. Qed.

Lemma enc_true: forall (v: Values) (l: Lit),
  Z.eqb (enc_value (lookup v l)) 1 = lookup_true v l.
Proof. intros v l. unfold lookup_true. now destruct (lookup v l) as [[|]|]. Qed.

Lemma enc_not_false: forall (v: Values) (l: Lit),
  negb (Z.eqb (enc_value (lookup v l)) (-1)) = not_false v l.
Proof. intros v l. unfold not_false. now destruct (lookup v l) as [[|]|]. Qed.

(* Values are small ints. *)
Lemma enc_small: forall (o: option bool), Small (enc_value o).
Proof. intros o. destruct o as [[|]|]; simpl; lia. Qed.

(* A count or none, as C returns it. *)
Definition enc_count (o: option nat): Z :=
match o with
| Some n => Z.of_nat n
| None   => -1
end.

(* The literals of the clauses of x have atoms below N. *)
Lemma clause_atoms: forall (m: mem) (sh: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (i: nat) (ls: list Lit) (l: Lit),
  RepL m sh N lss x -> tget (cmap x) i = Some ls -> In l ls -> (extract l < N)%nat.
Proof.
  intros m sh N lss x i ls l HRep Hi Hl.
  destruct (a_lits HRep) as (t & _ & Hatoms & Hcl).
  destruct (Nat.lt_ge_cases i (length lss)) as [Hlt | Hge].
  - rewrite (Hcl i Hlt) in Hi. injection Hi as <-. apply in_map_iff in Hl as [q [<- Hq]].
    apply in_seq in Hq. destruct (r_starts HRep i Hlt) as [_ Hle].
    destruct (Hatoms q) as [l0 [-> Hl0]].
    + lia.
    + now rewrite lit_of_key.
  - rewrite (r_cmap HRep i Hge) in Hi. discriminate.
Qed.

(* Literal d of clause i is the key at position starts i + d of block clits. *)
Lemma clause_lit: forall (m: mem) (sh: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (t: nat -> Z) (i d: nat) (cls: list Lit),
  RepL m sh N lss x -> ClausesIn sh N (length lss) t (cmap x) -> (i < length lss)%nat ->
  tget (cmap x) i = Some cls -> (d < length cls)%nat ->
  (starts sh i + d < nclits sh)%nat /\
  t (starts sh i + d)%nat = key (nth d cls (Pos 0%nat)) /\
  (extract (nth d cls (Pos 0%nat)) < N)%nat.
Proof.
  intros m sh N lss x t i d cls HRep [Hatoms Hcl] Hi Hcls Hd.
  destruct (r_starts HRep i Hi) as [Hsi Hsn].
  rewrite (Hcl i Hi) in Hcls. injection Hcls as <-.
  rewrite length_map, length_seq in Hd.
  assert (Hq: (starts sh i + d < nclits sh)%nat) by lia.
  destruct (Hatoms (starts sh i + d)%nat Hq) as [l [Hl Hla]].
  assert (Hnth: nth d (map (fun (q: nat) => lit_of (t q)) (clause_range sh i))
                  (Pos 0%nat) = l).
  - rewrite nth_indep with (d' := lit_of (t 0%nat)) by
      (rewrite length_map, length_seq; lia).
    pose proof (map_nth (fun (q: nat) => lit_of (t q)) (clause_range sh i) 0%nat d)
      as Hmap.
    cbv beta in Hmap. rewrite Hmap, seq_nth by lia. rewrite Hl. apply lit_of_key.
  - rewrite Hnth. split.
    + assumption.
    + split; assumption.
Qed.

(* The length of clause i is the length of its range. *)
Lemma clause_length: forall (sh: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (t: nat -> Z) (i: nat) (cls: list Lit),
  ClausesIn sh N (length lss) t (cmap x) -> (i < length lss)%nat ->
  tget (cmap x) i = Some cls ->
  length cls = (starts sh (S i) - starts sh i)%nat.
Proof.
  intros sh N lss x t i cls [_ Hcl] Hi Hcls. rewrite (Hcl i Hi) in Hcls.
  injection Hcls as <-. now rewrite length_map, length_seq.
Qed.

(* C compares literals by their keys. *)
Lemma key_eqb: forall (a b: Lit), Z.eqb (key a) (key b) = (a =? b).
Proof.
  intros a b. destruct (a =? b) eqn:Hab.
  - apply Lit.eqb_eq in Hab as ->. apply Z.eqb_refl.
  - apply Lit.eqb_neq in Hab. apply Z.eqb_neq. intros Hk. apply Hab. apply lit_key_inj.
    unfold key in Hk. lia.
Qed.

(* The trail of the solver in memory holds the assignment pm: its length (field tlen,
   at 80), and its literals oldest first. *)
Definition TrailIn (m: mem) (sh: Shape) (N: nat) (pm: PA): Prop :=
  Fld m (b_s sh) o_tlen Mint32 (vnat (PA.length pm)) /\
  exists (t: nat -> Z), Arr m (b_tr sh) N t /\
    forall (j: nat), (j < PA.length pm)%nat ->
      t j = key (nth j (trail_lits pm) (Pos 0%nat)).
