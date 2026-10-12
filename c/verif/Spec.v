(* The specification of the C solver (../solver.c) with VST: its state represents a context of
   verification/refinement/Step.v, and solve gives a correct answer. Work in progress: the bodies are not proved
   yet (Admitted below); see README.md for the plan. *)
From RocqSAT Require Import Lit.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import State.
From RocqSAT Require Import Model.
From RocqSAT Require Import Satisfiability.
From RocqSAT Require Import Trans.
From RocqSAT.systems Require Import DPLL_BJ.
From RocqSAT.refinement Require Import Table Lookup Watches Propagate Step CStep.
From VST Require Import floyd.proofauto.
From RocqSATClight Require Import solver.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Section Encoding.
  (* Values of atoms and literals: 1 true, -1 false, 0 unassigned. *)
  Definition enc_value (b: option bool): Z :=
  match b with
  | Some true  => 1
  | Some false => -1
  | None       => 0
  end.

  Definition enc_bool (b: bool): Z := if b then 1 else 0.

  (* A literal as its key. *)
  Definition key (l: Lit): Z := Z.of_nat (lit_key l).

  Definition vint (z: Z): val := Vint (Int.repr z).

  (* The first n entries of a table as an array. *)
  Definition table_vals {A: Type} (enc: A -> Z) (t: Table A) (n: nat): list val :=
  map (fun (k: nat) => vint (enc (tget t k))) (seq 0 n).

  (* Setting key k changes entry k of the encoded segment. *)
  Lemma map_seq_tset: forall {A: Type} (enc: A -> Z) (t: Table A) (k: nat) (a: A) (n s: nat), (s <= k < s + n)%nat ->
    map (fun (j: nat) => vint (enc (tget (tset t k a) j))) (seq s n) =
    upd_Znth (Z.of_nat (k - s)) (map (fun (j: nat) => vint (enc (tget t j))) (seq s n)) (vint (enc a)).
  Proof.
    intros A enc t k a n. induction n as [|n IH]; intros s Hk.
    - lia.
    - simpl. destruct (Nat.eq_dec k s) as [->|Hneq].
      + rewrite Nat.sub_diag. simpl. rewrite upd_Znth0, tget_tset_same. f_equal. apply map_ext_in. intros j Hj.
        apply in_seq in Hj. rewrite tget_tset_other by lia. reflexivity.
      + rewrite upd_Znth_cons by lia. rewrite tget_tset_other by lia. f_equal.
        replace (Z.of_nat (k - s) - 1) with (Z.of_nat (k - S s)) by lia. apply IH. lia.
  Qed.

  Lemma table_vals_tset: forall {A: Type} (enc: A -> Z) (t: Table A) (k: nat) (a: A) (n: nat), (k < n)%nat ->
    table_vals enc (tset t k a) n = upd_Znth (Z.of_nat k) (table_vals enc t n) (vint (enc a)).
  Proof. intros A enc t k a n Hk. unfold table_vals. rewrite map_seq_tset by lia. now rewrite Nat.sub_0_r. Qed.

  (* The atom of a literal key is the key shifted right by one, and its lowest bit tells its sign. *)
  Lemma shr_key: forall (l: Lit), key l <= Int.max_signed ->
    Int.shr (Int.repr (key l)) (Int.repr 1) = Int.repr (Z.of_nat (extract l)).
  Proof.
    intros l Hl. unfold key in *. unfold Int.shr. rewrite Int.signed_repr by rep_lia.
    rewrite Int.unsigned_repr by rep_lia. rewrite Z.shiftr_div_pow2, Z.pow_1_r by lia. f_equal.
    destruct l as [p|p]; cbn [lit_key extract] in *.
    - symmetry. apply Z.div_unique with 0; lia.
    - symmetry. apply Z.div_unique with 1; lia.
  Qed.

  Lemma land_key: forall (l: Lit), Z.land (key l) 1 = if is_pos l then 0 else 1.
  Proof.
    intros l. unfold key. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia.
    destruct l as [p|p]; cbn [lit_key is_pos].
    - symmetry. apply Z.mod_unique with (Z.of_nat p); lia.
    - symmetry. apply Z.mod_unique with (Z.of_nat p); lia.
  Qed.
End Encoding.

(* The facts about a context that the C code needs for memory safety and for its ints, for N atoms and the clauses
   lss; lims are the trail positions of the decisions, newest first. *)
Record Shape (N: nat) (lss: list (list Lit)) (x: Ctx) (lims: list nat): Prop := {
  sh_n: (1 <= N < 268435456)%nat;
  sh_ncl: (length lss < 268435456)%nat;
  sh_cmap: forall (i: nat), tget (cmap x) i = nth_error lss i;
  sh_lits: forall (ls: list Lit) (l: Lit), In ls lss -> In l ls -> (extract l < N)%nat;
  sh_wat: forall (i: nat), (i < length lss)%nat ->
    (extract (fst (tget (wat x) i)) < N)%nat /\ (extract (snd (tget (wat x) i)) < N)%nat;
  sh_wls: forall (k i: nat), (k < 2 * N)%nat -> In i (tget (wls x) k) -> (i < length lss)%nat;
  sh_tlen: (qhead x <= tlen x <= N)%nat;
  sh_tr: forall (j: nat), (j < N)%nat -> (extract (tget (tr x) j) < N)%nat;
  sh_shorts: forall (i: nat), In i (shorts x) -> (i < length lss)%nat;
  sh_alls: (cur x <= nlits x <= 2 * N)%nat /\ forall (j: nat), (j < nlits x)%nat -> (extract (tget (alls x) j) < N)%nat;
  sh_saved: length (saved x) = dl x /\ forall (c: nat), In c (saved x) -> (c <= nlits x)%nat;
  sh_lims: length lims = dl x /\ forall (j: nat), In j lims -> (j < tlen x)%nat;
  sh_rsn: forall (a: nat), (a < N)%nat -> (tget (rsn x) a <= length lss)%nat;
  sh_lvl: forall (a: nat), (a < N)%nat -> (tget (lvl x) a <= N)%nat;
  sh_nvars: nvars x = N
}.

Definition t_solver := Tstruct _solver noattr.

(* The offsets of the clauses lss from o on, and their literals. *)
Fixpoint offsets (o: Z) (lss: list (list Lit)): list Z :=
match lss with
| []        => [o]
| ls :: lss' => o :: offsets (o + Zlength ls) lss'
end.

(* The prefix sums of the room of the watch lists. *)
Fixpoint prefix_sums (o: Z) (caps: list Z): list Z :=
match caps with
| []         => []
| c :: caps' => o :: prefix_sums (o + c) caps'
end.

(* The C state at s represents the context x with N atoms and clauses lss, the decision positions lims, and the
   learnt clause c of an analysis. The arrays hold the tables up to their sizes; the watch lists are segments of
   one pool, and the stacks hold their entries oldest first. *)
Definition solver_rep (N: nat) (lss: list (list Lit)) (x: Ctx) (lims: list nat) (c: list Lit) (s: val): mpred :=
  let n := Z.of_nat N in
  let C := Zlength lss in
  EX ps: list val, EX lcap: Z, EX clits: list val, EX room: Z, EX caps: list Z, EX pool: list val,
  EX sh: list val, EX sv: list val, EX lm: list val, EX al: list val, EX lt: list val,
  !! (Shape N lss x lims /\ Zlength ps = 19 /\
      sublist 0 (Zlength (concat lss)) clits = map (fun (l: Lit) => vint (key l)) (concat lss) /\
      Zlength clits = lcap /\ Zlength pool = room /\ Zlength caps = (2 * n)%Z /\ fold_right Z.add 0 caps <= room /\
      (forall (k: nat), (k < 2 * N)%nat ->
        Zlength (tget (wls x) k) <= Znth (Z.of_nat k) caps /\
        sublist (Znth (Z.of_nat k) (prefix_sums 0 caps)) (Znth (Z.of_nat k) (prefix_sums 0 caps) +
          Zlength (tget (wls x) k)) pool = map (fun (i: nat) => vint (Z.of_nat i)) (tget (wls x) k)) /\
      Zlength sh = C /\ sublist 0 (Zlength (shorts x)) sh = map (fun (i: nat) => vint (Z.of_nat i)) (rev (shorts x)) /\
      Zlength sv = n /\ sublist 0 (Z.of_nat (dl x)) sv = map (fun (k: nat) => vint (Z.of_nat k)) (rev (saved x)) /\
      Zlength lm = n /\ sublist 0 (Z.of_nat (dl x)) lm = map (fun (k: nat) => vint (Z.of_nat k)) (rev lims) /\
      Zlength al = (2 * n)%Z /\ sublist 0 (Z.of_nat (nlits x)) al = table_vals key (alls x) (nlits x) /\
      Zlength lt = (2 * n)%Z /\ Zlength c <= (2 * n)%Z /\ sublist 0 (Zlength c) lt = map (fun (l: Lit) => vint (key l)) (rev c)) &&
  (data_at Ews t_solver
    (vint n, (vint C, (Znth 0 ps, (Znth 1 ps, (Znth 2 ps, (Znth 3 ps, (Znth 4 ps, (Znth 5 ps, (Znth 6 ps,
    (Znth 7 ps, (Znth 8 ps, (Znth 9 ps, (vint (Z.of_nat (tlen x)), (vint (Z.of_nat (qhead x)), (Znth 10 ps,
    (vint (Zlength (shorts x)), (Znth 11 ps, (vint (Z.of_nat (nlits x)), (vint (Z.of_nat (cur x)), (Znth 12 ps,
    (Znth 13 ps, (vint (Z.of_nat (dl x)), (Znth 14 ps, (Znth 15 ps, (Znth 16 ps, (Znth 17 ps, (Znth 18 ps,
    vint (Zlength c)))))))))))))))))))))))))))) s *
  data_at Ews (tarray tint (C + 1)%Z) (map vint (offsets 0 lss)) (Znth 0 ps) *
  data_at Ews (tarray tint lcap) clits (Znth 1 ps) *
  data_at Ews (tarray tint n) (table_vals enc_value (vals x) N) (Znth 2 ps) *
  data_at Ews (tarray tint C) (map (fun (i: nat) => vint (key (fst (tget (wat x) i)))) (seq 0 (length lss))) (Znth 3 ps) *
  data_at Ews (tarray tint C) (map (fun (i: nat) => vint (key (snd (tget (wat x) i)))) (seq 0 (length lss))) (Znth 4 ps) *
  data_at Ews (tarray tint room) pool (Znth 5 ps) *
  data_at Ews (tarray tint (2 * n)%Z) (map vint (prefix_sums 0 caps)) (Znth 6 ps) *
  data_at Ews (tarray tint (2 * n)%Z) (table_vals (fun (ws: list nat) => Zlength ws) (wls x) (2 * N)%nat) (Znth 7 ps) *
  data_at Ews (tarray tint (2 * n)%Z) (map vint caps) (Znth 8 ps) *
  data_at Ews (tarray tint n) (table_vals key (tr x) N) (Znth 9 ps) *
  data_at Ews (tarray tint C) sh (Znth 10 ps) *
  data_at Ews (tarray tint (2 * n)%Z) al (Znth 11 ps) *
  data_at Ews (tarray tint n) sv (Znth 12 ps) *
  data_at Ews (tarray tint n) lm (Znth 13 ps) *
  data_at Ews (tarray tint n) (table_vals Z.of_nat (rsn x) N) (Znth 14 ps) *
  data_at Ews (tarray tint n) (table_vals Z.of_nat (lvl x) N) (Znth 15 ps) *
  data_at Ews (tarray tint (2 * n)%Z) (table_vals enc_bool (mrk x) (2 * N)%nat) (Znth 16 ps) *
  data_at Ews (tarray tint n) (table_vals enc_value (phs x) N) (Znth 17 ps) *
  data_at Ews (tarray tint (2 * n)%Z) lt (Znth 18 ps))%logic.

(* Assigning a literal: 0 if the trail is full, otherwise the C state represents assign x l r. *)
Definition assign_spec :=
 DECLARE _assign
 WITH s: val, N: nat, lss: list (list Lit), x: Ctx, lims: list nat, c: list Lit, l: Lit, r: nat
 PRE [tptr t_solver, tint, tint]
   PROP ((extract l < N)%nat; (r <= length lss)%nat)
   PARAMS (s; vint (key l); vint (Z.of_nat r))
   SEP (solver_rep N lss x lims c s)
 POST [tint]
   EX ok: bool,
   PROP (ok = false -> tlen x = N)
   RETURN (vint (enc_bool ok))
   SEP (solver_rep N lss (if ok then assign x l r else x) lims c s).

(* The answer of solve, from a context consistent with a reachable state of f: UNSAT only if f is unsatisfiable,
   SAT only with a model of f on the trail, and 2 if it ran out of room. *)
Definition solve_spec :=
 DECLARE _solve
 WITH s: val, N: nat, lss: list (list Lit), x: Ctx, lims: list nat, c: list Lit, m: PA, f: CNF
 PRE [tptr t_solver]
   PROP (StepInv (State.state m f) x; LimsOf lims m; State.state ⟨⟩ f ==>*[DPLL_BJ] State.state m f)
   PARAMS (s)
   SEP (solver_rep N lss x lims c s)
 POST [tint]
   EX r: Z, EX x': Ctx, EX lims': list nat, EX c': list Lit, EX m': PA,
   PROP ((r = 0 -> Unsat f) /\ (r = 1 -> Model m' f /\ TrailOf (tr x') (tlen x') m') /\ 0 <= r <= 2)
   RETURN (vint r)
   SEP (if Z.eq_dec r 2 then emp else solver_rep N lss x' lims' c' s).

Definition Gprog := [assign_spec; solve_spec].

Lemma body_assign: semax_body Vprog Gprog f_assign assign_spec.
Proof.
Admitted.

Lemma body_solve: semax_body Vprog Gprog f_solve solve_spec.
Proof.
Admitted.
