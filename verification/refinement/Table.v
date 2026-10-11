(* Tables from natural numbers to values, backed by a primitive array (PArray) for constant-time access.

   NOTE: primitive arrays and 63-bit integers are only specified by axioms (Corelib's ArrayAxioms and
   Uint63Axioms), so every result that depends on this file depends on those axioms. Keys that do not fit in
   the array are kept in an AVL map instead, so a table is correct for every key. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Uint63.
From Stdlib Require Import PArray.
From Stdlib Require Import Structures.OrderedTypeEx.
From Stdlib Require Import FSets.FMapAVL.
From Stdlib Require Import FSets.FMapFacts.

(* Finite maps from natural numbers. *)
Module AtomMap := FMapAVL.Make(Nat_as_OT).
Module AtomMapFacts := FMapFacts.WFacts_fun(Nat_as_OT)(AtomMap).

Local Open Scope uint63_scope.

(* The machine integer for n. It is extracted to Uint63.of_int, so it takes constant time when run. *)
Definition nat_index (n: nat): int := of_Z (Z.of_nat n).

(* A table: an array for the keys below bound (which fits in the array), and a map for all other keys. *)
Record Table (A: Type): Type := mkTable {
  tarr: array A;
  tspill: AtomMap.t A;
  tbound: nat;
  tbound_ok: (Z.of_nat tbound <= φ max_length)%Z;
  tbound_len: (Z.of_nat tbound <= φ (PrimArray.length tarr))%Z
}.

Arguments mkTable {A}.
Arguments tarr {A}.
Arguments tspill {A}.
Arguments tbound {A}.
Arguments tbound_ok {A}.
Arguments tbound_len {A}.

(* Whether key k is stored in the array of t. Only the bound is compared, since asking the array for its
   length costs as much as a lookup. *)
Definition in_array {A: Type} (t: Table A) (k: nat): bool := Nat.ltb k (tbound t).

(* The value of key k, or the default of the table. *)
Definition tget {A: Type} (t: Table A) (k: nat): A :=
if in_array t k then (tarr t).[nat_index k]
else match AtomMap.find k (tspill t) with
     | Some a => a
     | None   => PrimArray.default (tarr t)
     end.

(* Setting a value in the array keeps its length. *)
Lemma tbound_len_set: forall {A: Type} (t: Table A) (i: int) (a: A),
  (Z.of_nat (tbound t) <= φ (PrimArray.length (tarr t).[i <- a]))%Z.
Proof. intros A t i a. rewrite length_set. apply tbound_len. Qed.

(* t with the value of key k set to a. *)
Definition tset {A: Type} (t: Table A) (k: nat) (a: A): Table A :=
if in_array t k then mkTable (tarr t).[nat_index k <- a] (tspill t) (tbound t) (tbound_ok t) (tbound_len_set t _ a)
else mkTable (tarr t) (AtomMap.add k a (tspill t)) (tbound t) (tbound_ok t) (tbound_len t).

(* The largest array length, as a natural number. *)
Definition max_length_nat: nat := Z.to_nat (φ max_length).

Lemma min_max_length_ok: forall (n: nat), (Z.of_nat (Nat.min n max_length_nat) <= φ max_length)%Z.
Proof.
  intros n. unfold max_length_nat. destruct (to_Z_bounded max_length) as [Hpos _]. lia.
Qed.

(* Keys stored in the array are converted exactly. *)
Lemma nat_index_spec: forall (n: nat), (Z.of_nat n <= φ max_length)%Z -> φ (nat_index n) = Z.of_nat n.
Proof.
  intros n Hn. unfold nat_index. rewrite of_Z_spec. apply Z.mod_small.
  destruct (to_Z_bounded max_length). lia.
Qed.

(* A new array for the keys below n has room for them, as far as an array can. *)
Lemma min_max_length_len: forall {A: Type} (n: nat) (d: A),
  let m := Nat.min n max_length_nat in (Z.of_nat m <= φ (PrimArray.length (PrimArray.make (nat_index m) d)))%Z.
Proof.
  intros A n d m. rewrite length_make. assert (Hm: φ (nat_index m) = Z.of_nat m).
  - apply nat_index_spec. apply min_max_length_ok.
  - destruct (nat_index m ≤? max_length) eqn:Hle.
    + lia.
    + exfalso. apply not_true_iff_false in Hle. apply Hle. apply leb_spec. rewrite Hm. apply min_max_length_ok.
Qed.

(* A table in which every key has value d, with an array for the keys below n where possible. *)
Definition tmake {A: Type} (n: nat) (d: A): Table A :=
mkTable (PrimArray.make (nat_index (Nat.min n max_length_nat)) d) (AtomMap.empty A) (Nat.min n max_length_nat)
  (min_max_length_ok n) (min_max_length_len n d).

Lemma in_array_bound: forall {A: Type} (t: Table A) (k: nat), in_array t k = true -> (Z.of_nat k <= φ max_length)%Z.
Proof.
  intros A t k Hin. unfold in_array in Hin. apply Nat.ltb_lt in Hin. pose proof (tbound_ok t). lia.
Qed.

(* Keys stored in the array are within its length. *)
Lemma in_array_lt: forall {A: Type} (t: Table A) (k: nat),
  in_array t k = true -> (nat_index k <? PrimArray.length (tarr t)) = true.
Proof.
  intros A t k Hin. apply ltb_spec. rewrite nat_index_spec.
  - unfold in_array in Hin. apply Nat.ltb_lt in Hin. pose proof (tbound_len t). lia.
  - now apply (in_array_bound t).
Qed.

Lemma nat_index_inj: forall {A: Type} (t: Table A) (k k': nat),
  in_array t k = true -> in_array t k' = true -> nat_index k = nat_index k' -> k = k'.
Proof.
  intros A t k k' Hk Hk' Heq. apply in_array_bound in Hk, Hk'. apply (f_equal to_Z) in Heq.
  rewrite !nat_index_spec in Heq.
  - lia.
  - assumption.
  - assumption.
Qed.

(* Setting a key does not change which keys are stored in the array. *)
Lemma in_array_tset: forall {A: Type} (t: Table A) (k k': nat) (a: A), in_array (tset t k a) k' = in_array t k'.
Proof.
  intros A t k k' a. unfold tset. destruct (in_array t k).
  - reflexivity.
  - reflexivity.
Qed.

Lemma tget_tset_same: forall {A: Type} (t: Table A) (k: nat) (a: A), tget (tset t k a) k = a.
Proof.
  intros A t k a. unfold tget. rewrite in_array_tset. unfold tset. destruct (in_array t k) eqn:Hin.
  - simpl. apply get_set_same. now apply in_array_lt.
  - simpl. now rewrite AtomMapFacts.add_eq_o.
Qed.

Lemma tget_tset_other: forall {A: Type} (t: Table A) (k k': nat) (a: A), k <> k' -> tget (tset t k a) k' = tget t k'.
Proof.
  intros A t k k' a Hneq. unfold tget. rewrite in_array_tset. unfold tset.
  destruct (in_array t k) eqn:Hin, (in_array t k') eqn:Hin'; simpl.
  - apply get_set_other. intros Heq. apply Hneq. now apply (nat_index_inj t).
  - now rewrite default_set.
  - reflexivity.
  - now rewrite AtomMapFacts.add_neq_o.
Qed.

Lemma tget_tmake: forall {A: Type} (n k: nat) (d: A), tget (tmake n d) k = d.
Proof.
  intros A n k d. unfold tget. destruct (in_array (tmake n d) k).
  - apply get_make.
  - simpl. apply default_make.
Qed.

Lemma tget_tset: forall {A: Type} (t: Table A) (k k': nat) (a: A),
  tget (tset t k a) k' = if Nat.eq_dec k k' then a else tget t k'.
Proof.
  intros A t k k' a. destruct (Nat.eq_dec k k') as [<-|Hneq].
  - apply tget_tset_same.
  - now apply tget_tset_other.
Qed.
