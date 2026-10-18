(* Tables from natural numbers to values, as a model: a table is a function, and setting a key builds a new
   function. The C solver keeps its tables in arrays; refinement/c/Rep.v says how the arrays hold them. *)
From Stdlib Require Import Arith.

(* A table: the value of every key. *)
Definition Table (A: Type): Type := nat -> A.

(* The value of key k. *)
Definition tget {A: Type} (t: Table A) (k: nat): A := t k.

(* t with the value of key k set to a. *)
Definition tset {A: Type} (t: Table A) (k: nat) (a: A): Table A :=
fun (k': nat) => if Nat.eqb k k' then a else t k'.

(* A table in which every key has value d. *)
Definition tmake {A: Type} (d: A): Table A := fun (_: nat) => d.

(* Keep simpl from unfolding the model, so that goals stay stated with the table operations. *)
Arguments tget : simpl never.
Arguments tset : simpl never.
Arguments tmake : simpl never.

(* Setting key k and reading it gives the new value. *)
Lemma tget_tset_same: forall {A: Type} (t: Table A) (k: nat) (a: A), tget (tset t k a) k = a.
Proof. intros A t k a. unfold tget, tset. now rewrite Nat.eqb_refl. Qed.

(* Setting key k leaves the other keys. *)
Lemma tget_tset_other: forall {A: Type} (t: Table A) (k k': nat) (a: A),
  k <> k' -> tget (tset t k a) k' = tget t k'.
Proof. intros A t k k' a Hneq. unfold tget, tset. apply Nat.eqb_neq in Hneq. now rewrite Hneq. Qed.

(* Every key of tmake d has value d. *)
Lemma tget_tmake: forall {A: Type} (k: nat) (d: A), tget (tmake d) k = d.
Proof. reflexivity. Qed.

(* Reading a set table, by cases on the key. *)
Lemma tget_tset: forall {A: Type} (t: Table A) (k k': nat) (a: A),
  tget (tset t k a) k' = if Nat.eq_dec k k' then a else tget t k'.
Proof.
  intros A t k k' a. destruct (Nat.eq_dec k k') as [<-|Hneq].
  - apply tget_tset_same.
  - now apply tget_tset_other.
Qed.
