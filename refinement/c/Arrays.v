(* Arrays of ints and struct fields in CompCert memory, as tables: Arr m b n t says that
   block b holds the ints t k for k below n, writable. Every table of the solver has a
   block of its own, so a store to one leaves the others unchanged without any
   separation logic.

   The bounds are powers of two: indices and small ints are below 2^30 = 1073741824, so
   that sums of two of them fit in a signed 32-bit int (2^31 = 2147483648); pointer
   offsets are 64-bit (2^64 = 18446744073709551616). *)
From compcert Require Import Coqlib Integers Values Memory AST.

(* The value of int z. *)
Definition vint (z: Z): val := Vint (Int.repr z).

(* Block b holds the n ints t 0 .. t (n - 1). *)
Definition Arr (m: mem) (b: block) (n: nat) (t: nat -> Z): Prop :=
  forall (k: nat), (k < n)%nat ->
    Mem.valid_access m Mint32 b (4 * Z.of_nat k) Writable /\
    Mem.load Mint32 m b (4 * Z.of_nat k) = Some (vint (t k)).

(* Block b holds value v of chunk at offset ofs, writable. *)
Definition Fld (m: mem) (b: block) (ofs: Z) (chunk: memory_chunk) (v: val): Prop :=
  Mem.valid_access m chunk b ofs Writable /\ Mem.load chunk m b ofs = Some v.

Section Lemmas.
  (* Arrays only depend on the entries below their size. *)
  Lemma arr_ext: forall (m: mem) (b: block) (n: nat) (t t': nat -> Z),
    Arr m b n t -> (forall (k: nat), (k < n)%nat -> t' k = t k) -> Arr m b n t'.
  Proof.
    intros m b n t t' Harr Hext k Hk. rewrite Hext by assumption. apply Harr. assumption.
  Qed.

  (* A store in another block, or to a disjoint range of the same block, keeps a field
     or an array. *)
  Lemma fld_store_other: forall (m m': mem) (b b': block) (ofs ofs': Z)
    (chunk chunk': memory_chunk) (v v': val),
    Fld m b ofs chunk v ->
    Mem.store chunk' m b' ofs' v' = Some m' ->
    b <> b' \/ ofs + size_chunk chunk <= ofs' \/ ofs' + size_chunk chunk' <= ofs ->
    Fld m' b ofs chunk v.
  Proof.
    intros m m' b b' ofs ofs' chunk chunk' v v' [Hvalid Hload] Hstore Hdisj. split.
    - apply (Mem.store_valid_access_1 _ _ _ _ _ _ Hstore). assumption.
    - rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore).
      + assumption.
      + destruct Hdisj as [Hne | [Hlt | Hlt]].
        * left. assumption.
        * right. left. assumption.
        * right. right. assumption.
  Qed.

  Lemma arr_store_other: forall (m m': mem) (b b': block) (n: nat) (t: nat -> Z)
    (ofs': Z) (chunk': memory_chunk) (v': val),
    Arr m b n t -> Mem.store chunk' m b' ofs' v' = Some m' -> b <> b' -> Arr m' b n t.
  Proof.
    intros m m' b b' n t ofs' chunk' v' Harr Hstore Hne k Hk.
    destruct (Harr k Hk) as [Hvalid Hload]. split.
    - apply (Mem.store_valid_access_1 _ _ _ _ _ _ Hstore). assumption.
    - rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore).
      + assumption.
      + left. assumption.
  Qed.

  (* A store to an entry of an array updates that entry. *)
  Lemma arr_store: forall (m m': mem) (b: block) (n k: nat) (t: nat -> Z) (z: Z),
    Arr m b n t -> (k < n)%nat ->
    Mem.store Mint32 m b (4 * Z.of_nat k) (vint z) = Some m' ->
    Arr m' b n (fun (j: nat) => if Nat.eqb k j then z else t j).
  Proof.
    intros m m' b n k t z Harr Hk Hstore j Hj.
    destruct (Harr j Hj) as [Hvalid Hload]. split.
    - apply (Mem.store_valid_access_1 _ _ _ _ _ _ Hstore). assumption.
    - destruct (Nat.eqb_spec k j) as [<- | Hne].
      + rewrite (Mem.load_store_same _ _ _ _ _ _ Hstore). reflexivity.
      + rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore).
        * assumption.
        * right. cbn [size_chunk]. lia.
  Qed.

  (* An entry of an array can be stored to. *)
  Lemma arr_storable: forall (m: mem) (b: block) (n k: nat) (t: nat -> Z) (z: Z),
    Arr m b n t -> (k < n)%nat ->
    exists (m': mem), Mem.store Mint32 m b (4 * Z.of_nat k) (vint z) = Some m'.
  Proof.
    intros m b n k t z Harr Hk. destruct (Harr k Hk) as [Hvalid _].
    destruct (Mem.valid_access_store _ _ _ _ (vint z) Hvalid) as [m' Hstore].
    exists m'. assumption.
  Qed.

  Lemma fld_storable: forall (m: mem) (b: block) (ofs: Z) (chunk: memory_chunk)
    (v w: val),
    Fld m b ofs chunk v -> exists (m': mem), Mem.store chunk m b ofs w = Some m'.
  Proof.
    intros m b ofs chunk v w [Hvalid _].
    destruct (Mem.valid_access_store _ _ _ _ w Hvalid) as [m' Hstore].
    exists m'. assumption.
  Qed.

  (* Storing a field. *)
  Lemma fld_store: forall (m m': mem) (b: block) (ofs: Z) (chunk: memory_chunk)
    (v w: val),
    Fld m b ofs chunk v -> Mem.store chunk m b ofs w = Some m' ->
    Fld m' b ofs chunk (Val.load_result chunk w).
  Proof.
    intros m m' b ofs chunk v w [Hvalid _] Hstore. split.
    - apply (Mem.store_valid_access_1 _ _ _ _ _ _ Hstore). assumption.
    - apply (Mem.load_store_same _ _ _ _ _ _ Hstore).
  Qed.
End Lemmas.

Section Access.
  (* The offset of entry k of an int array, as C computes it. *)
  Lemma index_ofs: forall (k: Z), 0 <= k < 2147483648 ->
    Ptrofs.unsigned
      (Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.repr k))))
    = 4 * k.
  Proof.
    intros k Hk.
    assert (Hmax: Ptrofs.max_unsigned = 18446744073709551615) by reflexivity.
    assert (Hint: Int.max_signed = 2147483647) by reflexivity.
    assert (Hmin: Int.min_signed = -2147483648) by reflexivity.
    unfold Ptrofs.of_ints. rewrite Int.signed_repr by lia. rewrite Ptrofs.add_zero_l.
    unfold Ptrofs.mul. rewrite (Ptrofs.unsigned_repr 4) by lia.
    rewrite (Ptrofs.unsigned_repr k) by lia. rewrite Ptrofs.unsigned_repr by lia.
    reflexivity.
  Qed.

  (* Reading a field or an array entry. *)
  Lemma fld_loadv: forall (m: mem) (b: block) (ofs: Z) (chunk: memory_chunk) (v: val)
    (p: ptrofs),
    Ptrofs.unsigned p = ofs -> Fld m b ofs chunk v ->
    ofs + size_chunk chunk <= Ptrofs.modulus ->
    Mem.loadv chunk m (Vptr b p) = Some v.
  Proof.
    intros m b ofs chunk v p Hp [_ Hload] Hbound. unfold Mem.loadv. rewrite Hp.
    destruct (zle _ _).
    - assumption.
    - lia.
  Qed.

  Lemma arr_loadv: forall (m: mem) (b: block) (n: nat) (t: nat -> Z) (k: nat),
    Arr m b n t -> (k < n)%nat -> Z.of_nat k < 2147483648 ->
    Mem.loadv Mint32 m
      (Vptr b (Ptrofs.add Ptrofs.zero
                 (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.repr (Z.of_nat k))))))
    = Some (vint (t k)).
  Proof.
    intros m b n t k Harr Hk Hsmall.
    assert (Hmod: Ptrofs.modulus = 18446744073709551616) by reflexivity.
    unfold Mem.loadv. rewrite index_ofs by lia. destruct (zle _ _).
    - apply Harr. assumption.
    - cbn [size_chunk] in *. lia.
  Qed.
End Access.

(* Comparisons of small ints. *)
Lemma lt_repr: forall (a b: Z), -1073741824 <= a < 1073741824 ->
  -1073741824 <= b < 1073741824 ->
  Int.lt (Int.repr a) (Int.repr b) = (a <? b).
Proof.
  intros a b Ha Hb. assert (Hint: Int.max_signed = 2147483647) by reflexivity.
  assert (Hmin: Int.min_signed = -2147483648) by reflexivity.
  unfold Int.lt. rewrite !Int.signed_repr by lia.
  destruct (zlt a b), (Z.ltb_spec a b); lia.
Qed.

(* Adding ints. *)
Lemma add_repr: forall (a b: Z), Int.add (Int.repr a) (Int.repr b) = Int.repr (a + b).
Proof.
  intros a b. unfold Int.add. apply Int.eqm_samerepr. apply Int.eqm_add.
  - apply Int.eqm_sym. apply Int.eqm_unsigned_repr.
  - apply Int.eqm_sym. apply Int.eqm_unsigned_repr.
Qed.

(* Adding small naturals, and adding 1, as C does for an index. *)
Lemma add_nat: forall (a b: nat), Z.of_nat a < 1073741824 -> Z.of_nat b < 1073741824 ->
  Int.add (Int.repr (Z.of_nat a)) (Int.repr (Z.of_nat b)) = Int.repr (Z.of_nat (a + b)).
Proof.
  intros a b Ha Hb. rewrite add_repr by lia. f_equal. lia.
Qed.

Lemma incr_nat: forall (a: nat), Z.of_nat a < 1073741824 ->
  Int.add (Int.repr (Z.of_nat a)) (Int.repr 1) = Int.repr (Z.of_nat (Datatypes.S a)).
Proof.
  intros a Ha. rewrite add_repr by lia. f_equal. lia.
Qed.

(* Subtracting ints. *)
Lemma sub_repr: forall (a b: Z), Int.sub (Int.repr a) (Int.repr b) = Int.repr (a - b).
Proof.
  intros a b. unfold Int.sub. apply Int.eqm_samerepr. apply Int.eqm_sub.
  - apply Int.eqm_sym. apply Int.eqm_unsigned_repr.
  - apply Int.eqm_sym. apply Int.eqm_unsigned_repr.
Qed.

(* An array holds its first entries as a smaller array. *)
Lemma arr_shrink: forall (m: mem) (b: block) (n n': nat) (t t': nat -> Z),
  Arr m b n t -> (n' <= n)%nat -> (forall (k: nat), (k < n')%nat -> t' k = t k) ->
  Arr m b n' t'.
Proof.
  intros m b n n' t t' Harr Hn Ht k Hk. rewrite Ht by assumption. apply Harr. lia.
Qed.

(* Multiplying ints. *)
Lemma mul_repr: forall (a b: Z), Int.mul (Int.repr a) (Int.repr b) = Int.repr (a * b).
Proof.
  intros a b. unfold Int.mul. apply Int.eqm_samerepr. apply Int.eqm_mult.
  - apply Int.eqm_sym. apply Int.eqm_unsigned_repr.
  - apply Int.eqm_sym. apply Int.eqm_unsigned_repr.
Qed.

(* Facts about the parts of memory that a call leaves unchanged. *)
Section Unchanged.
  Lemma arr_unchanged: forall (P: block -> Z -> Prop) (m m': mem) (b: block) (n: nat)
    (t: nat -> Z),
    Mem.unchanged_on P m m' -> (forall (ofs: Z), P b ofs) -> Arr m b n t -> Arr m' b n t.
  Proof.
    intros P m m' b n t Hun HP Harr k Hk.
    destruct (Harr k Hk) as [[Hperm Halign] Hload]. split.
    - split.
      + intros ofs Hofs. apply (Mem.unchanged_on_perm _ _ _ Hun).
        * apply HP.
        * apply (Mem.perm_valid_block _ _ ofs Cur Writable). apply Hperm. assumption.
        * apply Hperm. assumption.
      + assumption.
    - eapply Mem.load_unchanged_on.
      + apply Hun.
      + intros i _. apply HP.
      + assumption.
  Qed.

  Lemma fld_unchanged: forall (P: block -> Z -> Prop) (m m': mem) (b: block) (ofs: Z)
    (chunk: memory_chunk) (v: val),
    Mem.unchanged_on P m m' ->
    (forall (i: Z), ofs <= i < ofs + size_chunk chunk -> P b i) ->
    Fld m b ofs chunk v -> Fld m' b ofs chunk v.
  Proof.
    intros P m m' b ofs chunk v Hun HP [[Hperm Halign] Hload]. split.
    - split.
      + intros i Hi. apply (Mem.unchanged_on_perm _ _ _ Hun).
        * apply HP. assumption.
        * apply (Mem.perm_valid_block _ _ i Cur Writable). apply Hperm. assumption.
        * apply Hperm. assumption.
      + assumption.
    - eapply Mem.load_unchanged_on.
      + apply Hun.
      + assumption.
      + assumption.
  Qed.

  (* A store outside P leaves P unchanged. *)
  Lemma store_unchanged: forall (P: block -> Z -> Prop) (m0 m m': mem)
    (chunk: memory_chunk) (b: block) (ofs: Z) (v: val),
    Mem.unchanged_on P m0 m -> Mem.store chunk m b ofs v = Some m' ->
    (forall (i: Z), ~ P b i) -> Mem.unchanged_on P m0 m'.
  Proof.
    intros P m0 m m' chunk b ofs v Hun Hst HP. eapply Mem.unchanged_on_trans.
    - apply Hun.
    - eapply Mem.store_unchanged_on.
      + apply Hst.
      + intros i _. apply HP.
  Qed.
End Unchanged.
