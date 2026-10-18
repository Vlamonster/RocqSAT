(* A program logic for total correctness over CompCert's big-step semantics of Clight:
   Exec le m s Q says that s has a terminating execution from temporaries le and memory
   m, without events, to a state satisfying Q. Q also gets the outcome of s (normal,
   break, continue or return), so one postcondition says what holds after each. Every
   rule is a lemma about the semantics itself, so the logic needs no soundness proof of
   its own. The rules are drawn as inference rules in the comments, as in Software
   Foundations (Hoare.v), with {{ P }} s {{ Q }} for Exec. *)
From compcert Require Import Coqlib.
From compcert Require Import Maps.
From compcert Require Import Integers.
From compcert Require Import AST.
From compcert Require Import Values.
From compcert Require Import Memory.
From compcert Require Import Globalenvs.
From compcert Require Import Events.
From compcert Require Import Ctypes.
From compcert Require Import Cop.
From compcert Require Ctypesdefs.
From compcert Require Import Clight.
From compcert Require Import ClightBigstep.

From RocqSAT.refinement.c Require Import Arrays.

(* Comparisons of ints as C computes them, on their values. *)
Definition zcmp (c: comparison) (a b: Z): bool :=
match c with
| Ceq => a =? b
| Cne => negb (a =? b)
| Clt => a <? b
| Cle => a <=? b
| Cgt => b <? a
| Cge => b <=? a
end.

(* The operator of a comparison. *)
Definition cmp_op (c: comparison): binary_operation :=
match c with
| Ceq => Oeq
| Cne => One
| Clt => Olt
| Cle => Ole
| Cgt => Ogt
| Cge => Oge
end.

(* Small ints: below 2^30 in absolute value, so that sums of two of them do not
   overflow. *)
Abbreviation Small z := (-1073741824 <= z < 1073741824).

(* C compares small ints as their values. *)
Lemma int_cmp_repr: forall (c: comparison) (a b: Z), Small a -> Small b ->
  Int.cmp c (Int.repr a) (Int.repr b) = zcmp c a b.
Proof.
  intros c a b Ha Hb.
  assert (Hint: Int.max_signed = 2147483647) by reflexivity.
  assert (Hmin: Int.min_signed = - int_bound) by reflexivity.
  destruct c; simpl; unfold Int.lt; rewrite ?Int.eq_signed, !Int.signed_repr by lia.
  - destruct (zeq a b), (Z.eqb_spec a b); lia.
  - destruct (zeq a b), (Z.eqb_spec a b); simpl; lia.
  - destruct (zlt a b), (Z.ltb_spec a b); lia.
  - destruct (zlt b a), (Z.leb_spec a b); simpl; lia.
  - destruct (zlt b a), (Z.ltb_spec b a); lia.
  - destruct (zlt a b), (Z.leb_spec b a); simpl; lia.
Qed.

(* The answer of two calls in a row (Triple2): the first rejected its input, or the
   second returned the int z. *)
Inductive Answer: Type :=
| Rejected
| Returned (z: Z).

(* Whether a type is int. *)
Definition is_tint (t: type): bool := if type_eq t Ctypesdefs.tint then true else false.

Lemma is_tint_spec: forall (t: type), is_tint t = true -> t = Ctypesdefs.tint.
Proof.
  intros t Ht. unfold is_tint in Ht. destruct (type_eq t Ctypesdefs.tint).
  - assumption.
  - discriminate.
Qed.

(* A postcondition of a statement: on its temporaries, memory and outcome at the end. *)
Abbreviation Post := (temp_env -> mem -> outcome -> Prop).

(* The outcome of return z in a function returning int. *)
Abbreviation ret_int z := (Out_return (Some (vint z, Ctypesdefs.tint))).

Section Logic.
  Context (ge: genv).

  (* A terminating execution of s from le and m, without events, ending in a state
     satisfying Q. *)
  Definition Exec (le: temp_env) (m: mem) (s: statement)
    (Q: Post): Prop :=
    exists (le': temp_env) (m': mem) (out: outcome),
      exec_stmt function_entry2 ge empty_env le m s E0 le' m' out /\ Q le' m' out.

  (* A terminating call of fd on vargs from m, without events, ending in a state
     satisfying Q. *)
  Definition Call (m: mem) (fd: fundef) (vargs: list val) (Q: mem -> val -> Prop):
    Prop :=
    exists (m': mem) (v: val),
      eval_funcall function_entry2 ge m fd vargs E0 m' v /\ Q m' v.

  (* The rule of consequence, for the postcondition:

       {{ P }} s {{ Q }}    Q ->> Q'
       ----------------------------- (exec_weaken)
       {{ P }} s {{ Q' }}                                                           *)
  Lemma exec_weaken: forall (le: temp_env) (m: mem) (s: statement) (Q Q': Post),
    Exec le m s Q -> (forall le' m' out, Q le' m' out -> Q' le' m' out) ->
    Exec le m s Q'.
  Proof.
    intros le m s Q Q' [le' [m' [out [Hexec HQ]]]] Himp. exists le', m', out. split.
    - assumption.
    - apply Himp. assumption.
  Qed.

  (*   ---------------------------------- (exec_skip)
       {{ Q normal }} skip {{ Q }}                                                  *)
  Lemma exec_skip: forall (le: temp_env) (m: mem) (Q: Post),
    Q le m Out_normal -> Exec le m Sskip Q.
  Proof.
    intros le m Q HQ. exists le, m, Out_normal. split.
    - apply exec_Sskip.
    - assumption.
  Qed.

  (*   a evaluates to v
       ---------------------------------------- (exec_set)
       {{ Q[id := v] normal }} id = a {{ Q }}                                       *)
  Lemma exec_set: forall (le: temp_env) (m: mem) (id: ident) (a: expr) (v: val) (Q: Post),
    eval_expr ge empty_env le m a v -> Q (PTree.set id v le) m Out_normal ->
    Exec le m (Sset id a) Q.
  Proof.
    intros le m id a v Q Ha HQ. exists (PTree.set id v le), m, Out_normal. split.
    - apply exec_Sset. assumption.
    - assumption.
  Qed.

  (* An assignment through an l-value a1, giving the memory m': as Clight states it. *)
  Lemma exec_assign: forall (le: temp_env) (m m': mem) (a1 a2: expr) (loc: block)
    (ofs: ptrofs) (v2 v: val) (Q: Post),
    eval_lvalue ge empty_env le m a1 loc ofs Full ->
    eval_expr ge empty_env le m a2 v2 ->
    sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
    assign_loc ge (typeof a1) m loc ofs Full v m' ->
    Q le m' Out_normal ->
    Exec le m (Sassign a1 a2) Q.
  Proof.
    intros le m m' a1 a2 loc ofs v2 v Q H1 H2 Hcast Hassign HQ.
    exists le, m', Out_normal. split.
    - apply exec_Sassign with loc ofs Full v2 v.
      + assumption.
      + assumption.
      + assumption.
      + assumption.
    - assumption.
  Qed.

  (* An outcome is normal or not. *)
  Lemma outcome_normal_dec: forall (out: outcome), out = Out_normal \/ out <> Out_normal.
  Proof.
    intros out. destruct out.
    - right. discriminate.
    - right. discriminate.
    - left. reflexivity.
    - right. discriminate.
  Qed.

  (* What must hold after the first statement of a sequence: the second runs on a
     normal end, and Q holds otherwise. A definition, so that Q occurs once in goals:
     written out, each nested sequence would double it. *)
  Definition SeqK (s2: statement) (Q: Post) (le: temp_env)
    (m: mem) (out: outcome): Prop :=
    (out = Out_normal -> Exec le m s2 Q) /\ (out <> Out_normal -> Q le m out).

  (*   {{ P }} s1 {{ SeqK s2 Q }}
       ---------------------------- (exec_seq)
       {{ P }} s1; s2 {{ Q }}                                                       *)
  Lemma exec_seq: forall (le: temp_env) (m: mem) (s1 s2: statement) (Q: Post),
    Exec le m s1 (SeqK s2 Q) -> Exec le m (Ssequence s1 s2) Q.
  Proof.
    intros le m s1 s2 Q [le1 [m1 [out1 [H1 [Hnormal Habrupt]]]]].
    destruct (outcome_normal_dec out1) as [-> | Hne].
    - destruct (Hnormal eq_refl) as [le2 [m2 [out2 [H2 HQ]]]].
      exists le2, m2, out2. split.
      + change E0 with (E0 ** E0). apply exec_Sseq_1 with le1 m1.
        * assumption.
        * assumption.
      + assumption.
    - exists le1, m1, out1. split.
      + apply exec_Sseq_2.
        * assumption.
        * assumption.
      + apply Habrupt. assumption.
  Qed.

  (* After the first statement of a sequence: it ended normally and the second runs, or
     it ended otherwise (a break, continue or return) with Q. *)
  Lemma seqk_normal: forall (le: temp_env) (m: mem) (s2: statement) (Q: Post),
    Exec le m s2 Q -> SeqK s2 Q le m Out_normal.
  Proof.
    intros le m s2 Q H. split.
    - intros _. assumption.
    - intros Hne. contradiction.
  Qed.

  Lemma seqk_abrupt: forall (le: temp_env) (m: mem) (s2: statement)
    (Q: Post) (out: outcome),
    out <> Out_normal -> Q le m out -> SeqK s2 Q le m out.
  Proof.
    intros le m s2 Q out Hne HQ. split.
    - intros Heq. contradiction.
    - intros _. assumption.
  Qed.

  (* A store through an l-value of a by-value type:

       a1 is at loc + ofs (within the block)    a2 evaluates to v
       store of v at loc + ofs gives m'         {{ Q normal }} in m'
       ------------------------------------------------------------- (exec_store)
       {{ ... }} a1 = a2 {{ Q }}                                                    *)
  Lemma exec_store: forall (le: temp_env) (m: mem) (a1 a2: expr) (loc: block)
    (ofs: ptrofs) (v2 v: val) (chunk: memory_chunk) (Q: Post),
    eval_lvalue ge empty_env le m a1 loc ofs Full ->
    eval_expr ge empty_env le m a2 v2 ->
    sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
    access_mode (typeof a1) = By_value chunk ->
    Ptrofs.unsigned ofs + size_chunk chunk <= Ptrofs.modulus ->
    (exists (m': mem), Mem.store chunk m loc (Ptrofs.unsigned ofs) v = Some m' /\
       Q le m' Out_normal) ->
    Exec le m (Sassign a1 a2) Q.
  Proof.
    intros le m a1 a2 loc ofs v2 v chunk Q H1 H2 Hcast Hmode Hbound [m' [Hstore HQ]].
    apply (exec_assign le m m' a1 a2 loc ofs v2 v).
    - assumption.
    - assumption.
    - assumption.
    - apply assign_loc_value with chunk.
      + assumption.
      + unfold Mem.storev. destruct (zle _ _).
        * assumption.
        * lia.
    - assumption.
  Qed.

  (* A store needs the types and the place of its l-value: an int stored to the int at
     offset o, within the block. A check that computes, closed by reflexivity. *)
  Definition int_store (a1 a2: expr) (p: ptrofs) (o: Z): bool :=
    is_tint (typeof a1) && is_tint (typeof a2) && Z.eqb (Ptrofs.unsigned p) o &&
    Z.leb (o + 4) Ptrofs.modulus.

  (* A store of an int to a field, at offset o of block b, which the memory has (F):

       F: b holds an int at o    a1 is at b + o    a2 evaluates to the int i
       forall m', storing i at b + o gives m' -> {{ Q normal }} in m'
       ---------------------------------------------------------------- (exec_store_fld)
       {{ ... }} a1 = a2 {{ Q }}                                                    *)
  Lemma exec_store_fld: forall (le: temp_env) (m: mem) (b: block) (o: Z) (v0: val)
    (a1 a2: expr) (p: ptrofs) (i: int) (Q: Post),
    Fld m b o Mint32 v0 ->
    eval_lvalue ge empty_env le m a1 b p Full ->
    int_store a1 a2 p o = true ->
    eval_expr ge empty_env le m a2 (Vint i) ->
    (forall (m': mem), Mem.store Mint32 m b o (Vint i) = Some m' -> Q le m' Out_normal) ->
    Exec le m (Sassign a1 a2) Q.
  Proof.
    intros le m b o v0 a1 a2 p i Q F Hlv Hcheck Ha2 HQ. unfold int_store in Hcheck.
    apply andb_prop in Hcheck as [Hcheck Hbound].
    apply andb_prop in Hcheck as [Hcheck Ho].
    apply andb_prop in Hcheck as [Ht1 Ht2].
    apply is_tint_spec in Ht1. apply is_tint_spec in Ht2.
    apply Z.eqb_eq in Ho. apply Z.leb_le in Hbound.
    destruct (fld_storable m b o Mint32 v0 (Vint i) F) as [m' Hst].
    apply (exec_store le m a1 a2 b p (Vint i) (Vint i) Mint32).
    - assumption.
    - assumption.
    - rewrite Ht1, Ht2. reflexivity.
    - rewrite Ht1. reflexivity.
    - rewrite Ho. assumption.
    - exists m'. rewrite Ho. split.
      + assumption.
      + apply HQ. assumption.
  Qed.

  (* A store of an int to entry k of an array of n ints at block b, which the memory has
     (A):

       A: b holds n ints    k < n    a1 is at b + 4 k    a2 evaluates to the int i
       forall m', storing i at b + 4 k gives m' -> {{ Q normal }} in m'
       ---------------------------------------------------------------- (exec_store_arr)
       {{ ... }} a1 = a2 {{ Q }}                                                    *)
  Lemma exec_store_arr: forall (le: temp_env) (m: mem) (b: block) (n: nat) (t: nat -> Z)
    (k: nat) (a1 a2: expr) (p: ptrofs) (i: int) (Q: Post),
    Arr m b n t -> (k < n)%nat ->
    eval_lvalue ge empty_env le m a1 b p Full ->
    Ptrofs.unsigned p = 4 * Z.of_nat k ->
    is_tint (typeof a1) && is_tint (typeof a2) = true ->
    eval_expr ge empty_env le m a2 (Vint i) ->
    (forall (m': mem), Mem.store Mint32 m b (4 * Z.of_nat k) (Vint i) = Some m' ->
       Q le m' Out_normal) ->
    Exec le m (Sassign a1 a2) Q.
  Proof.
    intros le m b n t k a1 a2 p i Q A Hk Hlv Hp Hcheck Ha2 HQ.
    apply andb_prop in Hcheck as [Ht1 Ht2].
    apply is_tint_spec in Ht1. apply is_tint_spec in Ht2.
    destruct (A k Hk) as [Hvalid _].
    destruct (Mem.valid_access_store _ _ _ _ (Vint i) Hvalid) as [m' Hst].
    apply (exec_store le m a1 a2 b p (Vint i) (Vint i) Mint32).
    - assumption.
    - assumption.
    - rewrite Ht1, Ht2. reflexivity.
    - rewrite Ht1. reflexivity.
    - (* the entry is within the pointer range, as its offset is *)
      pose proof (Ptrofs.unsigned_range_2 p) as Hrange.
      assert (Hmod: Ptrofs.modulus = 18446744073709551616) by reflexivity.
      assert (Hmax: Ptrofs.max_unsigned = 18446744073709551615) by reflexivity.
      cbn [size_chunk]. lia.
    - exists m'. rewrite Hp. split.
      + assumption.
      + apply HQ. assumption.
  Qed.

  (* A branch on a comparison of small ints:

       a1 evaluates to z1    a2 evaluates to z2    both ints    both small
       {{ P }} (if zcmp c z1 z2 then s1 else s2) {{ Q }}
       --------------------------------------------------- (exec_if_cmp)
       {{ P }} if (a1 c a2) s1 else s2 {{ Q }}                                      *)
  Lemma exec_if_cmp: forall (le: temp_env) (m: mem) (c: comparison) (a1 a2: expr)
    (z1 z2: Z) (s1 s2: statement) (Q: Post),
    eval_expr ge empty_env le m a1 (vint z1) ->
    eval_expr ge empty_env le m a2 (vint z2) ->
    is_tint (typeof a1) && is_tint (typeof a2) = true -> Small z1 /\ Small z2 ->
    Exec le m (if zcmp c z1 z2 then s1 else s2) Q ->
    Exec le m (Sifthenelse (Ebinop (cmp_op c) a1 a2 Ctypesdefs.tint) s1 s2) Q.
  Proof.
    intros le m c a1 a2 z1 z2 s1 s2 Q H1 H2 Ht [Hz1 Hz2] [le' [m' [out [Hexec HQ]]]].
    apply andb_prop in Ht as [Ht1 Ht2].
    apply is_tint_spec in Ht1. apply is_tint_spec in Ht2.
    exists le', m', out. split.
    - apply exec_Sifthenelse with (Val.of_bool (zcmp c z1 z2)) (zcmp c z1 z2).
      + apply eval_Ebinop with (vint z1) (vint z2).
        * assumption.
        * assumption.
        * rewrite Ht1, Ht2, <- int_cmp_repr by assumption. destruct c; reflexivity.
      + destruct (zcmp c z1 z2); reflexivity.
      + assumption.
    - assumption.
  Qed.

  (* A branch on a small int, taken unless it is 0:

       a evaluates to z    an int    small
       {{ P }} (if z <> 0 then s1 else s2) {{ Q }}
       ------------------------------------------- (exec_if_int)
       {{ P }} if (a) s1 else s2 {{ Q }}                                            *)
  Lemma exec_if_int: forall (le: temp_env) (m: mem) (a: expr) (z: Z) (s1 s2: statement)
    (Q: Post),
    eval_expr ge empty_env le m a (vint z) -> is_tint (typeof a) = true -> Small z ->
    Exec le m (if negb (z =? 0) then s1 else s2) Q -> Exec le m (Sifthenelse a s1 s2) Q.
  Proof.
    intros le m a z s1 s2 Q Ha Ht Hz [le' [m' [out [Hexec HQ]]]].
    apply is_tint_spec in Ht. exists le', m', out. split.
    - apply exec_Sifthenelse with (vint z) (negb (z =? 0)).
      + assumption.
      + rewrite Ht. unfold vint, bool_val, Ctypesdefs.tint. simpl.
        rewrite Int.eq_signed, Int.signed_repr, Int.signed_zero.
        * destruct (zeq z 0), (Z.eqb_spec z 0).
          -- reflexivity.
          -- contradiction.
          -- contradiction.
          -- reflexivity.
        * assert (Int.max_signed = 2147483647) by reflexivity.
          assert (Int.min_signed = - int_bound) by reflexivity.
          lia.
      + assumption.
    - assumption.
  Qed.

  (* A branch on a comparison c of two small ints, where each branch knows the outcome
     of the test, a proposition T that holds exactly when zcmp c z1 z2 does:

       a1 evaluates to z1    a2 evaluates to z2    both ints    both small
       zcmp c z1 z2 = true <-> T
       T -> {{ P }} s1 {{ Q }}      ~ T -> {{ P }} s2 {{ Q }}
       ----------------------------------------------------------------- (exec_if_test)
       {{ P }} if (a1 c a2) s1 else s2 {{ Q }}

     exec_if_lt .. exec_if_ne are its instances, where the else branch knows the negated
     comparison: for exec_if_lt, z1 < z2 -> {{ P }} s1 {{ Q }} and
     z2 <= z1 -> {{ P }} s2 {{ Q }}. *)
  Lemma exec_if_test: forall (le: temp_env) (m: mem) (c: comparison) (a1 a2: expr)
    (z1 z2: Z) (s1 s2: statement) (Q: Post) (T: Prop),
    eval_expr ge empty_env le m a1 (vint z1) ->
    eval_expr ge empty_env le m a2 (vint z2) ->
    is_tint (typeof a1) && is_tint (typeof a2) = true -> Small z1 /\ Small z2 ->
    (zcmp c z1 z2 = true <-> T) ->
    (T -> Exec le m s1 Q) -> (~ T -> Exec le m s2 Q) ->
    Exec le m (Sifthenelse (Ebinop (cmp_op c) a1 a2 Ctypesdefs.tint) s1 s2) Q.
  Proof.
    intros le m c a1 a2 z1 z2 s1 s2 Q T H1 H2 Ht Hz Hiff Hthen Helse.
    apply exec_if_cmp with z1 z2.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - destruct (zcmp c z1 z2) eqn:Hc.
      + apply Hthen. now apply Hiff.
      + apply Helse. intros HT. apply Hiff in HT. discriminate.
  Qed.

  Lemma exec_if_lt: forall (le: temp_env) (m: mem) (a1 a2: expr) (z1 z2: Z)
    (s1 s2: statement) (Q: Post),
    eval_expr ge empty_env le m a1 (vint z1) ->
    eval_expr ge empty_env le m a2 (vint z2) ->
    is_tint (typeof a1) && is_tint (typeof a2) = true -> Small z1 /\ Small z2 ->
    (z1 < z2 -> Exec le m s1 Q) -> (z2 <= z1 -> Exec le m s2 Q) ->
    Exec le m (Sifthenelse (Ebinop Olt a1 a2 Ctypesdefs.tint) s1 s2) Q.
  Proof.
    intros le m a1 a2 z1 z2 s1 s2 Q H1 H2 Ht Hz Hthen Helse.
    apply (exec_if_test le m Clt a1 a2 z1 z2 s1 s2 Q (z1 < z2)).
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - apply Z.ltb_lt.
    - assumption.
    - intros Hn. apply Helse. lia.
  Qed.

  Lemma exec_if_le: forall (le: temp_env) (m: mem) (a1 a2: expr) (z1 z2: Z)
    (s1 s2: statement) (Q: Post),
    eval_expr ge empty_env le m a1 (vint z1) ->
    eval_expr ge empty_env le m a2 (vint z2) ->
    is_tint (typeof a1) && is_tint (typeof a2) = true -> Small z1 /\ Small z2 ->
    (z1 <= z2 -> Exec le m s1 Q) -> (z2 < z1 -> Exec le m s2 Q) ->
    Exec le m (Sifthenelse (Ebinop Ole a1 a2 Ctypesdefs.tint) s1 s2) Q.
  Proof.
    intros le m a1 a2 z1 z2 s1 s2 Q H1 H2 Ht Hz Hthen Helse.
    apply (exec_if_test le m Cle a1 a2 z1 z2 s1 s2 Q (z1 <= z2)).
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - apply Z.leb_le.
    - assumption.
    - intros Hn. apply Helse. lia.
  Qed.

  Lemma exec_if_gt: forall (le: temp_env) (m: mem) (a1 a2: expr) (z1 z2: Z)
    (s1 s2: statement) (Q: Post),
    eval_expr ge empty_env le m a1 (vint z1) ->
    eval_expr ge empty_env le m a2 (vint z2) ->
    is_tint (typeof a1) && is_tint (typeof a2) = true -> Small z1 /\ Small z2 ->
    (z2 < z1 -> Exec le m s1 Q) -> (z1 <= z2 -> Exec le m s2 Q) ->
    Exec le m (Sifthenelse (Ebinop Ogt a1 a2 Ctypesdefs.tint) s1 s2) Q.
  Proof.
    intros le m a1 a2 z1 z2 s1 s2 Q H1 H2 Ht Hz Hthen Helse.
    apply (exec_if_test le m Cgt a1 a2 z1 z2 s1 s2 Q (z2 < z1)).
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - apply Z.ltb_lt.
    - assumption.
    - intros Hn. apply Helse. lia.
  Qed.

  Lemma exec_if_ge: forall (le: temp_env) (m: mem) (a1 a2: expr) (z1 z2: Z)
    (s1 s2: statement) (Q: Post),
    eval_expr ge empty_env le m a1 (vint z1) ->
    eval_expr ge empty_env le m a2 (vint z2) ->
    is_tint (typeof a1) && is_tint (typeof a2) = true -> Small z1 /\ Small z2 ->
    (z2 <= z1 -> Exec le m s1 Q) -> (z1 < z2 -> Exec le m s2 Q) ->
    Exec le m (Sifthenelse (Ebinop Oge a1 a2 Ctypesdefs.tint) s1 s2) Q.
  Proof.
    intros le m a1 a2 z1 z2 s1 s2 Q H1 H2 Ht Hz Hthen Helse.
    apply (exec_if_test le m Cge a1 a2 z1 z2 s1 s2 Q (z2 <= z1)).
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - apply Z.leb_le.
    - assumption.
    - intros Hn. apply Helse. lia.
  Qed.

  Lemma exec_if_eq: forall (le: temp_env) (m: mem) (a1 a2: expr) (z1 z2: Z)
    (s1 s2: statement) (Q: Post),
    eval_expr ge empty_env le m a1 (vint z1) ->
    eval_expr ge empty_env le m a2 (vint z2) ->
    is_tint (typeof a1) && is_tint (typeof a2) = true -> Small z1 /\ Small z2 ->
    (z1 = z2 -> Exec le m s1 Q) -> (z1 <> z2 -> Exec le m s2 Q) ->
    Exec le m (Sifthenelse (Ebinop Oeq a1 a2 Ctypesdefs.tint) s1 s2) Q.
  Proof.
    intros le m a1 a2 z1 z2 s1 s2 Q H1 H2 Ht Hz Hthen Helse.
    apply (exec_if_test le m Ceq a1 a2 z1 z2 s1 s2 Q (z1 = z2)).
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - apply Z.eqb_eq.
    - assumption.
    - assumption.
  Qed.

  Lemma exec_if_ne: forall (le: temp_env) (m: mem) (a1 a2: expr) (z1 z2: Z)
    (s1 s2: statement) (Q: Post),
    eval_expr ge empty_env le m a1 (vint z1) ->
    eval_expr ge empty_env le m a2 (vint z2) ->
    is_tint (typeof a1) && is_tint (typeof a2) = true -> Small z1 /\ Small z2 ->
    (z1 <> z2 -> Exec le m s1 Q) -> (z1 = z2 -> Exec le m s2 Q) ->
    Exec le m (Sifthenelse (Ebinop One a1 a2 Ctypesdefs.tint) s1 s2) Q.
  Proof.
    intros le m a1 a2 z1 z2 s1 s2 Q H1 H2 Ht Hz Hthen Helse.
    apply (exec_if_test le m Cne a1 a2 z1 z2 s1 s2 Q (z1 <> z2)).
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - cbn [zcmp]. rewrite negb_true_iff. apply Z.eqb_neq.
    - assumption.
    - intros Hn. apply Helse. lia.
  Qed.

  (* A branch on a small int, taken unless it is 0, where each branch knows which:

       a evaluates to z    an int    small
       z <> 0 -> {{ P }} s1 {{ Q }}      z = 0 -> {{ P }} s2 {{ Q }}
       ----------------------------------------------------------- (exec_if_nonzero)
       {{ P }} if (a) s1 else s2 {{ Q }}                                            *)
  Lemma exec_if_nonzero: forall (le: temp_env) (m: mem) (a: expr) (z: Z)
    (s1 s2: statement) (Q: Post),
    eval_expr ge empty_env le m a (vint z) -> is_tint (typeof a) = true -> Small z ->
    (z <> 0 -> Exec le m s1 Q) -> (z = 0 -> Exec le m s2 Q) ->
    Exec le m (Sifthenelse a s1 s2) Q.
  Proof.
    intros le m a z s1 s2 Q Ha Ht Hz Hthen Helse.
    apply exec_if_int with z.
    - assumption.
    - assumption.
    - assumption.
    - destruct (Z.eqb_spec z 0) as [Heq | Hne].
      + now apply Helse.
      + now apply Hthen.
  Qed.

  (* A branch on any value of a known truth value b. *)
  Lemma exec_if: forall (le: temp_env) (m: mem) (a: expr) (s1 s2: statement) (v: val)
    (b: bool) (Q: Post),
    eval_expr ge empty_env le m a v -> bool_val v (typeof a) m = Some b ->
    Exec le m (if b then s1 else s2) Q -> Exec le m (Sifthenelse a s1 s2) Q.
  Proof.
    intros le m a s1 s2 v b Q Ha Hb [le' [m' [out [Hexec HQ]]]]. exists le', m', out.
    split.
    - apply exec_Sifthenelse with v b.
      + assumption.
      + assumption.
      + assumption.
    - assumption.
  Qed.

  (*   a evaluates to v
       ---------------------------------------- (exec_return)
       {{ Q (return v) }} return a {{ Q }}                                          *)
  Lemma exec_return: forall (le: temp_env) (m: mem) (a: expr) (v: val) (Q: Post),
    eval_expr ge empty_env le m a v -> Q le m (Out_return (Some (v, typeof a))) ->
    Exec le m (Sreturn (Some a)) Q.
  Proof.
    intros le m a v Q Ha HQ. exists le, m, (Out_return (Some (v, typeof a))). split.
    - apply exec_Sreturn_some. assumption.
    - assumption.
  Qed.

  (* A return without a value:

         ---------------------------------------- (exec_return_none)
         {{ Q (return) }} return; {{ Q }}                                             *)
  Lemma exec_return_none: forall (le: temp_env) (m: mem)
    (Q: Post),
    Q le m (Out_return None) -> Exec le m (Sreturn None) Q.
  Proof.
    intros le m Q HQ. exists le, m, (Out_return None). split.
    - apply exec_Sreturn_none.
    - assumption.
  Qed.

  (*   ---------------------------------- (exec_break)
       {{ Q break }} break {{ Q }}                                                  *)
  Lemma exec_break: forall (le: temp_env) (m: mem) (Q: Post),
    Q le m Out_break -> Exec le m Sbreak Q.
  Proof.
    intros le m Q HQ. exists le, m, Out_break. split.
    - apply exec_Sbreak.
    - assumption.
  Qed.

  (*   ---------------------------------------- (exec_continue)
       {{ Q continue }} continue {{ Q }}                                            *)
  Lemma exec_continue: forall (le: temp_env) (m: mem) (Q: Post),
    Q le m Out_continue -> Exec le m Scontinue Q.
  Proof.
    intros le m Q HQ. exists le, m, Out_continue. split.
    - apply exec_Scontinue.
    - assumption.
  Qed.

  (* What must hold after the body of a loop with invariant I, at index a: the loop goes
     on with a smaller index, or ends, normally after a break, or returning. A
     definition for the same reason as SeqK. *)
  Definition LoopK {A: Type} (R: A -> A -> Prop) (I: A -> temp_env -> mem -> Prop)
    (Q: Post) (a: A) (le: temp_env) (m: mem)
    (out: outcome): Prop :=
    ((out = Out_normal \/ out = Out_continue) /\ exists a', R a' a /\ I a' le m) \/
    (out = Out_break /\ Q le m Out_normal) \/
    (exists r, out = Out_return r /\ Q le m out).

  (* The ways a loop body can end: normally or with a continue, at a smaller index with
     the invariant; with a break; with a return. *)
  Lemma loopk_next: forall {A: Type} (R: A -> A -> Prop)
    (I: A -> temp_env -> mem -> Prop) (Q: Post) (a a': A) (le: temp_env) (m: mem),
    R a' a -> I a' le m -> LoopK R I Q a le m Out_normal.
  Proof.
    intros A R I Q a a' le m HR HI. left. split.
    - left. reflexivity.
    - exists a'. split.
      + assumption.
      + assumption.
  Qed.

  Lemma loopk_continue: forall {A: Type} (R: A -> A -> Prop)
    (I: A -> temp_env -> mem -> Prop) (Q: Post) (a a': A) (le: temp_env) (m: mem),
    R a' a -> I a' le m -> LoopK R I Q a le m Out_continue.
  Proof.
    intros A R I Q a a' le m HR HI. left. split.
    - right. reflexivity.
    - exists a'. split.
      + assumption.
      + assumption.
  Qed.

  Lemma loopk_break: forall {A: Type} (R: A -> A -> Prop)
    (I: A -> temp_env -> mem -> Prop) (Q: Post) (a: A) (le: temp_env) (m: mem),
    Q le m Out_normal -> LoopK R I Q a le m Out_break.
  Proof.
    intros A R I Q a le m HQ. right. left. split.
    - reflexivity.
    - assumption.
  Qed.

  Lemma loopk_return: forall {A: Type} (R: A -> A -> Prop)
    (I: A -> temp_env -> mem -> Prop) (Q: Post) (a: A) (le: temp_env) (m: mem)
    (r: option (val * type)),
    Q le m (Out_return r) -> LoopK R I Q a le m (Out_return r).
  Proof.
    intros A R I Q a le m r HQ. right. right. exists r. split.
    - reflexivity.
    - assumption.
  Qed.

  (* A loop whose body keeps the invariant I for a smaller index in a well-founded
     relation R, or leaves the loop; R gives termination. Our loops have no increment
     statement:

       R well-founded    for all a, {{ I a }} s {{ LoopK R I Q a }}
       ------------------------------------------------------------- (exec_loop)
       {{ I a }} loop s {{ Q }}                                                     *)
  Lemma exec_loop: forall {A: Type} (R: A -> A -> Prop) (I: A -> temp_env -> mem -> Prop)
    (s: statement) (Q: Post),
    well_founded R ->
    (forall a le m, I a le m -> Exec le m s (LoopK R I Q a)) ->
    forall a le m, I a le m -> Exec le m (Sloop s Sskip) Q.
  Proof.
    intros A R I s Q Hwf Hbody a. induction a as [a IH] using (well_founded_ind Hwf).
    intros le m HI.
    destruct (Hbody a le m HI)
      as [le1 [m1 [out1 [H1 [[Hout [a' [Hlt HI']]] | [[Hbrk HQ] | [r [Hret HQ]]]]]]]].
    - (* the body ended normally or continued: run the loop again from a' *)
      destruct (IH a' Hlt le1 m1 HI') as [le2 [m2 [out2 [H2 HQ]]]].
      exists le2, m2, out2. split.
      + change E0 with (E0 ** E0 ** E0). apply exec_Sloop_loop with le1 m1 out1 le1 m1.
        * assumption.
        * destruct Hout as [Hn | Hc]; subst out1; constructor.
        * apply exec_Sskip.
        * assumption.
      + assumption.
    - (* a break *)
      subst out1. exists le1, m1, Out_normal. split.
      + apply exec_Sloop_stop1 with Out_break.
        * assumption.
        * constructor.
      + assumption.
    - (* a return *)
      subst out1. exists le1, m1, (Out_return r). split.
      + apply exec_Sloop_stop1 with (Out_return r).
        * assumption.
        * constructor.
      + assumption.
  Qed.

  (* A call of global function id, defined as fd, on arguments al evaluating to vargs:

       id names fd    al evaluate to vargs    Call m fd vargs (Q[optid := v] normal)
       ------------------------------------------------------------------ (exec_call)
       {{ ... }} optid = id(al) {{ Q }}                                             *)
  Lemma exec_call: forall (le: temp_env) (m: mem) (optid: option ident) (id: ident)
    (ty: type) (al: list expr) (tyargs: list type) (tyres: type) (cc: calling_convention)
    (b: block) (fd: fundef) (vargs: list val) (Q: Post),
    ty = Tfunction tyargs tyres cc ->
    Genv.find_symbol ge id = Some b ->
    Genv.find_funct_ptr ge b = Some fd ->
    type_of_fundef fd = ty ->
    eval_exprlist ge empty_env le m al tyargs vargs ->
    Call m fd vargs (fun m' v => Q (set_opttemp optid v le) m' Out_normal) ->
    Exec le m (Scall optid (Evar id ty) al) Q.
  Proof.
    intros le m optid id ty al tyargs tyres cc b fd vargs Q Hty Hsym Hfunct Htype Hargs
      [m' [v [Hcall HQ]]].
    exists (set_opttemp optid v le), m', Out_normal. split.
    - subst ty. apply exec_Scall with tyargs tyres cc (Vptr b Ptrofs.zero) vargs fd.
      + reflexivity.
      + apply eval_Elvalue with b Ptrofs.zero Full.
        * apply eval_Evar_global.
          -- reflexivity.
          -- assumption.
        * apply deref_loc_reference. reflexivity.
      + assumption.
      + simpl. rewrite pred_dec_true by reflexivity. assumption.
      + assumption.
      + assumption.
    - assumption.
  Qed.

  (* The rule of consequence for calls. *)
  Lemma call_weaken: forall (m: mem) (fd: fundef) (vargs: list val)
    (Q Q': mem -> val -> Prop),
    Call m fd vargs Q -> (forall m' v, Q m' v -> Q' m' v) -> Call m fd vargs Q'.
  Proof.
    intros m fd vargs Q Q' [m' [v [Hcall HQ]]] Himp. exists m', v. split.
    - assumption.
    - apply Himp. assumption.
  Qed.

  (* Calling an internal function without local variables: its parameters become
     temporaries. *)
  Lemma call_internal: forall (m: mem) (f: function) (vargs: list val) (le: temp_env)
    (Q: mem -> val -> Prop),
    fn_vars f = nil ->
    list_norepet (var_names (fn_params f)) ->
    list_disjoint (var_names (fn_params f)) (var_names (fn_temps f)) ->
    bind_parameter_temps (fn_params f) vargs (create_undef_temps (fn_temps f))
      = Some le ->
    Exec le m (fn_body f)
      (fun _ m' out =>
         exists v, outcome_result_value out (fn_return f) v m' /\ Q m' v) ->
    Call m (Internal f) vargs Q.
  Proof.
    intros m f vargs le Q Hvars Hnorepet Hdisj Hbind
      [le' [m' [out [Hexec [v [Hres HQ]]]]]].
    exists m', v. split.
    - apply (eval_funcall_internal function_entry2 ge m f vargs E0 empty_env le le' m m'
               out v m').
      + constructor.
        * rewrite Hvars. constructor.
        * assumption.
        * assumption.
        * rewrite Hvars. constructor.
        * assumption.
      + assumption.
      + assumption.
      + reflexivity.
    - assumption.
  Qed.

  (* Parts of a generated function body, so that a loop can be proved in a lemma of
     its own: the statements of a sequence s1; s2; ... (nested to the right, as
     clightgen writes it) after the first k, the first statement of a sequence, the
     body of a loop, and the then and else branches of an if. *)
  Fixpoint drop_stmts (k: nat) (s: statement): statement :=
    match k, s with
    | S k', Ssequence _ s2 => drop_stmts k' s2
    | _,    _              => s
    end.

  Definition first_stmt (s: statement): statement :=
    match s with
    | Ssequence s1 _ => s1
    | _              => s
    end.

  Definition loop_body (s: statement): statement :=
    match s with
    | Sloop body _ => body
    | _            => Sskip
    end.

  Definition then_stmt (s: statement): statement :=
    match s with
    | Sifthenelse _ s1 _ => s1
    | _                  => Sskip
    end.

  Definition else_stmt (s: statement): statement :=
    match s with
    | Sifthenelse _ _ s2 => s2
    | _                  => Sskip
    end.

  (* Hoare triples for calls, in the style of Software Foundations: from every memory m
     with P m, the call of f on args terminates, without events, in a memory m' returning
     a value v with Q m m' v. Q may mention the memory m before the call, as the
     postconditions of Software Foundations mention logical variables. The notation
     {{ m | P }} f(args) {{ m', v | Q }} is in Rep.v, where the program is known. *)
  Definition Triple (P: mem -> Prop) (f: function) (args: list val)
    (Q: mem -> mem -> val -> Prop): Prop :=
    forall (m: mem), P m -> Call m (Internal f) args (Q m).

  (* Triples for two calls in a row, as a driver makes them: from every memory m with
     P m, f1(args1) terminates; either it returned 0 and Q holds for the answer
     Rejected, or f2(args2) then terminates returning an int z and Q holds for the
     answer Returned z (so when f1 did not return 0, the second holds). The notation
     {{ m | P }} f1(x); f2(y) {{ m', r | Q }} is in Rep.v. *)
  Definition Triple2 (P: mem -> Prop) (f1: function) (args1: list val) (f2: function)
    (args2: list val) (Q: mem -> Answer -> Prop): Prop :=
    forall (m: mem), P m ->
      Call m (Internal f1) args1 (fun m1 v1 =>
        (v1 = vint 0 /\ Q m1 Rejected) \/
        Call m1 (Internal f2) args2 (fun m2 v2 =>
          exists (z: Z), v2 = vint z /\ Q m2 (Returned z))).

  (* A call of a function with a triple, whose result goes to temporary t: from P in the
     memory of the call, the call runs, and from its postcondition the rest goes on:

       id names f    al evaluate to vargs    {{ m | P }} f(vargs) {{ m', v | Qf }}
       P m    forall m' v, Qf m m' v -> {{ Q[t := v] normal }} in m'
       ---------------------------------------------------------- (exec_call_triple)
       {{ ... }} t = id(al) {{ Q }}

     exec_call_triple_none is the same for a call without a result. *)
  Lemma exec_call_triple: forall (le: temp_env) (m: mem) (t id: ident) (tyargs: list type)
    (tyres: type) (cc: calling_convention) (al: list expr) (f: function)
    (vargs: list val) (P: mem -> Prop) (Qf: mem -> mem -> val -> Prop) (Q: Post),
    (exists (b: block),
       Genv.find_symbol ge id = Some b /\ Genv.find_funct_ptr ge b = Some (Internal f)) ->
    Triple P f vargs Qf ->
    type_of_function f = Tfunction tyargs tyres cc ->
    eval_exprlist ge empty_env le m al tyargs vargs ->
    P m ->
    (forall (m': mem) (v: val), Qf m m' v -> Q (PTree.set t v le) m' Out_normal) ->
    Exec le m (Scall (Some t) (Evar id (Tfunction tyargs tyres cc)) al) Q.
  Proof.
    intros le m t id tyargs tyres cc al f vargs P Qf Q (b & Hsym & Hptr) Htriple Hty
      Hargs HP HQ.
    apply (exec_call le m (Some t) id _ al tyargs tyres cc b (Internal f) vargs).
    - reflexivity.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - apply (call_weaken m (Internal f) vargs (Qf m)).
      + apply Htriple. assumption.
      + assumption.
  Qed.

  Lemma exec_call_triple_none: forall (le: temp_env) (m: mem) (id: ident)
    (tyargs: list type) (tyres: type) (cc: calling_convention) (al: list expr)
    (f: function) (vargs: list val) (P: mem -> Prop) (Qf: mem -> mem -> val -> Prop)
    (Q: Post),
    (exists (b: block),
       Genv.find_symbol ge id = Some b /\ Genv.find_funct_ptr ge b = Some (Internal f)) ->
    Triple P f vargs Qf ->
    type_of_function f = Tfunction tyargs tyres cc ->
    eval_exprlist ge empty_env le m al tyargs vargs ->
    P m ->
    (forall (m': mem) (v: val), Qf m m' v -> Q le m' Out_normal) ->
    Exec le m (Scall None (Evar id (Tfunction tyargs tyres cc)) al) Q.
  Proof.
    intros le m id tyargs tyres cc al f vargs P Qf Q (b & Hsym & Hptr) Htriple Hty Hargs
      HP HQ.
    apply (exec_call le m None id _ al tyargs tyres cc b (Internal f) vargs).
    - reflexivity.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - apply (call_weaken m (Internal f) vargs (Qf m)).
      + apply Htriple. assumption.
      + assumption.
  Qed.

  (* A function returning int returns the int of its return statement. *)
  Lemma result_int: forall (z: Z) (m: mem),
    outcome_result_value (ret_int z) Ctypesdefs.tint
      (vint z) m.
  Proof.
    intros z m. split.
    - discriminate.
    - reflexivity.
  Qed.

  (* A function is simple when it has no local variables, and its parameters are distinct
     and differ from its temporaries. Every function of the solver is: reflexivity checks
     it. *)
  Definition simple (f: function): bool :=
    let params := var_names (fn_params f) in
    match fn_vars f with
    | nil => true
    | _   => false
    end &&
    proj_sumbool (list_norepet_dec ident_eq params) &&
    proj_sumbool (list_disjoint_dec ident_eq params (var_names (fn_temps f))).

  (* The temporaries le of a call of f on vargs: its parameters bound to vargs. *)
  Definition Binds (f: function) (vargs: list val) (le: temp_env): Prop :=
    bind_parameter_temps (fn_params f) vargs (create_undef_temps (fn_temps f)) = Some le.

  (* After the body of f: it returned a value v with Q in the memory m' at the end. *)
  Definition Returns (f: function) (Q: mem -> val -> Prop) (le: temp_env) (m': mem)
    (out: outcome): Prop :=
    exists (v: val), outcome_result_value out (fn_return f) v m' /\ Q m' v.

  (* Calling a simple function runs its body, with its parameters bound to the arguments:

       simple f = true    Binds f vargs le    Exec le m (fn_body f) (Returns f Q)
       ------------------------------------------------------------- (call_simple)
       Call m (Internal f) vargs Q                                                  *)
  Lemma call_simple: forall (m: mem) (f: function) (vargs: list val) (le: temp_env)
    (Q: mem -> val -> Prop),
    simple f = true -> Binds f vargs le -> Exec le m (fn_body f) (Returns f Q) ->
    Call m (Internal f) vargs Q.
  Proof.
    intros m f vargs le Q Hsimple Hbind Hbody. unfold simple in Hsimple.
    apply andb_prop in Hsimple as [Hsimple Hdisjoint].
    apply andb_prop in Hsimple as [Hvars Hnorepet].
    apply (call_internal m f vargs le Q).
    - destruct (fn_vars f).
      + reflexivity.
      + discriminate.
    - destruct (list_norepet_dec ident_eq (var_names (fn_params f))) as [Hok | Hnot].
      + assumption.
      + discriminate.
    - destruct (list_disjoint_dec ident_eq (var_names (fn_params f))
                  (var_names (fn_temps f))) as [Hok | Hnot].
      + assumption.
      + discriminate.
    - assumption.
    - assumption.
  Qed.
End Logic.

(* The branch rules take the values compared explicitly: exec_if_lt z1 z2. *)
Arguments exec_if_lt {ge le m a1 a2} z1 z2 {s1 s2 Q}.
Arguments exec_if_le {ge le m a1 a2} z1 z2 {s1 s2 Q}.
Arguments exec_if_gt {ge le m a1 a2} z1 z2 {s1 s2 Q}.
Arguments exec_if_ge {ge le m a1 a2} z1 z2 {s1 s2 Q}.
Arguments exec_if_eq {ge le m a1 a2} z1 z2 {s1 s2 Q}.
Arguments exec_if_ne {ge le m a1 a2} z1 z2 {s1 s2 Q}.
Arguments exec_if_nonzero {ge le m a} z {s1 s2 Q}.

(* The rules are applied to their facts and triples: the rest is inferred. *)
Arguments exec_store_fld {ge le m b o v0 a1 a2 p i Q}.
Arguments exec_store_arr {ge le m b n t k a1 a2 p i Q}.
Arguments exec_call_triple {ge le m t id tyargs tyres cc al f vargs P Qf Q}.
Arguments exec_call_triple_none {ge le m id tyargs tyres cc al f vargs P Qf Q}.
