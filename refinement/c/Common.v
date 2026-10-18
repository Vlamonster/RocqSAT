(* What the proofs of the C solvers share: literals as keys, values of atoms, and the
   tactics that run straight-line code over arrays and struct fields. *)
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
From RocqSAT.refinement Require Import Table.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement.c Require Import Arrays.
From RocqSAT.refinement.c Require Import Logic.

(* A literal as C keeps it, its key: 2p for Pos p and 2p + 1 for Neg p. *)
Definition key (l: Lit): Z := Z.of_nat (lit_key l).

(* A value as C keeps it: 1 for true, -1 for false and 0 for none. *)
Definition enc_value (b: option bool): Z :=
match b with
| Some true  => 1
| Some false => -1
| None       => 0
end.

(* The literal with key z: 2p is Pos p and 2p + 1 is Neg p. *)
Definition lit_of (z: Z): Lit :=
  let k := Z.to_nat z in if Nat.even k then Pos (Nat.div2 k) else Neg (Nat.div2 k).

(* The key of the literal with key z is z. *)
Lemma key_lit_of: forall (z: Z), 0 <= z -> key (lit_of z) = z.
Proof.
  intros z Hz. unfold key, lit_of.
  pose proof (Nat.div2_odd (Z.to_nat z)) as Hdiv.
  rewrite <- Nat.negb_odd.
  destruct (Nat.odd (Z.to_nat z)); cbn [negb lit_key Nat.b2n] in *.
  - lia.
  - lia.
Qed.

(* The literal with the key of l is l. *)
Lemma lit_of_key: forall (l: Lit), lit_of (key l) = l.
Proof.
  intros l. apply lit_key_inj. assert (Hk: key (lit_of (key l)) = key l).
  - apply key_lit_of. unfold key. lia.
  - unfold key in *. lia.
Qed.

(* The atom of a literal key is the key shifted right by one, and its lowest bit tells
   its sign. *)
Lemma shr_key: forall (l: Lit), 0 <= key l < small_bound ->
  Int.shr (Int.repr (key l)) (Int.repr 1) = Int.repr (Z.of_nat (extract l)).
Proof.
  intros l Hl. assert (Hint: Int.max_signed = 2147483647) by reflexivity.
  assert (Hmin: Int.min_signed = - int_bound) by reflexivity.
  unfold key in *. unfold Int.shr. rewrite Int.signed_repr by lia.
  rewrite Int.unsigned_repr by (unfold Int.max_unsigned; simpl; lia).
  rewrite Z.shiftr_div_pow2, Z.pow_1_r by lia. f_equal.
  destruct l as [p|p]; cbn [lit_key extract] in *.
  - symmetry. apply Z.div_unique with 0; lia.
  - symmetry. apply Z.div_unique with 1; lia.
Qed.

(* The lowest bit of a key: 0 for a positive literal, 1 for a negative one. *)
Lemma land_key: forall (l: Lit), Z.land (key l) 1 = if is_pos l then 0 else 1.
Proof.
  intros l. unfold key. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia.
  destruct l as [p|p]; cbn [lit_key is_pos].
  - symmetry. apply Z.mod_unique with (Z.of_nat p); lia.
  - symmetry. apply Z.mod_unique with (Z.of_nat p); lia.
Qed.

(* The same, as C computes it: key & 1. *)
Lemma and_key: forall (l: Lit), 0 <= key l < small_bound ->
  Int.and (Int.repr (key l)) (Int.repr 1) = Int.repr (if is_pos l then 0 else 1).
Proof.
  intros l Hl. unfold Int.and.
  rewrite !Int.unsigned_repr by (unfold Int.max_unsigned; simpl; lia).
  now rewrite land_key.
Qed.

(* The value C computes for a literal: 1 - 2 * (key & 1). *)
Lemma sign_value: forall (b: bool),
  Int.sub (Int.repr 1) (Int.mul (Int.repr 2) (Int.repr (if b then 0 else 1)))
  = Int.repr (enc_value (Some b)).
Proof. intros b. now destruct b. Qed.

(* Entries at different positions of a list without duplicates differ. *)
Lemma nodup_nth_neq: forall {A: Type} (l: list A) (i j: nat) (d: A),
  NoDup l -> (i < length l)%nat -> (j < length l)%nat -> i <> j ->
  nth i l d <> nth j l d.
Proof.
  intros A l i j d Hnd Hi Hj Hij Heq. apply Hij. rewrite (NoDup_nth l d) in Hnd.
  now apply (Hnd i j).
Qed.

(* The position of a in the list l, syntactically. *)
Ltac index a l := lazymatch l with
  | a :: _ => constr:(0%nat)
  | _ :: ?l' => let n := index a l' in constr:(S n)
  end.

(* Blocks of a list without duplicates are distinct: found by their positions, so it
   takes one lemma. *)
Ltac distinct Hnodup := lazymatch goal with |- ?a <> ?b =>
  lazymatch type of Hnodup with NoDup ?l =>
    let i := index a l in let j := index b l in
    change (nth i l a <> nth j l a); apply nodup_nth_neq;
      [ apply Hnodup
      | apply Nat.ltb_lt; reflexivity
      | apply Nat.ltb_lt; reflexivity
      | discriminate ]
  end end.

(* Two blocks are distinct, from the list. Disequalities of blocks are not kept as
   hypotheses: lia would split on each of them. *)
Ltac neq Hnodup := distinct Hnodup.

(* Pack the facts of the representation, kept whole. *)
Ltac pack B := exists B;
  repeat match goal with |- _ /\ _ => split; [solve [reflexivity | assumption] |] end;
  assumption.

(* Rewrite the int operations of the goal with the equations in the context that
   compute them, like shr_key. *)
Ltac ints := cbv beta; repeat match goal with H: ?a = Int.repr _ |- context [?a] =>
  lazymatch a with Int.repr _ => fail | _ => progress rewrite H end end.

(* An index that is a literal key, as a natural number. *)
Ltac key_index := repeat match goal with
  |- context [Ptrofs.of_ints (Int.repr (key ?l))] =>
  change (Ptrofs.of_ints (Int.repr (key l)))
    with (Ptrofs.of_ints (Int.repr (Z.of_nat (lit_key l)))) end.

(* The offset of an array entry, as computed by C, is 4 times its index. *)
Ltac ofs := change (sizeof _ Ctypesdefs.tint) with 4; cbn [ptrofs_of_int cast_int_int];
  ints; key_index; rewrite index_ofs by (unfold key in *; lia); reflexivity.

(* Facts about the memory before the store Hst hold after it in other blocks and at
   other offsets. *)
Ltac carry Hst Hnodup := match type of Hst with Mem.store _ ?m _ _ _ = Some ?m' =>
  repeat match goal with
  | H: Arr m ?b ?n ?t |- _ => let H' := fresh H in
    (* the array stored to keeps no fact: arr_store gives its new one *)
    lazymatch type of Hst with Mem.store _ _ ?b' _ _ = _ =>
      tryif constr_eq b b' then fail else idtac end;
    assert (H': Arr m' b n t)
      by (apply (arr_store_other H Hst); neq Hnodup);
    clear H; rename H' into H
  | H: exists (t: nat -> Z), Arr m ?b ?n t /\ @?P t |- _ => let H' := fresh H in
    (* a table that only a property describes, as several of the representation *)
    lazymatch type of Hst with Mem.store _ _ ?b' _ _ = _ =>
      tryif constr_eq b b' then fail else idtac end;
    let T := eval cbv beta in (exists (t: nat -> Z), Arr m' b n t /\ P t) in
    assert (H': T) by (apply (arr_ex_store_other H Hst); neq Hnodup);
    clear H; rename H' into H
  | H: Fld m ?b ?o ?c ?v |- _ => let H' := fresh H in
    assert (H': Fld m' b o c v)
      by (apply (fld_store_other H Hst);
          (* the same block: the offsets are apart; another block: it is distinct *)
          lazymatch type of Hst with Mem.store _ _ ?b' _ _ = _ =>
            tryif constr_eq b b'
            then (right; unfold Mptr; cbv [Archi.ptr64]; cbn [size_chunk];
                  first [ left; apply Z.leb_le; reflexivity
                        | right; apply Z.leb_le; reflexivity
                        | lia ])
            else (left; neq Hnodup)
          end);
    clear H; rename H' into H
  end end.

(* Evaluating expressions: temporaries, constants, operators, struct fields and array
   entries. *)
(* Load an array entry or a field: the shape of the address tells which, and its block
   which fact to use, so that no unification with a wrong fact (expensive on offsets)
   is tried. *)
Ltac ld := lazymatch goal with
  | |- Mem.loadv _ _ (Vptr ?b (Ptrofs.add _ (Ptrofs.mul _ _))) = _ =>
    cbn [ptrofs_of_int cast_int_int]; ints; key_index;
    lazymatch goal with
    | |- context [Ptrofs.of_ints (Int.repr (Z.of_nat _))] =>
      match goal with A: Arr _ b _ _ |- _ =>
        eapply (arr_loadv A); unfold key in *; lia end
    | |- _ =>
      fail "the index is not of the form Int.repr (Z.of_nat k): add an equation for ints"
    end
  | |- Mem.loadv _ _ (Vptr ?b _) = _ =>
    match goal with |- context [Ptrofs.repr ?d] =>
      let d' := eval vm_compute in d in change d with d' end;
    match goal with F: Fld _ b _ _ _ |- _ =>
      eapply fld_loadv; [reflexivity | apply F | vm_compute; congruence] end
  end.

(* Look up a temporary, in a temporary environment that may be partly unknown (in
   loops). *)
Ltac tmp := repeat first [rewrite PTree.gss | rewrite PTree.gso by discriminate];
  first [match goal with H: ?le ! ?i = Some _ |- ?le ! ?i = _ => apply H end
        | reflexivity].

Ltac ev := match goal with
  | |- eval_expr _ _ _ _ (Etempvar _ _) _ => apply eval_Etempvar; tmp
  | |- eval_expr _ _ _ _ (Econst_int _ _) _ => apply eval_Econst_int
  | |- eval_expr _ _ _ _ (Ebinop _ _ _ _) _ =>
    eapply eval_Ebinop; [ev | ev | reflexivity]
  | |- eval_expr _ _ _ _ (Eunop _ _ _) _ => eapply eval_Eunop; [ev | reflexivity]
  | |- eval_expr _ _ _ _ (Ecast _ _) _ => eapply eval_Ecast; [ev | reflexivity]
  | |- eval_expr _ _ _ _ (Efield _ _ _) _ =>
    eapply eval_Elvalue; [evl | eapply deref_loc_value; [reflexivity | ld]]
  | |- eval_expr _ _ _ _ (Ederef _ _) _ =>
    eapply eval_Elvalue; [evl | eapply deref_loc_value; [reflexivity | ld]]
  end
with evl := match goal with
  | |- eval_lvalue _ _ _ _ (Efield _ _ _) _ _ _ =>
    eapply eval_Efield_struct;
      [eapply eval_Elvalue; [eapply eval_Ederef; ev | apply deref_loc_copy; reflexivity]
      | reflexivity | reflexivity | reflexivity]
  | |- eval_lvalue _ _ _ _ (Ederef _ _) _ _ _ => eapply eval_Ederef; ev
  end.

(* Close the continuation of a statement that ended normally, or abruptly. *)
Ltac normal := cbv beta; lazymatch goal with
  | |- SeqK _ _ _ _ _ Out_normal => apply seqk_normal
  | |- _ => idtac
  end.
Ltac abrupt := cbv beta; lazymatch goal with
  | |- SeqK _ _ _ _ _ _ => apply seqk_abrupt; [discriminate | ]
  | |- _ => idtac
  end.

(* Leave the statements around a return, and the loop it is in. *)
Ltac ret := cbv beta; repeat (apply seqk_abrupt; [discriminate | ]);
  try (apply loopk_return; cbv beta; repeat (apply seqk_abrupt; [discriminate | ])).

(* Running straight-line code: sequences and assignments of temporaries. *)
Ltac run := repeat match goal with
  | |- Exec _ _ _ (Ssequence _ _) _ => apply exec_seq
  | |- Exec _ _ _ (Sset _ _) _ => eapply exec_set; [ev | cbn [cast_int_int]; try normal]
  | |- Exec _ _ _ Sskip _ => apply exec_skip; try normal
  end.

(* An array that a store updated holds the updated table. *)
Ltac arr_tset := eapply arr_ext; [eassumption | ];
  let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; rewrite tget_tset;
  match goal with |- context [Nat.eq_dec ?a j] =>
    destruct (Nat.eq_dec a j), (Nat.eqb_spec a j) end;
  (reflexivity || congruence).

(* Evaluate the arguments of a call. *)
Ltac evs := first [apply eval_Enil | eapply eval_Econs; [ev | reflexivity | evs]].

(* The negation of a literal flips the lowest bit of its key. *)
Lemma xor_key: forall (l: Lit), 0 <= key l < small_bound ->
  Int.xor (Int.repr (key l)) (Int.repr 1) = Int.repr (key (Neg.neg l)).
Proof.
  intros l Hl. unfold Int.xor.
  rewrite !Int.unsigned_repr by (unfold Int.max_unsigned; simpl; lia). f_equal.
  assert (Heven: forall (p: Z), Z.lxor (2 * p) 1 = 2 * p + 1).
  { intros p. symmetry. apply Z.add_nocarry_lxor. change 1 with (Z.ones 1).
    rewrite Z.land_ones by lia. rewrite Z.mul_comm. now apply Z_mod_mult. }
  unfold key. destruct l as [p|p]; cbn [lit_key Neg.neg].
  - rewrite Nat2Z.inj_succ, Nat2Z.inj_mul, <- Z.add_1_r. apply Heven.
  - rewrite Nat2Z.inj_succ, Nat2Z.inj_mul, <- Z.add_1_r, <- Heven, Z.lxor_assoc,
      Z.lxor_nilpotent.
    apply Z.lxor_0_r.
Qed.

(* Unpack the arrays given by some table, so that stores carry them, and pack them
   again. *)
Ltac unpack := repeat match goal with H: exists (t: nat -> Z), Arr _ _ _ t /\ _ |- _ =>
  let t := fresh "t" in let A := fresh "A" in let Ht := fresh "Ht" in
  destruct H as (t & A & Ht) end.

Ltac repack := eexists; split; [eassumption | assumption].

(* Drop the facts about the memory m, which a call replaced. *)
Ltac forget_mem m := repeat match goal with
  | H: Arr m _ _ _ |- _ => clear H
  | H: Fld m _ _ _ _ |- _ => clear H
  end.

(* Keep only the facts about the memory m, the one after a call. *)
Ltac keep_mem m := repeat match goal with
  | H: Arr ?mm _ _ _ |- _ => tryif constr_eq mm m then fail else clear H
  | H: Fld ?mm _ _ _ _ |- _ => tryif constr_eq mm m then fail else clear H
  end.

(* Carry the facts about the memory before a call that left P unchanged, as Hun says,
   over to the memory after it, for the blocks that P covers. *)
Ltac transfer Hun Hnodup := lazymatch type of Hun with Mem.unchanged_on _ ?m ?m' =>
  repeat match goal with
  | H: Arr m ?b ?n ?t |- _ => let H' := fresh H in
    assert (H': Arr m' b n t)
      by (apply (arr_unchanged _ m m' b n t Hun);
          [intros ?; cbv beta; repeat split; neq Hnodup | apply H]);
    clear H; rename H' into H
  | H: Fld m ?b ?o ?c ?v |- _ => let H' := fresh H in
    assert (H': Fld m' b o c v)
      by (apply (fld_unchanged _ m m' b o c v Hun);
          [intros ? ?; cbv beta; repeat split; neq Hnodup | apply H]);
    clear H; rename H' into H
  end end.
