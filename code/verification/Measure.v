From Stdlib Require Import Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Relations.
From Stdlib Require Import Wellfounded.
From Stdlib Require Import Lia.
Import ListNotations.

From Equations Require Import Equations.

From RocqSAT Require Import Atom.
From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import State.

(* The termination measure of an assignment m for a formula f:
     - score m f: per decision level, lowest first, the bound minus its number of propagations;
     - score_total m f: the bound minus the number of assigned literals.
   Propagating and backtracking lower the score, deciding keeps it but lowers score_total. *)

(* The largest atom occurring in a formula (0 if there is none). *)
Definition max_atom_f (f: CNF): nat :=
list_max (map extract (flat_map Clause.elements (CNF.elements f))).

(* Per decision level, newest first: n minus its number of propagations (x counts them so far). *)
Equations score_aux (m: PA) (n x: nat): list nat :=
score_aux ⟨⟩    n x := [n - x];
score_aux ⟨m, l⟩ n x := score_aux m n (S x);
score_aux ⟨m; l⟩ n x := n - x :: score_aux m n 0.

(* l padded with x up to length n. *)
Definition pad (x n: nat) (l: list nat): list nat := l ++ repeat x (n - length l).

(* The scores of all decision levels, lowest first, padded with the bound to a fixed length. *)
Definition score (m: PA) (f: CNF): list nat :=
  pad (S (max_atom_f f)) (S (S (max_atom_f f))) (rev (score_aux m (S (max_atom_f f)) 0)).

(* One more than the largest atom, minus the number of assigned literals. *)
Definition score_total (m: PA) (f: CNF): nat := S (max_atom_f f) - length m.

(* l and l' are at most x long and, after a common prefix, l has the smaller entry. *)
Inductive PrefixLt (x: nat): relation (list nat) :=
| p_head (m m': list nat) (n n': nat):
  length (n :: m) <= x ->
  length (n' :: m') <= x ->
  n < n' ->
  PrefixLt x (n :: m) (n' :: m')
| p_tail (m m': list nat) (n: nat):
  length (n :: m) <= x ->
  length (n :: m') <= x ->
  PrefixLt x m m' ->
  PrefixLt x (n :: m) (n :: m').

(* Lists related by PrefixLt x are at most x long. *)
Lemma prefix_lt_length: forall (x: nat) (l l': list nat), 
  PrefixLt x l l' -> length l <= x.
Proof. intros x l l' H. now destruct H. Qed.

(* A larger bound keeps lists related. *)
Lemma prefix_lt_incl: forall (x y: nat) (l l': list nat),
  x <= y -> PrefixLt x l l' -> PrefixLt y l l'.
Proof.
  intros x y l l' Hle H. induction H as [m m' n n' Hm Hm' Hlt | m m' n Hm Hm' H IH].
  - apply p_head.
    + lia.
    + lia.
    + assumption.
  - apply p_tail.
    + lia.
    + lia.
    + assumption.
Qed.

(* Conversely, any bound that both lists satisfy keeps them related. *)
Lemma prefix_lt_restrict: forall (x y: nat) (l l': list nat),
  PrefixLt y l l' -> length l <= x -> length l' <= x -> PrefixLt x l l'.
Proof.
  intros x y l l' H. induction H as [m m' n n' _ _ Hlt | m m' n _ _ H IH].
  - intros Hm Hm'. now apply p_head.
  - intros Hm Hm'. apply p_tail.
    + assumption.
    + assumption.
    + apply IH.
      * simpl in Hm. lia.
      * simpl in Hm'. lia.
Qed.

(* Below n :: m are lists with a smaller head, or with head n and a tail below m. *)
Lemma prefix_lt_well_founded: forall (x: nat), well_founded (PrefixLt x).
Proof.
  induction x as [|x IH].
  - intros l. constructor. intros l' Hlt. destruct Hlt; simpl in *; lia.
  - intros [|n m].
    + constructor. intros l' Hlt. inversion Hlt.
    + revert m. induction n as [n IHn] using (well_founded_ind lt_wf).
      intros m. induction (IH m) as [m _ IHm].
      constructor. intros l' Hlt. inversion Hlt as [m' ? n' ? _ _ Hn | m' ? ? Hm' Hm Hlt']; subst.
      * now apply IHn.
      * apply IHm. apply prefix_lt_restrict with (S x).
        -- assumption.
        -- simpl in Hm'. lia.
        -- simpl in Hm. lia.
Qed.

(* A flag that puts fail below every state, then the score and score_total. *)
Equations state_measure (s: State): nat * (list nat * nat) :=
state_measure fail        := (0, ([]       , 0              ));
state_measure (state m f) := (1, (score m f, score_total m f)).

(* s >>[f] s': s' has a smaller measure than s, compared lexicographically. *)
Definition StateLt (f: CNF): relation State :=
  MR (slexprod _ _ lt (slexprod _ _ (PrefixLt (S (S (max_atom_f f)))) lt)) state_measure.

Notation "s '>>[' f ']' s'" := (StateLt f s' s) (at level 40, format "s '/ ' '[' >>[ ']' f ] '/ ' s'").

Lemma state_lt_well_founded: forall (f: CNF), well_founded (StateLt f).
Proof.
  intros f. apply wf_MR. apply wf_slexprod.
  - apply lt_wf.
  - apply wf_slexprod.
    + apply prefix_lt_well_founded.
    + apply lt_wf.
Qed.

(* Every element of a list is at most its maximum. *)
Lemma in_le_list_max: forall (l: list nat) (x: nat), In x l -> x <= list_max l.
Proof. intros l. apply Forall_forall. now apply list_max_le. Qed.

(* Every atom occurring in f is at most max_atom_f f. *)
Lemma max_atom_f_le: forall (f: CNF) (c: Clause) (l: Lit) (p: Atom),
  Clause.In l c -> CNF.In c f -> extract l = p -> p <= max_atom_f f.
Proof.
  intros f c l p Hl_in_c Hc_in_f <-. unfold max_atom_f. apply in_le_list_max. apply in_map. apply in_flat_map.
  apply CNF.elements_spec1 in Hc_in_f. apply SetoidList.InA_alt in Hc_in_f as [c' [Hequal Hc'_in_f]].
  exists c'. split.
  - assumption.
  - apply Hequal, Clause.elements_spec1 in Hl_in_c. now apply SetoidList.InA_alt in Hl_in_c as [l' [<- Hin]].
Qed.

(* Pigeonhole principle: distinct numbers that are all at most m are at most m + 1 many. *)
Lemma nodup_length_le: forall (l: list nat) (m: nat),
  NoDup l ->
  (forall (n: nat), In n l -> n <= m) ->
  length l <= S m.
Proof.
  intros l m Hnodup Hin_le. transitivity (length (seq 0 (S m))).
  - apply NoDup_incl_length.
    + assumption.
    + intros n Hin. apply in_seq. apply Hin_le in Hin. lia.
  - now rewrite length_seq.
Qed.

(* A well-formed trail assigns distinct atoms of f, so it has at most max_atom_f f + 1 literals. *)
Lemma well_formed_length_le: forall (m: PA) (f: CNF),
  WellFormed (state m f) ->
  length m <= S (max_atom_f f).
Proof.
  intros m f [Hnodup Hbounded]. transitivity (length (map extract (map fst m))).
  - now repeat rewrite length_map.
  - apply nodup_length_le.
    + assumption.
    + intros p Hin. rewrite map_map in Hin. apply in_map_iff in Hin as [[l a] [<- Hin]].
      apply Hbounded in Hin as [c [Hc_in_f [Hl_in_c|Hnegl_in_c]]].
      * now apply max_atom_f_le with c l.
      * apply max_atom_f_le with c (¬l).
        -- assumption.
        -- assumption.
        -- now rewrite Neg.extract_neg.
Qed.

(* score_aux has one entry per decision, plus one for decision level 0. *)
Lemma score_aux_length: forall (m: PA) (n n': nat),
  length (score_aux m n n') <= S (length m).
Proof.
  intros. funelim (score_aux m n n').
  - simpl in *. lia.
  - simpl in *. lia.
  - simpl in *. lia.
Qed.

(* For a well-formed assignment, the unpadded score is at most as long as the padded one. *)
Lemma score_aux_length_well_formed: forall (m: PA) (f: CNF) (n x: nat),
  WellFormed (state m f) -> length (score_aux m n x) <= S (S (max_atom_f f)).
Proof.
  intros m f n x Hwf. transitivity (S (length m)).
  - apply score_aux_length.
  - apply well_formed_length_le in Hwf. lia.
Qed.

(* Below a well-formed literal, the score has room for one more entry. *)
Lemma score_aux_length_tail: forall (m: PA) (f: CNF) (l: Lit) (a: Ann) (n x: nat),
  WellFormed (state (add m l a) f) -> length (score_aux m n x) <= S (max_atom_f f).
Proof.
  intros m f l a n x Hwf. transitivity (S (length m)).
  - apply score_aux_length.
  - now apply well_formed_length_le in Hwf.
Qed.

(* Every entry of score_aux is at most the bound n. *)
Lemma score_aux_le_bound: forall (m: PA) (n x k: nat),
  In k (score_aux m n x) -> k <= n.
Proof.
  intros m n x k Hin. funelim (score_aux m n x).
  - simp score_aux in Hin. inversion Hin.
    + lia.
    + inversion H.
  - rewrite <- Heqcall in Hin. inversion Hin.
    + lia.
    + now apply H.
  - rewrite <- Heqcall in Hin. now apply H.
Qed.

(* A decision does not change the score: the new level adds an entry equal to the padding value. *)
Lemma score_decide: forall (m: PA) (f: CNF) (l: Lit),
  WellFormed (state ⟨m; l⟩ f) ->
  score ⟨m; l⟩ f = score m f.
Proof.
  intros m f l Hwf. unfold score, pad. simp score_aux. simpl rev.
  rewrite length_app, length_rev, <- app_assoc. simpl length. f_equal.
  rewrite Nat.add_1_r, Nat.sub_succ. symmetry. rewrite Nat.sub_succ_l.
  - reflexivity.
  - now apply score_aux_length_tail with l dec.
Qed.

(* A decision does decrease score_total, since it assigns one more literal. *)
Lemma score_total_decide: forall (m: PA) (f: CNF) (l: Lit),
  WellFormed (state ⟨m; l⟩ f) ->
  score_total ⟨m; l⟩ f < score_total m f.
Proof.
  intros m f l Hwf. apply well_formed_length_le in Hwf.
  unfold score_total. simpl length in *. lia.
Qed.

(* Padding with an entry n that is at least all entries keeps lists related. *)
Lemma prefix_lt_pad: forall (l1 l2: list nat) (m n x x': nat),
  (forall (k: nat), In k l1 -> k <= n) ->
  (forall (k: nat), In k l2 -> k <= n) ->
  length l1 + x  <= m ->
  length l2 + x' <= m ->
  PrefixLt m l1 l2 -> PrefixLt m (l1 ++ repeat n x) (l2 ++ repeat n x').
Proof.
  intros l1 l2 m n x x' Hin_l1 Hin_l2 Hle_l1 Hle_l2 Hlt. 
  induction Hlt as [l1 l2 a1 a2 _ _ Hlt|l1 l2 a _ _ _ IH].
  - simpl. apply p_head.
    + simpl. rewrite length_app. now rewrite repeat_length.
    + simpl. rewrite length_app. now rewrite repeat_length.
    + assumption.
  - simpl. apply p_tail.
    + simpl. rewrite length_app. now rewrite repeat_length.
    + simpl. rewrite length_app. now rewrite repeat_length.
    + apply IH.
      * intros. apply Hin_l1. now right.
      * intros. apply Hin_l2. now right.
      * simpl in *. lia.
      * simpl in *. lia.
Qed.

(* Lists that start with the same entries are related when their rests are. *)
Lemma prefix_lt_app_l: forall (m1 m2 n: list nat) (x: nat),
  length (n ++ m1) <= x ->
  length (n ++ m2) <= x ->
  PrefixLt x m1 m2 ->
  PrefixLt x (n ++ m1) (n ++ m2).
Proof. 
  intros m1 m2 n. generalize dependent m1. generalize dependent m2.
  induction n.
  - now intros.
  - intros. simpl in *. apply p_tail.
    + assumption.
    + assumption.
    + apply IHn.
      * lia.
      * lia.
      * assumption.
Qed.

(* More propagations on the newest level give a smaller score. *)
Lemma score_aux_more_props: forall (m: PA) (f: CNF) (x: nat),
  WellFormed (state m f) ->
  x + length m <= max_atom_f f ->
  PrefixLt (S (S (max_atom_f f))) 
           (rev (score_aux m (S (max_atom_f f)) (S x)))
           (rev (score_aux m (S (max_atom_f f)) x)).
Proof.
  intros m f x Hwf Hle. generalize dependent x.
  induction m as [|m IH l [|]].
  - intros. simp score_aux. simpl. destruct x; apply p_head; simpl in *; lia.
  - intros. simp score_aux. simpl rev. apply prefix_lt_app_l.
    + rewrite length_app, length_rev, Nat.add_1_r. apply le_n_S.
      now apply score_aux_length_tail with l dec.
    + rewrite length_app, length_rev, Nat.add_1_r. apply le_n_S.
      now apply score_aux_length_tail with l dec.
    + destruct x; apply p_head; simpl in *; lia.
  - intros. simp score_aux. apply IH.
    + now apply well_formed_tail in Hwf.
    + simpl in *. lia.
Qed.

(* Extending the larger of two related lists keeps them related. *)
Lemma prefix_lt_app_r: forall (m1 m2 n: list nat) (x: nat),
  length (m2 ++ n) <= x ->
  PrefixLt x m1 m2 ->
  PrefixLt x m1 (m2 ++ n).
Proof.
  intros m1 m2. generalize dependent m1.
  induction m2.
  - intros m1 n x Hle Hlt. inversion Hlt.
  - intros m1 n x Hle Hlt. destruct m1.
    + inversion Hlt.
    + simpl. inversion Hlt.
      * now apply p_head.
      * apply p_tail.
        -- assumption.
        -- assumption.
        -- apply IHm2.
          ++ rewrite length_app in *. simpl in *. lia.
          ++ assumption.
Qed.

(* A decision splits the score into the parts before and after it. *)
Lemma score_aux_split: forall (m1 m2: PA) (l: Lit) (n x: nat),
  score_aux ⟨m1; l ++ m2⟩ n x = (score_aux m2 n x) ++ (score_aux m1 n 0).
Proof.
  intros m1 m2 l n. induction m2 as [|m2 IH l' [|]].
  - intros x. now simp score_aux.
  - intros x. simpl. simp score_aux. simpl. now rewrite IH.
  - intros x. simpl. simp score_aux.
Qed.

(* For well-formed assignments, scores compare like their unpadded versions. *)
Lemma prefix_lt_score: forall (m m': PA) (f: CNF),
  WellFormed (state m f) ->
  WellFormed (state m' f) ->
  PrefixLt (S (S (max_atom_f f)))
           (rev (score_aux m (S (max_atom_f f)) 0))
           (rev (score_aux m' (S (max_atom_f f)) 0)) ->
  PrefixLt (S (S (max_atom_f f))) (score m f) (score m' f).
Proof.
  intros m m' f Hwf Hwf' Hlt. unfold score, pad. apply prefix_lt_pad.
  - intros k Hin. rewrite <- in_rev in Hin. now apply score_aux_le_bound in Hin.
  - intros k Hin. rewrite <- in_rev in Hin. now apply score_aux_le_bound in Hin.
  - rewrite length_rev, Nat.add_comm, Nat.sub_add.
    + apply le_n.
    + now apply score_aux_length_well_formed.
  - rewrite length_rev, Nat.add_comm, Nat.sub_add.
    + apply le_n.
    + now apply score_aux_length_well_formed.
  - assumption.
Qed.

(* A propagation decreases the score: it lowers the entry of the newest level. *)
Lemma score_propagate: forall (m: PA) (f: CNF) (l: Lit),
  WellFormed (state ⟨m, l⟩ f) ->
  PrefixLt (S (S (max_atom_f f))) (score ⟨m, l⟩ f) (score m f).
Proof.
  intros m f l Hwf. apply prefix_lt_score.
  - assumption.
  - now apply well_formed_tail in Hwf.
  - simp score_aux. apply score_aux_more_props.
    + now apply well_formed_tail in Hwf.
    + apply well_formed_length_le in Hwf. simpl in *. lia.
Qed.

(* Backtracking decreases the score: it lowers the entry of the level before the decision. *)
Lemma score_backtrack: forall (m n: PA) (f: CNF) (l l': Lit),
  WellFormed (state ⟨m, l⟩ f) ->
  WellFormed (state ⟨m; l' ++ n⟩ f) ->
  PrefixLt (S (S (max_atom_f f))) (score ⟨m, l⟩ f) (score ⟨m; l' ++ n⟩ f).
Proof.
  intros m n f l l' Hwf Hwf'. apply prefix_lt_score.
  - assumption.
  - assumption.
  - rewrite score_aux_split. rewrite rev_app_distr. simp score_aux. apply prefix_lt_app_r.
    + rewrite length_app. repeat rewrite length_rev.
      rewrite Nat.add_comm, <- length_app, <- score_aux_split with (l := l').
      now apply score_aux_length_well_formed.
    + apply score_aux_more_props.
      * now apply well_formed_tail in Hwf.
      * apply well_formed_length_le in Hwf. simpl in Hwf. lia.
Qed.

(* Hence StateLt only grows with the largest atom of the formula. *)
Lemma state_lt_incl: forall (f g: CNF) (s s': State),
  max_atom_f f <= max_atom_f g -> s >>[f] s' -> s >>[g] s'.
Proof.
  intros f g s s' Hle Hlt. unfold StateLt, MR in *.
  destruct (state_measure s') as [b [l t]], (state_measure s) as [b' [l' t']].
  inversion Hlt as [? ? ? ? Hflag | ? ? ? Hlex]; subst.
  - now apply left_slex.
  - apply right_slex. inversion Hlex as [? ? ? ? Hprefix | ? ? ? Htotal]; subst.
    + apply left_slex. apply prefix_lt_incl with (S (S (max_atom_f f))).
      * lia.
      * assumption.
    + now apply right_slex.
Qed.

(* The score is at least the padded length long, and exactly that long if well-formed. *)
Lemma score_length_ge: forall (m: PA) (f: CNF), S (S (max_atom_f f)) <= length (score m f).
Proof. intros m f. unfold score, pad. rewrite length_app, repeat_length. lia. Qed.

Lemma score_length_well_formed: forall (m: PA) (f: CNF),
  WellFormed (state m f) -> length (score m f) = S (S (max_atom_f f)).
Proof.
  intros m f Hwf. unfold score, pad. rewrite length_app, repeat_length, length_rev, Nat.add_comm, Nat.sub_add.
  - reflexivity.
  - now apply score_aux_length_well_formed.
Qed.

(* A decreasing step from a well-formed state never increases the largest atom. *)
Lemma state_lt_max_atom: forall (m m': PA) (f f': CNF),
  WellFormed (state m f) -> state m f >>[f] state m' f' -> max_atom_f f' <= max_atom_f f.
Proof.
  intros m m' f f' Hwf Hlt. unfold StateLt, MR in Hlt. simp state_measure in Hlt.
  inversion Hlt as [? ? ? ? Hflag | ? ? ? Hlex]; subst.
  - lia.
  - apply le_S_n, le_S_n. transitivity (length (score m' f')).
    + apply score_length_ge.
    + remember (score m' f', score_total m' f') as p' eqn:Hp'.
      remember (score m f, score_total m f) as p eqn:Hp.
      destruct Hlex as [l l' t t' Hprefix | l t t' Htotal].
      * injection Hp' as -> _. now apply prefix_lt_length in Hprefix.
      * injection Hp' as -> _. injection Hp as Hscore _. rewrite Hscore.
        now rewrite score_length_well_formed.
Qed.
