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

Ltac slia := simpl in *; lia.

(* The largest atom occurring in a clause, or in a formula (0 if there is none). *)
Definition max_atom_c (c: Clause): nat :=
list_max (map extract (Clause.elements c)).

Definition max_atom_f (f: CNF): nat :=
list_max (map max_atom_c (CNF.elements f)).

(* Walking from the most recent entry: for each decision level, the bound n minus the number of propagated literals at that level (x counts the propagations seen so far on the current level). *)
Equations score_aux (m: PA) (n x: nat): list nat :=
score_aux []        n x := [n - x];
score_aux (m ++p l) n x := score_aux m n (S x);
score_aux (m ++d l) n x := n - x :: score_aux m n 0.

(* The scores of all decision levels, oldest first, padded with the bound to a fixed length so that scores of different assignments are comparable. *)
Equations score (m: PA) (f: CNF): list nat :=
score m f :=
  let max_atom := max_atom_f f in
  let unpadded := rev (score_aux m (S max_atom) 0) in
  let  padding := repeat (S max_atom) (S (S max_atom) - length unpadded) in
  unpadded ++ padding.

(* One more than the largest atom, minus the number of assigned literals. *)
Equations score_total (m: PA) (f: CNF): nat :=
score_total m f := S (max_atom_f f) - length m.

(* fail is below every other state. *)
Inductive FailLt: relation State :=
| f_fail (m: PA) (f: CNF):
  FailLt fail (state m f).

Lemma fail_lt_well_founded: well_founded FailLt.
Proof.
  unfold well_founded. intros m. constructor. intros m' Hlt. destruct Hlt.
  constructor. intros m' Hlt. inversion Hlt.
Qed.

(* Lexicographic order on lists of length at most x. *)
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

(* Lexicographic order on lists; bcll additionally bounds the lengths, which makes it well-founded. *)
Inductive cll: relation (list nat) :=
| hd_less (n n': nat) (m m': list nat):
  n < n' ->
  cll (n :: m) (n' :: m')
| tl_less (n: nat) (m m': list nat):
  cll m m' ->
  cll (n :: m) (n :: m').

Definition bcll (n: nat) (m m': list nat): Prop :=
  length m <= n /\ length m' <= n /\ cll m m'.

Lemma bcll__prefix_lt: forall (x: nat) (m m': list nat),
  bcll x m m' <-> PrefixLt x m m'.
Proof.
  intros. split.
  - intros. inversion H as [H1 [H2 H3]]. induction H3.
    + apply (p_head _ _ _ _ _ H1 H2 H0).
    + apply (p_tail _ _ _ _ H1 H2). apply IHcll.
      * unfold bcll. split.
        -- slia.
        -- split. 
          ++ slia.
          ++ assumption.
      * slia.
      * slia.
  - intros. 
    + induction H.
      * unfold bcll. intuition. now apply hd_less.
      * unfold bcll. intuition. apply tl_less. now destruct IHPrefixLt.
Qed.

(* Encoding of bounded lists as a head and a tail, used to prove bcll well-founded. *)
Definition list_to_sum (n: nat) (m: list nat): nat * list nat + unit :=
  if List.length m <=? n then
  match m with
  | nil => inr tt
  | h :: t => inl (h, t)
  end else inr tt.

Definition bcll' (n: nat) (m m': list nat): Prop :=
  le_AsB _ _ (slexprod _ _ lt (bcll n)) (fun _ _ => False) (list_to_sum (S n) m) (list_to_sum (S n) m').

Lemma cll_incl {n} (m m': list nat): bcll (S n) m m' -> bcll' n m m'.
Proof.
  intros [Hl1 [Hl2 H]]. unfold bcll'. unfold list_to_sum.
  rewrite 2 leb_correct; auto.
  destruct H; constructor.
  + constructor 1. auto.
  + constructor 2. simpl in *; split; [| split]; auto; lia.
Qed.

Lemma bcll_well_founded: forall (x: nat), well_founded (bcll x).
Proof.
  induction x.
  - intros l. constructor. intros [] [H1 [H2 H3]].
    + inversion H3.
    + slia.
  - apply (wf_incl _ _ (fun l1 l2 => bcll' x l1 l2)).
    + red. apply cll_incl.
    + unfold bcll'.
      apply wf_inverse_image.
      apply wf_disjoint_sum.
      * apply wf_slexprod.
        -- apply lt_wf.
        -- apply IHx.
      * constructor; intros ? [].
Qed.

Lemma prefix_lt_well_founded: forall x, well_founded (PrefixLt x).
Proof.
  intro x. apply (wf_incl _ _ (bcll x)).
  - unfold inclusion. now apply bcll__prefix_lt.
  - apply bcll_well_founded.
Qed.

Definition TotalLt: relation nat := lt.

Lemma total_lt_well_founded: well_founded TotalLt.
Proof. apply lt_wf. Qed.

(* Measures are compared lexicographically: first by score, then by score_total. *)
Definition StateLexLt (f: CNF): relation (list nat * nat) :=
  slexprod _ _ (PrefixLt (S (S (max_atom_f f)))) TotalLt.

Lemma state_lex_lt_well_founded: forall (f: CNF), well_founded (StateLexLt f).
Proof.
  intros. apply wf_slexprod.
  - apply prefix_lt_well_founded.
  - apply total_lt_well_founded.
Qed.

(* The measure of a state: its score and score_total. *)
Equations state_measure (s: State): list nat * nat :=
state_measure fail          := ([]       , 0              );
state_measure (state m f)   := (score m f, score_total m f).

(* StateLt f s' s, written s >>[f] s': s' is fail and s is not, or s' has a smaller measure than s. *)
Definition StateLt (f: CNF): relation State := union _ FailLt (MR (StateLexLt f) state_measure).
Definition StateLtTransClos (f: CNF): relation State := clos_trans _ (StateLt f).

Notation "s '>>[' f ']' s'" := (StateLt f s' s) (at level 40, format "s '/ ' '[' >>[ ']' f ] '/ ' s'").
Notation "s '>>+[' f ']' s'" := (StateLtTransClos f s' s) (at level 40, format "s '/ ' '[' >>+[ ']' f ] '/ ' s'").

Lemma state_lt_well_founded: forall (f: CNF), well_founded (StateLt f).
Proof.
  intros. apply wf_union.
  - unfold commut. intros. inversion H. subst. exists (state m f0).
    + unfold MR in H0. simp state_measure in H0. inversion H0.
      * subst. inversion H3.
      * subst. inversion H3.
    + unfold MR in H0. simp state_measure in H0. inversion H0.
      * subst. inversion H3.
      * subst. inversion H3.
  - apply fail_lt_well_founded.
  - apply wf_MR. apply state_lex_lt_well_founded.
Qed.

Lemma in_le_list_max: forall (l: list nat) (x: nat), In x l -> x <= list_max l.
Proof. intros l. apply Forall_forall. now apply list_max_le. Qed.

(* Every atom occurring in c is at most max_atom_c c. *)
Lemma max_atom_c_le: forall (c: Clause) (l: Lit) (p: Atom),
  Clause.In l c -> extract l = p -> p <= max_atom_c c.
Proof.
  intros c l p Hl_in_c <-. unfold max_atom_c. apply in_le_list_max. apply in_map.
  apply Clause.elements_spec1 in Hl_in_c. now apply SetoidList.InA_alt in Hl_in_c as [l' [<- Hin]].
Qed.

(* Every atom occurring in f is at most max_atom_f f. *)
Lemma max_atom_f_le: forall (f: CNF) (c: Clause) (l: Lit) (p: Atom),
  Clause.In l c -> CNF.In c f -> extract l = p -> p <= max_atom_f f.
Proof.
  intros f c l p Hl_in_c Hc_in_f Heq.
  apply CNF.elements_spec1 in Hc_in_f. apply SetoidList.InA_alt in Hc_in_f as [c' [Hequal Hc'_in_f]].
  apply Hequal in Hl_in_c. transitivity (max_atom_c c').
  - now apply max_atom_c_le with l.
  - unfold max_atom_f. apply in_le_list_max. now apply in_map.
Qed.

(* Hence every atom on a well-formed trail is at most max_atom_f f. *)
Lemma well_formed_atom_le: forall (m: PA) (f: CNF) (p: Atom),
  WellFormed (state m f) ->
  In p (map extract (map fst m)) ->
  p <= max_atom_f f.
Proof.
  intros m f p Hwf Hin. apply in_map_iff in Hin as [l [Heq Hin]].
  apply in_map_iff in Hin as [(l', a) [Heq' Hin]]. simpl in Heq'. subst l'.
  destruct Hwf as [Hnodup Hbounded]. apply Hbounded in Hin as [c [Hc_in_f [Hl_in_c|Hnegl_in_c]]].
  - destruct l as [p'|p'].
    + simp extract in Heq. subst p'. now apply (max_atom_f_le f c (Pos p)).
    + simp extract in Heq. subst p'. now apply (max_atom_f_le f c (Neg p)).
  - destruct l as [p'|p'].
    + simp extract in Heq. subst p'. now apply (max_atom_f_le f c (Neg p)).
    + simp extract in Heq. subst p'. now apply (max_atom_f_le f c (Pos p)).
Qed.

(* Pigeonhole principle: distinct numbers that are all at most m are at most m + 1 many. *)
Lemma pigeon: forall (l: list nat) (m: nat),
  NoDup l ->
  (forall (n: nat), In n l -> n <= m) ->
  length l <= S m.
Proof.
  intros l m Hnodup Hin_le.
  assert (Hincl: incl l (seq 0 (S m))).
  - unfold incl. intros n Hin. apply in_seq. specialize (Hin_le n Hin). lia.
  - apply (@NoDup_incl_length _ _ (seq 0 (S m))) in Hnodup.
    + now rewrite length_seq in Hnodup.
    + assumption.
Qed.

(* So a well-formed trail has at most max_atom_f f + 1 literals. *)
Lemma well_formed_length_le: forall (m: PA) (f: CNF),
  WellFormed (state m f) ->
  length m <= S (max_atom_f f).
Proof.
  intros m f Hwf. assert (Heq: length m = length (map extract (map fst m))).
  - now repeat rewrite length_map.
  - rewrite Heq. apply pigeon.
    + now destruct Hwf.
    + intros. apply (well_formed_atom_le m); assumption.
Qed.

Lemma score_aux_length: forall (m: PA) (n n': nat),
  length (score_aux m n n') <= S (length m).
Proof.
  intros. funelim (score_aux m n n').
  - slia.
  - slia.
  - slia.
Qed.

Lemma score_aux_length_le: forall (m: PA) (f: CNF) (l: Lit) (a: Ann) (n x: nat),
  WellFormed (state ((l, a) :: m) f) ->
  length (score_aux m n x) <= S (max_atom_f f).
Proof.
  intros. 
  pose proof (score_aux_length m n x).
  pose proof (score_aux_length (m ++d l) n x).
  pose proof (well_formed_length_le ((l, a) :: m) f H).
  slia.
Qed.

Lemma score_aux_in_le: forall (m: PA) (n x k: nat),
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
Lemma score_dec: forall (m: PA) (f: CNF) (l: Lit),
  WellFormed (state (m ++d l) f) ->
  score (m ++d l) f = score m f.
Proof.
  intros. simp score. simpl. simp score_aux. simpl.
  rewrite length_app. simpl. rewrite Nat.add_1_r. rewrite <- app_assoc.
  destruct (length (rev (score_aux m (S (max_atom_f f)) 0))) eqn:G.
  - reflexivity.
  - destruct n.
    + simp pad. now rewrite Nat.sub_0_r.
    + rewrite length_rev in G. 
      pose proof (score_aux_length_le m f l dec (S (max_atom_f f)) 0 H).
      assert (T: S (max_atom_f f - S n) = max_atom_f f - n).
      * lia.
      * now rewrite <- T.
Qed.

(* A decision does decrease score_total, since it assigns one more literal. *)
Lemma total_decide: forall (m: PA) (f: CNF) (l: Lit),
  WellFormed (state (m ++d l) f) ->
  TotalLt (score_total (m ++d l) f) (score_total m f).
Proof.
  intros m f l Hwf. pose proof (well_formed_length_le (m ++d l) f Hwf).
  unfold TotalLt. simp score_total. simpl in *. destruct (length m); lia.
Qed.

Lemma prefix_repeat: forall (l1 l2: list nat) (m n x x': nat),
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
      * slia.
      * slia.
Qed.

Lemma prefix_postfix: forall (m1 m2 n: list nat) (x: nat),
  length (m1 ++a n) <= x ->
  length (m2 ++a n) <= x ->
  PrefixLt x m1 m2 ->
  PrefixLt x (m1 ++a n) (m2 ++a n).
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

Lemma prefix_shift: forall (m: PA) (f: CNF) (x: nat),
  WellFormed (state m f) ->
  x + length m <= max_atom_f f ->
  PrefixLt (S (S (max_atom_f f))) 
           (rev (score_aux m (S (max_atom_f f)) (S x)))
           (rev (score_aux m (S (max_atom_f f)) x)).
Proof.
  intros m f x Hwf Hle. generalize dependent x.
  induction m as [|[l [|]] m IH].
  - intros. simp score_aux. simpl. destruct x eqn:Heq.
    + apply p_head.
      * slia.
      * slia.
      * lia.
    + apply p_head.
      * slia.
      * slia.
      * lia.
  - intros. simp score_aux. simpl. destruct x eqn:Heq.
    * apply prefix_postfix.
      -- pose proof (score_aux_length_le m f l dec (S (max_atom_f f)) 0 Hwf).
         rewrite length_app. rewrite length_rev. slia.
      -- pose proof (score_aux_length_le m f l dec (S (max_atom_f f)) 0 Hwf).
         rewrite length_app. rewrite length_rev. slia.
      -- apply p_head.
        ++ slia.
        ++ slia.
        ++ lia.
    * apply prefix_postfix.
      -- pose proof (score_aux_length_le m f l dec (S (max_atom_f f)) 0 Hwf).
         rewrite length_app. rewrite length_rev. slia.
      -- pose proof (score_aux_length_le m f l dec (S (max_atom_f f)) 0 Hwf).
         rewrite length_app. rewrite length_rev. slia.
      -- apply p_head.
        ++ slia.
        ++ slia.
        ++ lia.
  - intros. simp score_aux. apply IH.
    * now apply well_formed_tail in Hwf.
    * slia.
Qed.

Lemma prefix_prefix: forall (m1 m2 n: list nat) (x: nat),
  length (n ++a m2) <= x ->
  PrefixLt x m1 m2 ->
  PrefixLt x m1 (n ++a m2).
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
          ++ rewrite length_app in *. slia.
          ++ assumption.
Qed.

Lemma score_aux_split: forall (m1 m2: PA) (l: Lit) (n x: nat),
  score_aux (m1 ++d l ++a m2) n x = (score_aux m1 n 0) ++a (score_aux m2 n x).
Proof.
  intros.
  generalize dependent x.
  induction m2.
  - intros. rewrite app_nil_l. simp score_aux. simpl. reflexivity.
  - intros. simpl. destruct a. destruct a.
    + simp score_aux. simpl. now rewrite IHm2.
    + simp score_aux.
Qed.

(* A propagation decreases the score. *)
Lemma prefix_prop: forall (m: PA) (f: CNF) (l: Lit),
  WellFormed (state (m ++p l) f) ->
  PrefixLt (S (S (max_atom_f f))) (score (m ++p l) f) (score m f).
Proof.
  intros m f l Hwf. 
  pose proof (well_formed_tail m f l prop Hwf) as Hwf'. 
  simp score. simpl. apply prefix_repeat.
  - intros. rewrite <- in_rev in H. now apply score_aux_in_le in H.
  - intros. rewrite <- in_rev in H. now apply score_aux_in_le in H.
  - repeat rewrite length_rev.
    destruct (length (score_aux (m ++p l) (S (max_atom_f f)) 0)) eqn:Heq.
    + lia.
    + destruct n.
      * lia.
      * pose proof (score_aux_length (m ++p l) (S (max_atom_f f)) 0).
        pose proof (well_formed_length_le (m ++p l) f Hwf) .
        slia.
  - repeat rewrite length_rev.
    destruct (length (score_aux m (S (max_atom_f f)) 0)) eqn:Heq.
    + lia.
    + destruct n.
      * lia.
      * pose proof (score_aux_length m (S (max_atom_f f)) 0).
        pose proof (well_formed_length_le m f Hwf').
        slia.
  - simp score_aux. apply prefix_shift.
    + assumption.
    + apply well_formed_length_le in Hwf. slia.
Qed.

(* Backtracking, which replaces a decision and everything after it by a propagated literal, decreases the score. *)
Lemma prefix_app: forall (m n: PA) (f: CNF) (l l': Lit),
  WellFormed (state (m ++p l) f) ->
  WellFormed (state (m ++d l' ++a n) f) ->
  PrefixLt (S (S (max_atom_f f))) (score (m ++p l) f) (score (m ++d l' ++a n) f).
Proof.
  intros m n f l l' Hwf Hwf'. simp score. simpl. apply prefix_repeat.
  - intros. rewrite <- in_rev in H. now apply score_aux_in_le in H.
  - intros. rewrite <- in_rev in H. now apply score_aux_in_le in H.
  - repeat rewrite length_rev.
    destruct (length (score_aux (m ++p l) (S (max_atom_f f)) 0)) eqn:Heq.
    + lia.
    + destruct n0.
      * lia.
      * pose proof (score_aux_length (m ++p l) (S (max_atom_f f)) 0).
        pose proof (well_formed_length_le (m ++p l) f Hwf) .
        slia.
  - repeat rewrite length_rev.
    destruct (length (score_aux (m ++d l' ++a n) (S (max_atom_f f)) 0)) eqn:Heq.
    + lia.
    + destruct n0.
      * lia.
      * pose proof (score_aux_length (m ++d l' ++a n) (S (max_atom_f f)) 0).
        pose proof (well_formed_length_le (m ++d l' ++a n) f Hwf').
        slia.
  - rewrite score_aux_split. rewrite rev_app_distr. simp score_aux. apply prefix_prefix.
    + rewrite length_app. repeat rewrite length_rev.
      apply well_formed_length_le in Hwf'. rewrite length_app in Hwf'. simpl in Hwf'.
      pose proof (score_aux_length m (S (max_atom_f f)) 0).
      pose proof (score_aux_length n (S (max_atom_f f)) 0).
      lia.
    + apply prefix_shift.
      * now apply well_formed_tail in Hwf.
      * apply well_formed_length_le in Hwf. simpl in Hwf. lia.
Qed.
