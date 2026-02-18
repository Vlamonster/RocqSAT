From Equations Require Import Equations.
From Stdlib Require Import Basics Nat Arith List Relations Wellfounded Lia.
Import ListNotations.
From RocqSAT Require Import Atom Lit Neg Clause CNF Evaluation Trans WellFormed.

Ltac slia := simpl in *; lia.

Equations max_atom_c (c: Clause): nat :=
max_atom_c []           := 0;
max_atom_c (Pos p :: c) := max p (max_atom_c c);
max_atom_c (Neg p :: c) := max p (max_atom_c c).

Equations max_atom_f (f: CNF): nat :=
max_atom_f []       := 0;
max_atom_f (c :: f) := max (max_atom_c c) (max_atom_f f).

Equations score_aux (m: PA) (n x: nat): list nat :=
score_aux []        n x := [n - x];
score_aux (m ++p l) n x := score_aux m n (S x);
score_aux (m ++d l) n x := n - x :: score_aux m n 0.

Equations score (m: PA) (f: CNF): list nat :=
score m f :=
  let max_atom := max_atom_f f in
  let unpadded := rev (score_aux m (S max_atom) 0) in
  let  padding := repeat (S max_atom) (S (S max_atom) - length unpadded) in
  unpadded ++ padding.

Equations score_total (m: PA) (f: CNF): nat :=
score_total m f := S (max_atom_f f) - length m.

Module ScoreExamples.
  Example score_1: score [] [[Pos 0; Pos 1]] = [2; 2; 2].
  Proof. reflexivity. Qed.

  Example score_2: score ([] ++p Pos 0) [[Pos 0; Pos 1]] = [1; 2; 2].
  Proof. reflexivity. Qed.

  Example score_3: score ([] ++d Pos 0) [[Pos 0; Pos 1]] = [2; 2; 2].
  Proof. reflexivity. Qed.

  Example score_4: score ([] ++d Neg 0 ++p Pos 1) [[Pos 0; Pos 1]] = [2; 1; 2].
  Proof. reflexivity. Qed.

  Example score_total_1: score_total [] [[Pos 0; Pos 1]] = 2.
  Proof. reflexivity. Qed.

  Example score_total_2: score_total ([] ++p Pos 0) [[Pos 0; Pos 1]] = 1.
  Proof. reflexivity. Qed.

  Example score_total_3: score_total ([] ++d Pos 0) [[Pos 0; Pos 1]] = 1.
  Proof. reflexivity. Qed.

  Example score_total_4: score_total ([] ++d Neg 0 ++p Pos 1) [[Pos 0; Pos 1]] = 0.
  Proof. reflexivity. Qed.
End ScoreExamples.

Inductive FailLt: relation State :=
| f_fail (m: PA) (f: CNF) (Hwf: WellFormed m f):
  FailLt fail (state m f Hwf).

Lemma wf_fail_lt: well_founded FailLt.
Proof.
  unfold well_founded. intros m. constructor. intros m' Hlt. destruct Hlt.
  constructor. intros m' Hlt. inversion Hlt.
Qed.

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

Lemma wf_bcll: forall (x: nat), well_founded (bcll x).
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

Lemma wf_prefix_lt: forall x, well_founded (PrefixLt x).
Proof.
  intro x. apply (wf_incl _ _ (bcll x)).
  - unfold inclusion. now apply bcll__prefix_lt.
  - apply wf_bcll.
Qed.

Definition TotalLt: relation nat := lt.

Lemma wf_total_lt: well_founded TotalLt.
Proof. apply lt_wf. Qed.

Definition StateLexLt (f: CNF): relation (list nat * nat) :=
  slexprod _ _ (PrefixLt (S (S (max_atom_f f)))) TotalLt.

Lemma wf_state_lex_lt: forall (f: CNF), well_founded (StateLexLt f).
Proof.
  intros. apply wf_slexprod.
  - apply wf_prefix_lt.
  - apply wf_total_lt.
Qed.

Equations state_measure (s: State): list nat * nat :=
state_measure fail          := ([]       , 0              );
state_measure (state m f _) := (score m f, score_total m f).

Definition StateLt (f: CNF): relation State := union _ FailLt (MR (StateLexLt f) state_measure).
Definition StateLtTransClos (f: CNF): relation State := clos_trans _ (StateLt f).

Notation "s '>>[' f ']' s'" := (StateLt f s' s) (at level 40, format "s '/ ' '[' >>[ ']' f ] '/ ' s'").
Notation "s '>>+[' f ']' s'" := (StateLtTransClos f s' s) (at level 40, format "s '/ ' '[' >>+[ ']' f ] '/ ' s'").

Lemma wf_state_lt: forall (f: CNF), well_founded (StateLt f).
Proof.
  intros. apply wf_union.
  - unfold commut. intros. inversion H. subst. exists (state m f0 Hwf).
    + unfold MR in H0. simp state_measure in H0. inversion H0.
      * subst. inversion H3.
      * subst. inversion H3.
    + unfold MR in H0. simp state_measure in H0. inversion H0.
      * subst. inversion H3.
      * subst. inversion H3.
  - apply wf_fail_lt.
  - apply wf_MR. apply wf_state_lex_lt.
Qed.

Theorem wf_state_lt_trans_clos (f: CNF): well_founded (StateLtTransClos f).
Proof. unfold well_founded. intros. constructor. apply wf_clos_trans. apply wf_state_lt. Qed.

Lemma max_atom_c_le: forall (c: Clause) (l: Lit) (p: Atom),
  In l c ->
  extract l = p ->
  p <= max_atom_c c.
Proof.
  intros c l p Hin Heq. funelim (max_atom_c c).
  - contradiction.
  - inversion Hin.
    + subst l. simp extract. apply Nat.max_le_iff. now left.
    + destruct l as [p'|p'].
      * simp extract. apply (H (Pos p') p') in H0.
        -- apply Nat.max_le_iff. now right.
        -- reflexivity.
      * simp extract. apply (H (Neg p') p') in H0.
        -- apply Nat.max_le_iff. now right.
        -- reflexivity.
  - inversion Hin.
    + subst l. simp extract. apply Nat.max_le_iff. now left.
    + destruct l as [p'|p'].
      * simp extract. apply (H (Pos p') p') in H0.
        -- apply Nat.max_le_iff. now right.
        -- reflexivity.
      * simp extract. apply (H (Neg p') p') in H0.
        -- apply Nat.max_le_iff. now right.
        -- reflexivity.
Qed.

Lemma max_atom_f_le: forall (f: CNF) (c: Clause) (l: Lit) (p: Atom),
  In l c ->
  In c f ->
  extract l = p ->
  p <= max_atom_f f.
Proof.
  intros f c l p Hl_in_c Hc_in_f Heq. funelim (max_atom_f f).
  - contradiction.
  - inversion Hc_in_f.
    + subst c0. destruct l as [p|p].
      * simp extract. apply Nat.max_le_iff. left. now apply (max_atom_c_le c (Pos p) p).
      * simp extract. apply Nat.max_le_iff. left. now apply (max_atom_c_le c (Neg p) p).
    + destruct l as [p|p].
      * apply Nat.max_le_iff. right. simp extract. now apply (H c0 (Pos p) p).
      * apply Nat.max_le_iff. right. simp extract. now apply (H c0 (Neg p) p).
Qed.

Lemma wf_le: forall (m: PA) (f: CNF) (p: Atom),
  WellFormed m f ->
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

Lemma wf_length_le: forall (m: PA) (f: CNF),
  WellFormed m f ->
  length m <= S (max_atom_f f).
Proof.
  intros m f Hwf. assert (Heq: length m = length (map extract (map fst m))).
  - now repeat rewrite length_map.
  - rewrite Heq. apply pigeon.
    + now destruct Hwf.
    + intros. apply (wf_le m); assumption.
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
  WellFormed ((l, a) :: m) f ->
  length (score_aux m n x) <= S (max_atom_f f).
Proof.
  intros. 
  pose proof (score_aux_length m n x).
  pose proof (score_aux_length (m ++d l) n x).
  pose proof (wf_length_le ((l, a) :: m) f H).
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

Lemma score_dec: forall (m: PA) (f: CNF) (l: Lit),
  WellFormed (m ++d l) f ->
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

Lemma total_decide: forall (m: PA) (f: CNF) (l: Lit),
  WellFormed (m ++d l) f ->
  TotalLt (score_total (m ++d l) f) (score_total m f).
Proof.
  intros m f l Hwf. pose proof (wf_length_le (m ++d l) f Hwf).
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
  WellFormed m f ->
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
    * now apply wf_cons__wf in Hwf.
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

Lemma prefix_prop: forall (m: PA) (f: CNF) (l: Lit),
  WellFormed (m ++p l) f ->
  PrefixLt (S (S (max_atom_f f))) (score (m ++p l) f) (score m f).
Proof.
  intros m f l Hwf. 
  pose proof (wf_cons__wf m f l prop Hwf) as Hwf'. 
  simp score. simpl. apply prefix_repeat.
  - intros. rewrite <- in_rev in H. now apply score_aux_in_le in H.
  - intros. rewrite <- in_rev in H. now apply score_aux_in_le in H.
  - repeat rewrite length_rev.
    destruct (length (score_aux (m ++p l) (S (max_atom_f f)) 0)) eqn:Heq.
    + lia.
    + destruct n.
      * lia.
      * pose proof (score_aux_length (m ++p l) (S (max_atom_f f)) 0).
        pose proof (wf_length_le (m ++p l) f Hwf) .
        slia.
  - repeat rewrite length_rev.
    destruct (length (score_aux m (S (max_atom_f f)) 0)) eqn:Heq.
    + lia.
    + destruct n.
      * lia.
      * pose proof (score_aux_length m (S (max_atom_f f)) 0).
        pose proof (wf_length_le m f Hwf').
        slia.
  - simp score_aux. apply prefix_shift.
    + assumption.
    + apply wf_length_le in Hwf. slia.
Qed.

Lemma prefix_app: forall (m n: PA) (f: CNF) (l l': Lit),
  WellFormed (m ++p l) f ->
  WellFormed (m ++d l' ++a n) f ->
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
        pose proof (wf_length_le (m ++p l) f Hwf) .
        slia.
  - repeat rewrite length_rev.
    destruct (length (score_aux (m ++d l' ++a n) (S (max_atom_f f)) 0)) eqn:Heq.
    + lia.
    + destruct n0.
      * lia.
      * pose proof (score_aux_length (m ++d l' ++a n) (S (max_atom_f f)) 0).
        pose proof (wf_length_le (m ++d l' ++a n) f Hwf').
        slia.
  - rewrite score_aux_split. rewrite rev_app_distr. simp score_aux. apply prefix_prefix.
    + rewrite length_app. repeat rewrite length_rev.
      apply wf_length_le in Hwf'. rewrite length_app in Hwf'. simpl in Hwf'.
      pose proof (score_aux_length m (S (max_atom_f f)) 0).
      pose proof (score_aux_length n (S (max_atom_f f)) 0).
      lia.
    + apply prefix_shift.
      * now apply wf_cons__wf in Hwf.
      * apply wf_length_le in Hwf. simpl in Hwf. lia.
Qed.

Lemma trans__state_lt: forall (m: PA) (f: CNF) (s': State) (Hwf: WellFormed m f),
  state m f Hwf ==> s' -> state m f Hwf >>[f] s'.
Proof.
  intros. inversion H as 
    [
      m' f' c_conflict Hwf' Hc_in_f Hconflict Hno_dec |
      m' f' c_unit l_unit ? Hwf' Hl_in_c Hc_in_f Hconflict Hundef |
      m' f' c_decide l_decide ? Hwf' Hx_in_c Hc_in_f Hundef |
      m_split n_split f' c_conflict l_split ? Hwf' Hc_in_f Hconflict Hno_dec |
      m' f' c_pure l_pure ? Hwf' Hl_in_c Hc_in_f Hpure Hundef
    ]; subst s'; try subst m'; try subst f'.
  (* t_fail *)
  - unfold StateLt. now left.
  (* t_unit *)
  - unfold StateLt. right. unfold MR. simp state_measure. apply left_slex.
    now apply prefix_prop.
  (* t_decide *)
  - unfold StateLt. right. unfold MR. simp state_measure. rewrite score_dec.
    + apply right_slex. now apply total_decide.
    + assumption.
  (* t_backtrack *)
  - unfold StateLt. right. unfold MR. simp state_measure. rewrite <- H0. apply left_slex.
    apply prefix_app.
    + assumption.
    + now rewrite H0.
  (* t_pure *)
  - unfold StateLt. right. unfold MR. simp state_measure. apply left_slex.
    now apply prefix_prop.
Qed.

Lemma derivation_strict__state_lt_trans_clos: forall (m: PA) (f: CNF) (s': State) (Hwf: WellFormed m f),
  state m f Hwf ==>+ s' -> state m f Hwf >>+[f] s'.
Proof.
  intros. apply clos_trans_tn1_iff in H. induction H.
  - apply t_step. now apply trans__state_lt.
  - destruct y.
    + inversion H.
    + apply clos_trans_tn1_iff in H0. apply derivation_strict_same_formula in H0. subst f0.
      eapply t_trans.
      * apply t_step. apply trans__state_lt. apply H.
      * apply IHclos_trans_n1.
Qed.

(* Thanks to Gaetan Gilbert *)
Lemma clos_refl_trans_flip A R x y : clos_refl_trans A (fun a b => R b a) x y -> clos_refl_trans A R y x.
Proof.
  induction 1;econstructor;solve [eauto].
Qed.

Section WfInclusion.
  Variable A : Type.
  Variables R1 R2 : A -> A -> Prop.

  Lemma Acc_incl' : forall z : A, (forall x y, clos_refl_trans _ R1 y z -> R1 x y -> R2 x y) -> Acc R2 z -> Acc R1 z.
  Proof.
    intros z H.
    induction 1 as [z Hz IH].
    apply Acc_intro.
    intros y Hy.
    apply IH.
    - apply H. 2:assumption.
      constructor 2.
    - intros x z' Hz' HR.
      apply H; only 2: exact HR.
      apply rt_trans with y.
      + assumption.
      + apply rt_step;assumption.
  Qed.
End WfInclusion.

Equations cnf (s: State): option CNF :=
cnf fail          := None;
cnf (state _ f _) := Some f.

Lemma to_statelt s s' :
  Trans s s' ->
  match cnf s with
  | None => False
  | Some f =>
      (cnf s' = None \/ cnf s' = Some f) /\ StateLt f s' s
  end.
Proof.
  intros. funelim (cnf s).
  - inversion H.
  - split.
    + destruct s'.
      * now left.
      * right. apply trans_same_formula in H. now subst.
    + now apply trans__state_lt.
Qed.

Lemma to_statelt' s s' :
  Trans s s' ->
  match cnf s' with
  | None => forall f, cnf s = Some f -> StateLt f s' s
  | Some f => cnf s = Some f /\ StateLt f s' s
  end.
Proof.
  intros H.
  apply to_statelt in H.
  destruct (cnf s').
  - destruct (cnf s).
    + destruct H as [[e|[=]] H];subst;auto.
      discriminate e.
    + contradiction H.
  - intros f Hf;rewrite Hf in H.
    destruct H;auto.
Qed.

Lemma to_statelt0 s s' f : cnf s' = Some f -> Trans s s' -> cnf s = Some f /\ StateLt f s' s.
Proof.
  intros H H'.
  apply to_statelt in H'.
  rewrite H in H'.
  destruct (cnf s).
  - destruct H' as [[e|[=]] H']; try discriminate e.
    subst;auto.
  - contradiction H'.
Qed.

Lemma to_statelt0' s s' f : cnf s = Some f -> Trans s s' -> (cnf s' = None \/ cnf s' = Some f) /\ StateLt f s' s.
Proof.
  intros H H'.
  apply to_statelt in H'. rewrite H in H'. assumption.
Qed.

Lemma clos_nf s s' f : cnf s' = Some f -> clos_refl_trans _ Trans s s' -> cnf s = Some f.
Proof.
  intros Hf H.
  induction H as [s s' H| s | y v x _ IHyv _ IHzy].
  - apply (to_statelt0 _ _ _ Hf) in H.
    destruct H as [H _]; exact H.
  - assumption.
  - auto.
Qed.

Lemma clos_nf0 s s' : cnf s = None -> clos_refl_trans _ Trans s s' -> s = s'.
Proof.
  intros Hf H.
  induction H as [s s' H| s | y v x Hyv IHyv Hzy IHzy].
  - apply to_statelt in H. rewrite Hf in H. contradiction H.
  - reflexivity.
  - firstorder. subst. auto.
Qed.

Lemma clos_nf' s s' f : cnf s = Some f -> clos_refl_trans _ Trans s s' -> cnf s' = None \/ cnf s' = Some f.
Proof.
  intros Hf H.
  induction H as [s s' H| s | y v x Hyv IHyv Hzy IHzy].
  - apply (to_statelt0' _ _ _ Hf) in H.
    destruct H as [H _]; exact H.
  - right;assumption.
  - specialize (IHyv Hf). destruct IHyv.
    + apply (clos_nf0 _ _ H) in Hzy. subst. left;assumption.
    + specialize (IHzy H). assumption.
Qed.

Lemma statelt_incl x f :
  cnf x = Some f ->
  forall z y,
  clos_refl_trans _ Trans x y ->
  Trans y z ->
  StateLt f z y.
Proof.
  intros Hx z; induction 1 as [y x Hyx| x | y v x Hyv Hzv Hvx Hzx].
  - intros Hxz.
    apply (to_statelt0' _ _ _ Hx) in Hyx.
    destruct Hyx as [[e|e] Hxy].
    + apply to_statelt in Hxz. rewrite e in Hxz. contradiction Hxz.
    + apply (to_statelt0' _ _ _ e) in Hxz.
      destruct Hxz as [_ Hxz].
      assumption.
  - intros Hxz.
    apply to_statelt in Hxz. rewrite Hx in Hxz.
    destruct Hxz as [_ Hxz].
    assumption.
  - intros Hxz.
    apply Hzx. 2:assumption.
    destruct (cnf v) as [f'|] eqn:Hv.
    + pose proof (clos_nf _ _ _ Hv Hyv) as Hy.
      congruence.
    + pose proof (clos_nf0 _ _ Hv Hvx). subst.
      apply to_statelt in Hxz.
      rewrite Hv in Hxz. contradiction Hxz.
Qed.

Lemma wf_trans0 : forall x f, cnf x = Some f -> Acc (flip Trans) x.
Proof.
  intros x f Hx.
  apply Acc_incl' with (R2:=StateLt f).
  2:apply wf_state_lt.
  intros z y Hxy Hyz.
  apply clos_refl_trans_flip in Hxy.
  apply (statelt_incl _ _ Hx); assumption.
Qed.

Lemma wf_trans: well_founded (flip Trans).
Proof.
  intros x.
  destruct (cnf x) eqn:Hx.
  - eapply wf_trans0;eassumption.
  - constructor;intros y H.
    apply to_statelt in H. rewrite Hx in H.
    contradiction H.
Qed.

Lemma clos_trans_flip: forall {A: Type} (R: relation A) (a b: A),
  flip (clos_trans _ R) a b <-> clos_trans _ (flip R) a b.
Proof.
  split.
  - intros. unfold flip in H. apply clos_trans_tn1_iff in H. induction H.
    + now apply t_step.
    + eapply t_trans.
      * apply t_step. apply H.
      * assumption.
  - intros. apply clos_trans_tn1_iff in H. induction H.
    + now apply t_step.
    + eapply t_trans.
      * apply t_step. apply H.
      * assumption.
Qed.

Lemma wf_strict_derivation: well_founded (flip DerivationStrict).
Proof. 
  apply (wf_incl _ _ (clos_trans _ (flip Trans))).
  - unfold inclusion. intros. now apply clos_trans_flip.
  - apply wf_clos_trans. apply wf_trans.
Qed.
