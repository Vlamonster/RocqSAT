From Equations Require Import Equations.
From Stdlib Require Import List.
From RocqSAT Require Import Atom Lit Neg Clause CNF Evaluation.

Definition NoDuplicates (m: PA): Prop := 
  NoDup (map extract (map fst m)).

Definition Bounded (m: PA) (f: CNF): Prop := 
  forall (l: Lit) (a: Ann), In (l, a) m -> 
  exists (c: Clause), In c f /\ (In l c \/ In (¬l) c).

Definition WellFormed (m: PA) (f: CNF): Prop :=
  NoDuplicates m /\ Bounded m f.

Lemma nodup_cons__nodup: forall (m: PA) (l: Lit) (a: Ann),
  NoDuplicates ((l, a) :: m) -> NoDuplicates m.
Proof. intros. now inversion H. Qed.

Lemma nodup_app__nodup: forall (m n: PA),
  NoDuplicates (m ++a n) -> NoDuplicates m.
Proof.
  induction n.
  - now intros.
  - intros. simpl in H. apply nodup_cons__nodup in H.
    + now apply IHn.
    + apply dec.
Qed.

Lemma bounded_cons__bounded: forall (m: PA) (f: CNF) (l: Lit) (a: Ann),
  Bounded ((l, a) :: m) f -> Bounded m f.
Proof.
  unfold Bounded. intros m f l a Hbounded l' a' Hin. apply (Hbounded l' a'). now right.
Qed.

Lemma bounded_app__bounded: forall (m n: PA) (f: CNF),
  Bounded (m ++a n) f -> Bounded m f.
Proof.
  induction n.
  - now intros.
  - intros. simpl in H. destruct a. apply bounded_cons__bounded in H. now apply IHn.
Qed.

Lemma wf_cons__wf: forall (m: PA) (f: CNF) (l: Lit) (a: Ann),
  WellFormed ((l, a) :: m) f -> WellFormed m f.
Proof.
  unfold WellFormed. intros. destruct H. split.
  - now apply nodup_cons__nodup in H.
  - now apply bounded_cons__bounded in H0.
Qed.

Lemma wf_app__wf: forall (m n: PA) (f: CNF),
  WellFormed (m ++a n) f -> WellFormed m f.
Proof.
  unfold WellFormed. intros. destruct H. split.
  - now apply nodup_app__nodup in H.
  - now apply bounded_app__bounded in H0.
Qed.

Lemma nodup_cons__undef: forall (m: PA) (l: Lit) (a: Ann),
  NoDuplicates ((l, a) :: m) -> Undef m l.
Proof. 
  unfold NoDuplicates, Undef. intros. simpl in *. inversion H.
  destruct (l_eval m l) eqn:G.
  - exfalso. apply H2. apply in_map_iff.
    destruct (proj1 (l_eval_some_iff m l) (ex_intro _ _ G)) as [a' [Hin|Hin]].
    + exists l. split.
      * reflexivity.
      * apply in_map_iff. now exists (l, a').
    + exists (¬l). split.
      * destruct l; reflexivity.
      * apply in_map_iff. now exists (¬l, a').
  - reflexivity.
Qed.

Lemma nodup_cons: forall (m: PA) (l: Lit) (a: Ann),
  NoDuplicates m -> Undef m l -> NoDuplicates ((l, a) :: m).
Proof.
  unfold Undef, NoDuplicates. intros. simpl. constructor.
  - unfold not. intros. funelim (l_eval m l).
    + contradiction.
    + congruence.
    + congruence.
    + simpl in *. destruct H2. 
      * destruct l, l'.
        -- simp extract in H2. subst p0. now rewrite eqb_refl in Heq0.
        -- simp extract in H2. subst p0. simp neg in Heq. now rewrite eqb_refl in Heq.
        -- simp extract in H2. subst p0. simp neg in Heq. now rewrite eqb_refl in Heq.
        -- simp extract in H2. subst p0. now rewrite eqb_refl in Heq0.
      * apply (H m l dec).
        -- now inversion H0.
        -- congruence.
        -- assumption.
        -- reflexivity.
        -- reflexivity.  
  - assumption.
Qed.

Lemma bounded_incl: forall (m m': PA) (f: CNF),
  incl m m' -> Bounded m' f -> Bounded m f.
Proof.
  unfold Bounded, incl. intros m m' f Hincl Hbounded l a Hin.
  apply Hincl in Hin. now apply Hbounded in Hin.
Qed.

Lemma bounded_cons: forall (m: PA) (f: CNF) (l: Lit) (a: Ann),
  Bounded m f -> l_in_f f l = true -> Bounded ((l, a) :: m) f.
Proof.
  unfold Bounded. intros m f l a Hbounded Hl_in_f l' a' Hin. 
  apply l_in_f_iff in Hl_in_f as [c [[Hl_in_c|Hnegl_in_c] Hc_in_f ]].
  - destruct Hin.
    + injection H as <- <-. exists c. intuition.
    + now apply Hbounded in H.
  - destruct Hin.
    + injection H as <- <-. exists c. intuition.
    + now apply Hbounded in H.
Qed.
