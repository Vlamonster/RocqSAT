From Stdlib Require Import Basics.
From Stdlib Require Import List.
From Stdlib Require Import Relations.
From Stdlib Require Import Wellfounded.
From Stdlib Require Import Wf_nat.
From Stdlib Require Import Lia.

From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import State.
From RocqSAT Require Import WellFormed.
From RocqSAT Require Import Rule.
From RocqSAT Require Import Trans.
From RocqSAT Require Import Measure.
From RocqSAT Require Import Termination.
From RocqSAT.rules Require Import Fail.
From RocqSAT.rules Require Import Unit.
From RocqSAT.rules Require Import Decide.
From RocqSAT.rules Require Import Backtrack.
From RocqSAT.rules Require Import Backjump.
From RocqSAT.rules Require Import Pure.
From RocqSAT.rules Require Import Restart.
From RocqSAT.utils Require Import Invariant.

(* A step of rs, or a restart once the number c of steps since the last restart reaches g k, where k is the number
   of restarts so far. The states carry k and c. *)
Inductive Scheduled (rs: list Rule) (g: nat -> nat): relation (State * nat * nat) :=
| s_step (s s': State) (k c: nat):
  s ==>[rs] s' ->
  Scheduled rs g (s, k, c) (s', k, S c)
| s_restart (s s': State) (k c: nat):
  g k <= c ->
  RestartStep s s' ->
  Scheduled rs g (s, k, c) (s', S k, 0).

(* Every rule of rs keeps the formula. *)
Definition KeepsFormula (rs: list Rule): Prop := forall (r: Rule), In r rs -> PreservesFormula (step r).

Lemma trans_same_formula: forall (rs: list Rule) (m m': PA) (f f': CNF),
  KeepsFormula rs -> state m f ==>[rs] state m' f' -> f = f'.
Proof.
  intros rs m m' f f' Hkeep Htrans. apply trans_rule in Htrans as [r [Hr Hstep]]. now apply (Hkeep r Hr) in Hstep.
Qed.

(* Nothing follows fail. *)
Lemma scheduled_fail_acc: forall (rs: list Rule) (g: nat -> nat) (k c: nat), Acc (flip (Scheduled rs g)) (fail, k, c).
Proof.
  intros rs g k c. constructor. intros p Hstep. inversion Hstep as [? ? ? ? Htrans|? ? ? ? _ Hrestart]; subst.
  - inversion Htrans.
  - inversion Hrestart.
Qed.

(* Given a bound C on the steps since the last restart plus the rank, and a number k0 of restarts after which the
   next one needs more than C steps, every derivation is finite: a step lowers the rank, and a restart raises k,
   which never gets past k0. *)
Lemma scheduled_acc: forall (rs: list Rule) (g: nat -> nat) (f: CNF) (C k0: nat),
  KeepsFormula rs ->
  C < g k0 ->
  rank ⟨⟩ f <= C ->
  forall (k: nat) (m: PA) (c: nat),
  k <= k0 ->
  WellFormed (state m f) ->
  c + rank m f <= C ->
  Acc (flip (Scheduled rs g)) (state m f, k, c).
Proof.
  intros rs g f C k0 Hkeep HC Hinit k.
  induction k as [k IHk] using (well_founded_induction (well_founded_ltof nat (fun (k: nat) => k0 - k))).
  intros m. remember (rank m f) as n eqn:Hn. revert m Hn.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros m Hn c Hk Hwf Hc. subst n. constructor. intros [[s' k'] c'] Hstep.
  inversion Hstep as [? ? ? ? Htrans|? ? ? ? Hg Hrestart]; subst.
  (* A step of rs *)
  - destruct s' as [|m' f'].
    + apply scheduled_fail_acc.
    + assert (Heq: f = f').
      * now apply (trans_same_formula rs m m' f f').
      * subst f'. assert (Hwf': WellFormed (state m' f)).
        -- now apply (trans_well_formed rs (state m f)).
        -- assert (Hlt: rank m' f < rank m f).
           ++ apply state_lt_rank.
              ** assumption.
              ** assumption.
              ** now apply (trans__state_lt rs).
           ++ apply (IHn (rank m' f) Hlt m').
              ** reflexivity.
              ** assumption.
              ** assumption.
              ** lia.
  (* A restart: k is not k0, since restart k0 needs more than C steps *)
  - inversion Hrestart; subst. apply IHk.
    + unfold ltof. assert (k <> k0).
      * intros ->. lia.
      * lia.
    + assert (k <> k0).
      * intros ->. lia.
      * lia.
    + now apply (restart_well_formed m ⟨⟩ f f).
    + assumption.
Qed.

(* Restarting on an unbounded schedule terminates: there are no infinite derivations from a well-formed state. *)
Theorem scheduled_terminates: forall (rs: list Rule) (g: nat -> nat) (s: State) (c: nat),
  KeepsFormula rs ->
  (forall (n: nat), exists (k: nat), n < g k) ->
  WellFormed s ->
  Acc (flip (Scheduled rs g)) (s, 0, c).
Proof.
  intros rs g [|m f] c Hkeep Hunbounded Hwf.
  - apply scheduled_fail_acc.
  - destruct (Hunbounded (max (c + rank m f) (rank ⟨⟩ f))) as [k0 Hk0].
    apply (scheduled_acc rs g f (max (c + rank m f) (rank ⟨⟩ f)) k0).
    + assumption.
    + assumption.
    + lia.
    + lia.
    + assumption.
    + lia.
Qed.

(* A restart leads back to the initial state, so every state reachable with restarts is reachable without. *)
Lemma scheduled_derivation: forall (rs: list Rule) (g: nat -> nat) (f: CNF) (s: State) (k c k' c': nat),
  KeepsFormula rs ->
  clos_refl_trans _ (Scheduled rs g) (state ⟨⟩ f, k, c) (s, k', c') ->
  state ⟨⟩ f ==>*[rs] s.
Proof.
  intros rs g f s k c k' c' Hkeep Hsched.
  apply (clos_refl_trans_invariant _ _ (fun (p: State * nat * nat) => state ⟨⟩ f ==>*[rs] fst (fst p))) in Hsched.
  - assumption.
  - intros [[s1 k1] c1] [[s2 k2] c2] Hstep Hs1. simpl in *.
    inversion Hstep as [? ? ? ? Htrans|? ? ? ? _ Hrestart]; subst.
    + apply rt_trans with s1.
      * assumption.
      * now apply rt_step.
    + inversion Hrestart as [m f']; subst.
      assert (Heq: f' = f).
      * apply (derivation_invariant rs (fun (_: PA) (g: CNF) => g = f)) with ⟨⟩ m f.
        -- intros m1 m2 f1 f2 Htrans <-. symmetry. now apply (trans_same_formula rs m1 m2 f1 f2).
        -- assumption.
        -- reflexivity.
      * subst f'. apply rt_refl.
  - apply rt_refl.
Qed.

(* The systems of Trans.v keep the formula. *)
Lemma dpll_keeps_formula: KeepsFormula DPLL.
Proof.
  intros r Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - apply fail_same_formula.
  - apply unit_same_formula.
  - apply decide_same_formula.
  - apply backtrack_same_formula.
  - apply pure_same_formula.
Qed.

Lemma basic_keeps_formula: KeepsFormula Basic.
Proof.
  intros r Hr. apply dpll_keeps_formula. destruct Hr as [<-|[<-|[<-|[]]]].
  - now left.
  - right. right. now left.
  - right. right. right. now left.
Qed.

Lemma dpll_bj_keeps_formula: KeepsFormula DPLL_BJ.
Proof.
  intros r Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - apply fail_same_formula.
  - apply unit_same_formula.
  - apply decide_same_formula.
  - apply backjump_same_formula.
  - apply pure_same_formula.
Qed.
