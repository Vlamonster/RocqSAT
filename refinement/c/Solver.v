(* The C solver, end to end: init and then solve answer whether the formula of
   the clauses is satisfiable, unless they reject the input or run out of room, and both
   terminate. *)
From Stdlib Require Import List SetoidList.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit Clause CNF Assignment Model Satisfiability State Measure.
From RocqSAT.refinement Require Import Search Propagate Step.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep Index Init Solve.
Import ListNotations.

(* The lists lss are the clauses of f: each holds exactly the literals of a clause of f,
   and each clause of f has such a list. *)
Record ClauseListsOf (f: CNF) (lss: list (list Lit)): Prop := {
  cl_sound: forall (cs: list Lit), In cs lss -> ClauseOf f cs;
  cl_complete: forall (c: Clause), c ∈ f ->
    exists (cs: list Lit), In cs lss /\ forall (l: Lit), In l cs <-> l ∈ c;
}.

(* The literals of clause lists that are the clauses of f are the literals of f. *)
Lemma lits_of_clauses: forall (lss: list (list Lit)) (f: CNF) (l: Lit),
  ClauseListsOf f lss -> (exists (cs: list Lit), In cs lss /\ In l cs) <-> l ∈ f.
Proof.
  intros lss f l [Hsound Hcomplete]. split.
  - intros [cs [Hcs Hl]]. destruct (Hsound cs Hcs) as [c [Hc Hiff]]. exists c. split.
    + now apply Hiff.
    + assumption.
  - intros [c [Hl Hc]]. destruct (Hcomplete c Hc) as [cs [Hcs Hiff]]. exists cs. split.
    + assumption.
    + now apply Hiff.
Qed.

(* With the atoms of f below N, the trail bound of the solver is at most N. *)
Lemma max_atom_below: forall (f: CNF) (N: nat),
  (forall (l: Lit), l ∈ f -> (extract l < N)%nat) -> (1 <= N)%nat ->
  (Datatypes.S (max_atom_f f) <= N)%nat.
Proof.
  intros f N Hat HN. unfold max_atom_f.
  assert (Hle: (list_max (map extract (flat_map Clause.elements (CNF.elements f)))
                <= N - 1)%nat).
  - apply list_max_le, Forall_forall. intros k Hk. apply in_map_iff in Hk as [l [<- Hl]].
    apply in_flat_map in Hl as [c [Hc Hl]]. apply clause_elements_iff in Hl.
    assert (Hcf: c ∈ f).
    { apply CNF.elements_spec1, In_InA.
      - apply CNF.E.eq_equiv.
      - assumption. }
    assert (Hlf: l ∈ f).
    { exists c. now split. }
    apply Hat in Hlf. lia.
  - lia.
Qed.

(* The solver, as the driver runs it. From memory holding the clauses lss of f for N
   atoms, laid out as InitInput says: init rejects the input, or solve answers 1 with a
   model of f on the trail, 0 when f is unsatisfiable, or 2 when out of room. Both calls
   terminate. In between, init sets up the initial context of SolverStep.v
   (init_correct), from which solve runs the solver (solve_correct). *)
Theorem solver_correct: forall (S: Shape) (bm: block) (N: nat) (lss: list (list Lit))
  (f: CNF) (tw tc: nat -> Z),
  InitInput S N lss tw tc -> ClauseListsOf f lss ->
  {{ m | IRep m S bm N lss tw tc }}
    f_init(sptr S); f_solve(sptr S)
  {{ m', r | r = Rejected \/
             (r = Returned 1 /\ exists (pm: PA), Model pm f /\ TrailIn m' S N pm) \/
             (r = Returned 0 /\ Unsat f) \/
             r = Returned 2 }}.
Proof.
  intros S bm N lss f tw tc HIn Hlss m HI. pose proof Hlss as [Hsound Hcomplete].
  eapply call_weaken.
  - apply (init_correct S bm N lss tw tc HIn m HI).
  - intros m' v [-> | [-> [HN1 (offs & caps & acc & HRep & Hnd & Hacc)]]].
    + (* init returned 0: rejected *)
      left. split.
      * reflexivity.
      * left. reflexivity.
    + (* init returned 1: solve runs from the initial context *)
      right. eapply call_weaken.
      * apply (solve_correct (with_room S offs caps) N lss (initial_of lss acc N) f m').
        split.
        -- assumption.
        -- apply initial_of_inv.
           ++ intros cs Hcs. split.
              ** apply In_nth with (d := []) in Hcs as [i [Hi <-]]. now apply Hnd.
              ** now apply Hsound.
           ++ assumption.
           ++ intros l. rewrite Hacc. now apply lits_of_clauses.
           ++ apply max_atom_below.
              ** intros l Hl.
                 apply (lits_of_clauses lss f l Hlss) in Hl as [cs [Hcs Hl]].
                 apply In_nth with (d := []) in Hcs as [i [Hi <-]].
                 apply (clause_atoms m' (with_room S offs caps) N lss
                          (initial_of lss acc N) [] i (nth i lss []) l (proj1 HRep)).
                 --- (* clause i of the initial context is clause i of lss *)
                     rewrite initial_of_idx. cbn [cmap]. rewrite idx_cm by lia.
                     replace (i <? length lss)%nat with true
                       by (symmetry; now apply Nat.ltb_lt).
                     reflexivity.
                 --- assumption.
              ** assumption.
      * (* what solve returned is the answer *)
        intros m'' r [[-> Hmodel] | [[-> Hunsat] | ->]].
        -- exists 1. split.
           ++ reflexivity.
           ++ right. left. split.
              ** reflexivity.
              ** assumption.
        -- exists 0. split.
           ++ reflexivity.
           ++ right. right. left. split.
              ** reflexivity.
              ** assumption.
        -- exists 2. split.
           ++ reflexivity.
           ++ right. right. right. reflexivity.
Qed.
