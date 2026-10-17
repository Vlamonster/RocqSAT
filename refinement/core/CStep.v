From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import State.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement Require Import Step.

(* The parts of a step computed from the context alone, as C code does: the trail is only used through its table,
   with the positions of its decisions on a stack (LimsOf). Propagation without the trail (visit_t, propagate_t,
   check_shorts_t), unsetting a range of the trail (unset_range), and when an outcome on the context agrees with a
   step (Agrees). Used by SolverStep.v and AnalysisCStep.v. *)

Section Free.
  (* The visit of Propagate.v without the trail. *)
  Fixpoint visit_t (p: Lit) (ws kept: list Watcher) (x: Ctx): Ctx * option nat :=
  match ws with
  | []             => (set_watching x p (rev kept), None)
  | (i, b) :: rest =>
    if lookup_true (vals x) b then visit_t p rest ((i, b) :: kept) x else
    match tget (cmap x) i with
    | Some [a]              =>
      if a =? p then
        (set_watching x p (rev_append kept ws), Some i) else visit_t p rest kept x
    | Some (c0 :: c1 :: ls) =>
      if (c0 =? p) || (c1 =? p) then
        let o := if c0 =? p then c1 else c0 in
        let x1 := set_clause x i (o :: p :: ls) in
        if lookup_true (vals x1) o then visit_t p rest ((i, o) :: kept) x1 else
        match swap_watch (vals x1) p ls with
        | Some (r, ls') => visit_t p rest kept (move_watch x1 i (o :: r :: ls') r o)
        | None          =>
          if lookup_undef (vals x1) o then visit_t p rest ((i, o) :: kept)
            (assign x1 o (input i))
          else (set_watching x1 p (rev_append kept ws), Some i)
        end
      else visit_t p rest kept x
    | _                     => visit_t p rest kept x
    end
  end.

  Lemma visit_free: forall (p: Lit) (ws kept: list Watcher) (m m': PA) (x x': Ctx)
    (r: option nat),
    visit p ws kept m x = (m', x', r) -> visit_t p ws kept x = (x', r).
  Proof.
    intros p ws.
    induction ws as [|[i b] ws IH]; intros kept m m' x x' r Hvisit; simpl in Hvisit |- *.
    - now injection Hvisit as _ <- <-.
    - destruct (lookup_true (vals x) b).
      + now apply IH in Hvisit.
      + destruct (tget (cmap x) i) as [[|c0 [|c1 ls]]|].
        * now apply IH in Hvisit.
        * destruct (c0 =? p).
          -- now injection Hvisit as _ <- <-.
          -- now apply IH in Hvisit.
        * destruct ((c0 =? p) || (c1 =? p)).
          -- destruct (lookup_true _ (if c0 =? p then c1 else c0)).
             ++ now apply IH in Hvisit.
             ++ destruct (swap_watch _ p ls) as [[r' ls']|].
                ** now apply IH in Hvisit.
                ** destruct (lookup_undef _ (if c0 =? p then c1 else c0)).
                   --- now apply IH in Hvisit.
                   --- now injection Hvisit as _ <- <-.
          -- now apply IH in Hvisit.
        * now apply IH in Hvisit.
  Qed.

  (* The propagation of Propagate.v without the trail. *)
  Fixpoint propagate_t (fuel: nat) (x: Ctx): Ctx * option nat :=
  match fuel with
  | 0       => (x, None)
  | S fuel' =>
    if qhead x <? tlen x then
      let p := ¬(tget (tr x) (qhead x)) in
      match visit_t p (watching (wls x) p) [] x with
      | (x', Some i) => (x', Some i)
      | (x', None)   => propagate_t fuel' (advance x')
      end
    else (x, None)
  end.

  Lemma propagate_free: forall (fuel: nat) (m m': PA) (x x': Ctx) (r: option nat),
    propagate fuel m x = (m', x', r) -> propagate_t fuel x = (x', r).
  Proof.
    intros fuel. induction fuel as [|fuel IH]; intros m m' x x' r Hprop; simpl in Hprop |- *.
    - now injection Hprop as _ <- <-.
    - destruct (qhead x <? tlen x).
      + destruct (visit (¬(tget (tr x) (qhead x))) _ [] m x) as [[m1 x1] [i|]] eqn:Hvisit;
          apply visit_free in Hvisit; rewrite Hvisit.
        * now injection Hprop as _ <- <-.
        * now apply IH in Hprop.
      + now injection Hprop as _ <- <-.
  Qed.

  (* The check of the short clauses of Propagate.v without the trail. *)
  Fixpoint check_shorts_t (ss: list nat) (x: Ctx): Ctx * option nat :=
  match ss with
  | []       => (x, None)
  | i :: ss' =>
    match tget (cmap x) i with
    | Some (a :: _) =>
      match lookup (vals x) a with
      | Some true  => check_shorts_t ss' x
      | Some false => (x, Some i)
      | None       => check_shorts_t ss' (assign x a (input i))
      end
    | Some []       => (x, Some i)
    | None          => check_shorts_t ss' x
    end
  end.

  Lemma check_shorts_free: forall (ss: list nat) (m m': PA) (x x': Ctx) (r: option nat),
    check_shorts ss m x = (m', x', r) -> check_shorts_t ss x = (x', r).
  Proof.
    intros ss. induction ss as [|i ss IH]; intros m m' x x' r Hcheck; simpl in Hcheck |- *.
    - now injection Hcheck as _ <- <-.
    - destruct (tget (cmap x) i) as [[|a ls]|].
      + now injection Hcheck as _ <- <-.
      + destruct (lookup (vals x) a) as [[|]|].
        * now apply IH in Hcheck.
        * now injection Hcheck as _ <- <-.
        * now apply IH in Hcheck.
      + now apply IH in Hcheck.
  Qed.
End Free.

Section Lims.
  (* lims holds the positions of the decisions of m on its trail, newest first. *)
  Fixpoint LimsOf (lims: list nat) (m: PA): Prop :=
  match m with
  | ⟨⟩     => lims = []
  | ⟨m, _⟩ => LimsOf lims m
  | ⟨m; _⟩ =>
    match lims with
    | j :: lims' => j = PA.length m /\ LimsOf lims' m
    | []         => False
    end
  end.

  (* Propagations keep the positions of the decisions. *)
  Lemma lims_extends: forall (lims: list nat) (m m': PA), LimsOf lims m -> Extends m m' -> LimsOf lims m'.
  Proof.
    intros lims m m' Hlims [n [-> Hn]]. induction n as [|n IH l|n IH l]; simpl in Hn |- *.
    - assumption.
    - now apply IH.
    - destruct Hn.
  Qed.

  (* No decisions exactly when no positions. *)
  Lemma lims_nil: forall (lims: list nat) (m: PA), LimsOf lims m -> lims = [] -> NoDecisions m.
  Proof.
    intros lims m. revert lims. induction m as [|m IH l|m IH l]; intros lims Hlims Hnil; simpl in Hlims |- *.
    - easy.
    - now apply (IH lims).
    - subst lims. contradiction.
  Qed.

  (* The positions of the decisions of ⟨m; l ++ n⟩: those of n, that of l, then those of m. *)
  Lemma lims_split: forall (lims: list nat) (m n: PA) (l: Lit),
    LimsOf lims ⟨m; l ++ n⟩ ->
    exists (lims': list nat), skipn (decisions n) lims = PA.length m :: lims' /\ LimsOf lims' m /\
      length lims = decisions n + S (length lims').
  Proof.
    intros lims m n l. revert lims. induction n as [|n IH y|n IH y]; intros lims Hlims; simpl in Hlims |- *.
    - destruct lims as [|j lims].
      + contradiction.
      + destruct Hlims as [-> Hlims]. now exists lims.
    - now apply IH.
    - destruct lims as [|j lims].
      + contradiction.
      + destruct Hlims as [_ Hlims]. destruct (IH lims Hlims) as (lims' & Hskip & Hlims' & Hlen). exists lims'.
        simpl. split.
        * assumption.
        * split.
          -- assumption.
          -- lia.
  Qed.

End Lims.

Section Trail.
  (* v without the values of the literals at the n positions from j on, newest first. *)
  Fixpoint unset_range (v: Values) (tr: Table Lit) (j n: nat): Values :=
  match n with
  | 0    => v
  | S n' => unset_range (unset_value v (tget tr (j + n'))) tr j n'
  end.

  Lemma unset_range_spec: forall (tr: Table Lit) (tlen: nat) (mt n: PA) (d: Lit) (v: Values),
    TrailOf tr tlen ⟨mt; d ++ n⟩ -> unset_range v tr (PA.length mt) (S (PA.length n)) = unassign_segment v d n.
  Proof.
    intros tr tlen mt n d. revert tlen. induction n as [|n IH x|n IH x]; intros tlen v Htrail.
    - destruct (trail_of_snoc tr tlen mt ⟨mt; d⟩ d eq_refl Htrail) as (_ & Hd & _). simpl.
      now rewrite Nat.add_0_r, Hd.
    - destruct (trail_of_snoc tr tlen ⟨mt; d ++ n⟩ ⟨mt; d ++ n, x⟩ x eq_refl Htrail) as (_ & Hx & Hprefix).
      cbn [unassign_segment PA.length unset_range]. replace (PA.length mt + S (PA.length n)) with
        (PA.length ⟨mt; d ++ n⟩).
      + rewrite Hx. now apply (IH (PA.length ⟨mt; d ++ n⟩)).
      + rewrite (pa_length_app ⟨mt; d⟩ n). simpl. lia.
    - destruct (trail_of_snoc tr tlen ⟨mt; d ++ n⟩ ⟨mt; d ++ n; x⟩ x eq_refl Htrail) as (_ & Hx & Hprefix).
      cbn [unassign_segment PA.length unset_range]. replace (PA.length mt + S (PA.length n)) with
        (PA.length ⟨mt; d ++ n⟩).
      + rewrite Hx. now apply (IH (PA.length ⟨mt; d ++ n⟩)).
      + rewrite (pa_length_app ⟨mt; d⟩ n). simpl. lia.
  Qed.

  (* Unassigning the last level is unassigning the segment of its decision. *)
  Lemma unassign_level_segment: forall (v: Values) (m n: PA) (l: Lit),
    NoDecisions n -> unassign_level v ⟨m; l ++ n⟩ = unassign_segment v l n.
  Proof.
    intros v m n l. revert v. induction n as [|n IH x|n IH x]; intros v Hn; simpl in Hn |- *.
    - reflexivity.
    - now apply IH.
    - destruct Hn.
  Qed.
End Trail.

(* The outcome of a step on the context: stop, fail, or the next context with the positions of its decisions. *)
Inductive CResult: Type :=
| CStop
| CFail
| CNext (x: Ctx) (lims: list nat).

(* The outcome on the context agrees with the step r on the state with formula f. *)
Definition Agrees (f: CNF) (r: option (State * Ctx)) (cr: CResult): Prop :=
match cr with
| CStop          => r = None
| CFail          => exists (x': Ctx), r = Some (fail, x')
| CNext x' lims' => exists (m': PA), r = Some (state m' f, x') /\ LimsOf lims' m'
end.

