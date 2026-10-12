(* The solver step on the store (Store.v): the tables are read and written in place, and only the scalars and short
   lists of the context are kept in a frame. Each computation is shown to compute exactly the corresponding function
   of Propagate.v and Step.v on the context made of the frame and the store, so the solver inherits their
   correctness. *)
From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT Require Import Assignment.
From RocqSAT Require Import State.
From RocqSAT Require Import Measure.
From RocqSAT Require Import Trans.
From RocqSAT Require Import Strategy.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Search.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import Analysis.
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement Require Import Step.
From RocqSAT.refinement Require Import Store.

Section Literals.
  (* The tests below read the value of the atom directly, so that the extracted code does not allocate the value of
     the literal. *)
  Definition lookup_trueM (l: Lit): M bool :=
  bind (vget (extract l)) (fun (r: option bool) =>
  ret match r with
      | Some b => if is_pos l then b else negb b
      | None   => false
      end).

  Lemma lookup_trueM_spec: forall (l: Lit) (st: Store), lookup_trueM l st = (lookup_true (svals st) l, st).
  Proof.
    intros l st. unfold lookup_trueM, lookup_true, lookup. rewrite (bind_spec _ _ _ _ _ (vget_spec (extract l) st)).
    destruct (tget (svals st) (extract l)) as [[|]|]; destruct (is_pos l); reflexivity.
  Qed.

  Definition lookup_undefM (l: Lit): M bool :=
  bind (vget (extract l)) (fun (r: option bool) =>
  ret match r with
      | Some _ => false
      | None   => true
      end).

  Lemma lookup_undefM_spec: forall (l: Lit) (st: Store), lookup_undefM l st = (lookup_undef (svals st) l, st).
  Proof.
    intros l st. unfold lookup_undefM, lookup_undef, lookup. rewrite (bind_spec _ _ _ _ _ (vget_spec (extract l) st)).
    now destruct (tget (svals st) (extract l)).
  Qed.

  Definition lookupM (l: Lit): M (option bool) :=
  bind (vget (extract l)) (fun (r: option bool) =>
  ret match r with
      | Some b => Some (if is_pos l then b else negb b)
      | None   => None
      end).

  Lemma lookupM_spec: forall (l: Lit) (st: Store), lookupM l st = (lookup (svals st) l, st).
  Proof. reflexivity. Qed.

  Definition not_falseM (l: Lit): M bool :=
  bind (vget (extract l)) (fun (r: option bool) =>
  ret match r with
      | Some b => if is_pos l then b else negb b
      | None   => true
      end).

  Lemma not_falseM_spec: forall (l: Lit) (st: Store), not_falseM l st = (not_false (svals st) l, st).
  Proof.
    intros l st. unfold not_falseM, not_false, lookup. rewrite (bind_spec _ _ _ _ _ (vget_spec (extract l) st)).
    destruct (tget (svals st) (extract l)) as [[|]|]; destruct (is_pos l); reflexivity.
  Qed.

  (* The phase of l, as phase. *)
  Definition phaseM (l: Lit): M Lit :=
  bind (pget (extract l)) (fun (o: option bool) =>
  match o with
  | Some true  => ret (Pos (extract l))
  | Some false => ret (Neg (extract l))
  | None       => ret l
  end).

  Lemma phaseM_spec: forall (l: Lit) (st: Store), phaseM l st = (phase (sphs st) l, st).
  Proof.
    intros l st. unfold phaseM, phase. rewrite (bind_spec _ _ _ _ _ (pget_spec _ _)).
    now destruct (tget (sphs st) (extract l)) as [[|]|].
  Qed.
End Literals.

(* The part of the context outside the store. *)
Record Frame: Type := mkFrame {
  ftlen: nat;           (* the length of the trail *)
  fqhead: nat;          (* the start of the propagation queue *)
  fshorts: list nat;    (* the short clauses still to check *)
  fnlits: nat;          (* the number of literals to decide on *)
  fcur: nat;            (* the cursor in the literals to decide on *)
  fsaved: list nat;     (* the cursor before each decision *)
  fdl: nat;             (* hint: the current decision level *)
  fnvars: nat           (* a bound on the length of the trail *)
}.

(* The context made of a frame and a store. *)
Definition combine (y: Frame) (st: Store): Ctx :=
mkCtx (svals st) (scmap st) (swat st) (swls st) (strl st) (ftlen y) (fqhead y) (fshorts y) (salls st) (fnlits y)
  (fcur y) (fsaved y) (srsn st) (slvl st) (fdl y) (smrk st) (sphs st) (fnvars y).

(* Assign l with reason r, as assign. *)
Definition assignM (y: Frame) (l: Lit) (r: nat): M Frame :=
bind (vset (extract l) (match l with Pos _ => Some true | Neg _ => Some false end)) (fun _ =>
bind (trset (ftlen y) l) (fun _ =>
bind (rset (extract l) r) (fun _ =>
bind (dset (extract l) (fdl y)) (fun _ =>
bind (pset (extract l) (match l with Pos _ => Some true | Neg _ => Some false end)) (fun _ =>
ret (mkFrame (S (ftlen y)) (fqhead y) (fshorts y) (fnlits y) (fcur y) (fsaved y) (fdl y) (fnvars y))))))).

Lemma assignM_spec: forall (y y': Frame) (l: Lit) (r: nat) (st st': Store),
  assignM y l r st = (y', st') -> combine y' st' = assign (combine y st) l r.
Proof. intros y y' l r st st' H. cbv [assignM bind ret vset trset rset dset pset] in H. injection H as <- <-. now destruct l. Qed.

(* Clause i now watches w and is appended to the watch list of l, as move_watch. *)
Definition move_watchM (i: nat) (w: Lit * Lit) (l: Lit): M unit :=
bind (wset i w) (fun _ => bind (lget (lit_key l)) (fun (ws: list nat) => lset (lit_key l) (ws ++ [i]))).

Lemma move_watchM_spec: forall (y: Frame) (i: nat) (w: Lit * Lit) (l: Lit) (st st': Store) (u: unit),
  move_watchM i w l st = (u, st') -> combine y st' = move_watch (combine y st) i w l.
Proof. intros y i w l st st' u H. cbv [move_watchM bind ret wset lget lset] in H. now injection H as _ <-. Qed.

(* The first literal of ls that is neither false nor o, as the search in visit. *)
Fixpoint find_otherM (o: Lit) (ls: list Lit): M (option Lit) :=
match ls with
| []       => ret None
| r :: ls' => bind (not_falseM r) (fun (b: bool) => if b && negb (r =? o) then ret (Some r) else find_otherM o ls')
end.

Lemma find_otherM_spec: forall (o: Lit) (ls: list Lit) (st: Store),
  find_otherM o ls st = (find (fun (r: Lit) => not_false (svals st) r && negb (r =? o)) ls, st).
Proof.
  intros o ls st. induction ls as [|r ls IH]; simpl.
  - reflexivity.
  - rewrite (bind_spec _ _ _ _ _ (not_falseM_spec r st)). destruct (not_false (svals st) r && negb (r =? o)).
    + reflexivity.
    + assumption.
Qed.

(* Visit the clauses ws watching p, as visit. *)
Fixpoint visitM (p: Lit) (ws kept: list nat) (m: PA) (y: Frame): M (PA * Frame * option nat) :=
match ws with
| []        => bind (lset (lit_key p) (rev kept)) (fun _ => ret (m, y, None))
| i :: rest =>
  bind (wget i) (fun (w: Lit * Lit) =>
  match w with
  | (w1, w2) =>
    if (w1 =? p) || (w2 =? p) then
      let o := if w1 =? p then w2 else w1 in
      bind (lookup_trueM o) (fun (t: bool) =>
      if t then visitM p rest (i :: kept) m y else
      bind (cget i) (fun (c: option (list Lit)) =>
      match c with
      | Some ls =>
        bind (find_otherM o ls) (fun (r: option Lit) =>
        match r with
        | Some r' =>
          bind (move_watchM i (if w1 =? p then (r', w2) else (w1, r')) r') (fun _ => visitM p rest kept m y)
        | None    =>
          bind (lookup_undefM o) (fun (u: bool) =>
          if u then bind (assignM y o (S i)) (fun (y': Frame) => visitM p rest (i :: kept) ⟨m, o⟩ y')
          else bind (lset (lit_key p) (rev_append kept ws)) (fun _ => ret (m, y, Some i)))
        end)
      | None    => visitM p rest kept m y
      end))
    else visitM p rest kept m y
  end)
end.

Lemma visitM_spec: forall (p: Lit) (ws kept: list nat) (m m': PA) (y y': Frame) (r: option nat) (st st': Store),
  visitM p ws kept m y st = (m', y', r, st') -> visit p ws kept m (combine y st) = (m', combine y' st', r).
Proof.
  intros p ws. induction ws as [|i rest IH]; intros kept m m' y y' r st st' H; simpl in H |- *.
  - cbv [bind ret lset] in H. now injection H as <- <- <- <-.
  - rewrite (bind_spec _ _ _ _ _ (wget_spec i st)) in H. destruct (tget (swat st) i) as [w1 w2].
    destruct ((w1 =? p) || (w2 =? p)).
    + rewrite (bind_spec _ _ _ _ _ (lookup_trueM_spec _ st)) in H. destruct (lookup_true (svals st) _).
      * now apply IH.
      * rewrite (bind_spec _ _ _ _ _ (cget_spec i st)) in H. destruct (tget (scmap st) i) as [ls|].
        -- rewrite (bind_spec _ _ _ _ _ (find_otherM_spec _ ls st)) in H.
           destruct (find (fun (r: Lit) => not_false (svals st) r && negb (r =? _)) ls) as [r'|].
           ++ destruct (move_watchM i (if w1 =? p then (r', w2) else (w1, r')) r' st) as [u st1] eqn:Hmove.
              rewrite (bind_spec _ _ _ _ _ Hmove) in H. rewrite <- (move_watchM_spec y i _ r' st st1 u Hmove).
              now apply IH.
           ++ rewrite (bind_spec _ _ _ _ _ (lookup_undefM_spec _ st)) in H. destruct (lookup_undef (svals st) _).
              ** destruct (assignM y (if w1 =? p then w2 else w1) (S i) st) as [y1 st1] eqn:Hassign.
                 rewrite (bind_spec _ _ _ _ _ Hassign) in H. rewrite <- (assignM_spec y y1 _ _ st st1 Hassign).
                 now apply IH.
              ** cbv [bind ret lset] in H. now injection H as <- <- <- <-.
        -- now apply IH.
    + now apply IH.
Qed.

(* The frame with the queue moved past one literal. *)
Definition advance_frame (y: Frame): Frame :=
mkFrame (ftlen y) (S (fqhead y)) (fshorts y) (fnlits y) (fcur y) (fsaved y) (fdl y) (fnvars y).

(* Visit the watchers of the queued literals, as propagate. *)
Fixpoint propagateM (fuel: nat) (m: PA) (y: Frame): M (PA * Frame * option nat) :=
match fuel with
| 0       => ret (m, y, None)
| S fuel' =>
  if fqhead y <? ftlen y then
    bind (trget (fqhead y)) (fun (t: Lit) =>
    bind (lget (lit_key (¬t))) (fun (ws: list nat) =>
    bind (visitM (¬t) ws [] m y) (fun (r: PA * Frame * option nat) =>
    match r with
    | (m', y', Some i) => ret (m', y', Some i)
    | (m', y', None)   => propagateM fuel' m' (advance_frame y')
    end)))
  else ret (m, y, None)
end.

Lemma propagateM_spec: forall (fuel: nat) (m m': PA) (y y': Frame) (r: option nat) (st st': Store),
  propagateM fuel m y st = (m', y', r, st') -> propagate fuel m (combine y st) = (m', combine y' st', r).
Proof.
  intros fuel. induction fuel as [|fuel IH]; intros m m' y y' r st st' H; simpl in H |- *.
  - now injection H as <- <- <- <-.
  - destruct (fqhead y <? ftlen y).
    + rewrite (bind_spec _ _ _ _ _ (trget_spec _ st)), (bind_spec _ _ _ _ _ (lget_spec _ st)) in H.
      destruct (visitM (¬(tget (strl st) (fqhead y))) (tget (swls st) (lit_key (¬(tget (strl st) (fqhead y))))) [] m y st)
        as [[[m1 y1] r1] st1] eqn:Hvisit.
      rewrite (bind_spec _ _ _ _ _ Hvisit) in H. apply visitM_spec in Hvisit. unfold watching. simpl.
      rewrite Hvisit. destruct r1 as [i|].
      * cbv [ret] in H. now injection H as <- <- <- <-.
      * change (advance (combine y1 st1)) with (combine (advance_frame y1) st1). now apply IH.
    + now injection H as <- <- <- <-.
Qed.

(* Check the short clauses ss, as check_shorts. *)
Fixpoint check_shortsM (ss: list nat) (m: PA) (y: Frame): M (PA * Frame * option nat) :=
match ss with
| []       => ret (m, y, None)
| i :: ss' =>
  bind (cget i) (fun (c: option (list Lit)) =>
  match c with
  | Some (a :: _) =>
    bind (lookupM a) (fun (b: option bool) =>
    match b with
    | Some true  => check_shortsM ss' m y
    | Some false => ret (m, y, Some i)
    | None       => bind (assignM y a (S i)) (fun (y': Frame) => check_shortsM ss' ⟨m, a⟩ y')
    end)
  | Some []       => ret (m, y, Some i)
  | None          => check_shortsM ss' m y
  end)
end.

Lemma check_shortsM_spec: forall (ss: list nat) (m m': PA) (y y': Frame) (r: option nat) (st st': Store),
  check_shortsM ss m y st = (m', y', r, st') -> check_shorts ss m (combine y st) = (m', combine y' st', r).
Proof.
  intros ss. induction ss as [|i ss IH]; intros m m' y y' r st st' H; simpl in H |- *.
  - now injection H as <- <- <- <-.
  - rewrite (bind_spec _ _ _ _ _ (cget_spec i st)) in H. destruct (tget (scmap st) i) as [[|a ls]|].
    + now injection H as <- <- <- <-.
    + rewrite (bind_spec _ _ _ _ _ (lookupM_spec a st)) in H. destruct (lookup (svals st) a) as [[|]|].
      * now apply IH.
      * now injection H as <- <- <- <-.
      * destruct (assignM y a (S i) st) as [y1 st1] eqn:Hassign.
        rewrite (bind_spec _ _ _ _ _ Hassign) in H. rewrite <- (assignM_spec y y1 _ _ st st1 Hassign).
        now apply IH.
    + now apply IH.
Qed.

(* The first position from c on with an unassigned literal, as skip_from. *)
Fixpoint skip_fromM (n fuel c: nat): M nat :=
match fuel with
| 0       => ret c
| S fuel' =>
  if c <? n then
    bind (aget c) (fun (l: Lit) =>
    bind (lookup_undefM l) (fun (u: bool) => if u then ret c else skip_fromM n fuel' (S c)))
  else ret c
end.

Lemma skip_fromM_spec: forall (n fuel c: nat) (st: Store),
  skip_fromM n fuel c st = (skip_from (svals st) (salls st) n fuel c, st).
Proof.
  intros n fuel. induction fuel as [|fuel IH]; intros c st; simpl.
  - reflexivity.
  - destruct (c <? n).
    + rewrite (bind_spec _ _ _ _ _ (aget_spec c st)), (bind_spec _ _ _ _ _ (lookup_undefM_spec _ st)). simpl.
      destruct (lookup_undef (svals st) (tget (salls st) c)).
      * reflexivity.
      * apply IH.
    + reflexivity.
Qed.

Section Analysis.
  (* The number of literals of c at level d, as count_level. *)
  Fixpoint count_levelM (d: nat) (c: list Lit): M nat :=
  match c with
  | []      => ret 0
  | y :: c' =>
    bind (dget (extract y)) (fun (k: nat) =>
    bind (count_levelM d c') (fun (n: nat) => ret (if Nat.eqb k d then S n else n)))
  end.

  Lemma count_levelM_spec: forall (d: nat) (c: list Lit) (st: Store),
    count_levelM d c st = (count_level (slvl st) d c, st).
  Proof.
    intros d c st. induction c as [|y c IH]; simpl.
    - reflexivity.
    - rewrite (bind_spec _ _ _ _ _ (dget_spec (extract y) st)), (bind_spec _ _ _ _ _ IH). unfold count_level. simpl.
      destruct (Nat.eqb (tget (slvl st) (extract y)) d).
      + reflexivity.
      + reflexivity.
  Qed.

  (* Mark the literals of c as b, as set_marks. *)
  Fixpoint set_marksM (c: list Lit) (b: bool): M unit :=
  match c with
  | []      => ret tt
  | y :: c' => bind (mset (lit_key y) b) (fun _ => set_marksM c' b)
  end.

  Lemma set_marksM_spec: forall (c: list Lit) (b: bool) (st: Store),
    set_marksM c b st = (tt, with_mrk st (set_marks (smrk st) c b)).
  Proof.
    intros c b. induction c as [|y c IH]; intros st; simpl.
    - now destruct st.
    - rewrite (bind_spec _ _ _ _ _ (mset_spec (lit_key y) b _)). apply IH.
  Qed.

  (* Add the unmarked literals of r other than x to c, as add_unmarked. *)
  Fixpoint add_unmarkedM (d: nat) (x: Lit) (r c: list Lit) (k: nat): M (list Lit * nat) :=
  match r with
  | []      => ret (c, k)
  | y :: r' =>
    bind (mget (lit_key y)) (fun (b: bool) =>
    if (y =? x) || b then add_unmarkedM d x r' c k
    else
    bind (mset (lit_key y) true) (fun _ =>
    bind (dget (extract y)) (fun (ky: nat) =>
    add_unmarkedM d x r' (y :: c) (if Nat.eqb ky d then S k else k))))
  end.

  Lemma add_unmarkedM_spec: forall (d: nat) (x: Lit) (r c c': list Lit) (k k': nat) (mk': Table bool) (st: Store),
    add_unmarked (slvl st) d (smrk st) x r c k = (c', mk', k') -> add_unmarkedM d x r c k st = ((c', k'), with_mrk st mk').
  Proof.
    intros d x r. induction r as [|y r IH]; intros c c' k k' mk' st H; simpl in H |- *.
    - injection H as <- <- <-. now destruct st.
    - rewrite (bind_spec _ _ _ _ _ (mget_spec (lit_key y) _)). destruct ((y =? x) || tget (smrk st) (lit_key y)).
      + now apply IH.
      + rewrite (bind_spec _ _ _ _ _ (mset_spec (lit_key y) true _)), (bind_spec _ _ _ _ _ (dget_spec (extract y) _)).
        apply (IH _ c' _ k' mk' (with_mrk st (tset (smrk st) (lit_key y) true)) H).
  Qed.

  (* Resolve c with r on x using the marks, as resolve_marked. *)
  Definition resolve_markedM (d: nat) (c r: list Lit) (x: Lit) (k: nat): M (list Lit * nat) :=
  let nx := ¬x in
  bind (mset (lit_key nx) false) (fun _ => add_unmarkedM d x r (filter (fun (y: Lit) => negb (y =? nx)) c) (k - 1)).

  Lemma resolve_markedM_spec: forall (d: nat) (c r c': list Lit) (x: Lit) (k k': nat) (mk': Table bool) (st: Store),
    resolve_marked (slvl st) d (smrk st) c r x k = (c', mk', k') ->
    resolve_markedM d c r x k st = ((c', k'), with_mrk st mk').
  Proof.
    intros d c r c' x k k' mk' st H. unfold resolve_markedM, resolve_marked in *. cbv zeta.
    rewrite (bind_spec _ _ _ _ _ (mset_spec (lit_key (¬x)) false _)).
    apply (add_unmarkedM_spec _ _ _ _ c' _ k' mk' (with_mrk st (tset (smrk st) (lit_key (¬x)) false)) H).
  Qed.

  (* Resolve c with the reasons of the literals of the last decision level of m, as analyze. *)
  Fixpoint analyzeM (d: nat) (m: PA) (c: list Lit) (k: nat): M (list Lit) :=
  match m with
  | ⟨m', t⟩ =>
    if Nat.leb k 1 then ret c
    else
    bind (mget (lit_key (¬t))) (fun (b: bool) =>
    if b then
      bind (rget (extract t)) (fun (j: nat) =>
      match j with
      | 0   => ret c
      | S i =>
        bind (cget i) (fun (ci: option (list Lit)) =>
        match ci with
        | Some r => bind (resolve_markedM d c r t k) (fun (p: list Lit * nat) => analyzeM d m' (fst p) (snd p))
        | None   => ret c
        end)
      end)
    else analyzeM d m' c k)
  | _ => ret c
  end.

  Lemma analyzeM_spec: forall (d: nat) (m: PA) (c c': list Lit) (k: nat) (mk': Table bool) (st: Store),
    analyze (scmap st) (srsn st) (slvl st) d m (smrk st) c k = (c', mk') -> analyzeM d m c k st = (c', with_mrk st mk').
  Proof.
    intros d m. induction m as [|m IH t|m IH t]; intros c c' k mk' st H; simpl in H |- *.
    - injection H as <- <-. now destruct st.
    - destruct (Nat.leb k 1).
      + injection H as <- <-. now destruct st.
      + rewrite (bind_spec _ _ _ _ _ (mget_spec (lit_key (¬t)) _)). simpl. destruct (tget (smrk st) (lit_key (¬t))).
        * rewrite (bind_spec _ _ _ _ _ (rget_spec (extract t) _)). simpl. destruct (tget (srsn st) (extract t)) as [|i].
          -- injection H as <- <-. now destruct st.
          -- rewrite (bind_spec _ _ _ _ _ (cget_spec i _)). simpl. destruct (tget (scmap st) i) as [r|].
             ++ destruct (resolve_marked (slvl st) d (smrk st) c r t k) as [[c1 mk1] k1] eqn:Hres.
                rewrite (bind_spec _ _ _ _ _ (resolve_markedM_spec d c r c1 t k k1 mk1 st Hres)). simpl.
                apply (IH c1 c' k1 mk' (with_mrk st mk1) H).
             ++ injection H as <- <-. now destruct st.
        * now apply IH.
    - injection H as <- <-. now destruct st.
  Qed.

  (* The first literal of c at level d, as the search in plan. *)
  Fixpoint find_levelM (d: nat) (c: list Lit): M (option Lit) :=
  match c with
  | []      => ret None
  | y :: c' => bind (dget (extract y)) (fun (k: nat) => if Nat.eqb k d then ret (Some y) else find_levelM d c')
  end.

  Lemma find_levelM_spec: forall (d: nat) (c: list Lit) (st: Store),
    find_levelM d c st = (find (fun (y: Lit) => Nat.eqb (tget (slvl st) (extract y)) d) c, st).
  Proof.
    intros d c st. induction c as [|y c IH]; simpl.
    - reflexivity.
    - rewrite (bind_spec _ _ _ _ _ (dget_spec (extract y) st)). destruct (Nat.eqb (tget (slvl st) (extract y)) d).
      + reflexivity.
      + apply IH.
  Qed.

  (* The levels of the literals of c. *)
  Fixpoint levelsM (c: list Lit): M (list nat) :=
  match c with
  | []      => ret []
  | y :: c' => bind (dget (extract y)) (fun (k: nat) => bind (levelsM c') (fun (ks: list nat) => ret (k :: ks)))
  end.

  Lemma levelsM_spec: forall (c: list Lit) (st: Store),
    levelsM c st = (map (fun (y: Lit) => tget (slvl st) (extract y)) c, st).
  Proof.
    intros c st. induction c as [|y c IH]; simpl.
    - reflexivity.
    - now rewrite (bind_spec _ _ _ _ _ (dget_spec (extract y) st)), (bind_spec _ _ _ _ _ IH).
  Qed.

  (* Whether every literal of c is false. *)
  Fixpoint all_falseM (c: list Lit): M bool :=
  match c with
  | []      => ret true
  | y :: c' => bind (not_falseM y) (fun (b: bool) => if b then ret false else all_falseM c')
  end.

  Lemma all_falseM_spec: forall (c: list Lit) (st: Store),
    all_falseM c st = (forallb (fun (y: Lit) => negb (not_false (svals st) y)) c, st).
  Proof.
    intros c st. induction c as [|y c IH]; simpl.
    - reflexivity.
    - rewrite (bind_spec _ _ _ _ _ (not_falseM_spec y st)). destruct (not_false (svals st) y).
      + reflexivity.
      + apply IH.
  Qed.

  (* Whether a literal of n other than nu has its negation marked, as marked_neg. *)
  Fixpoint marked_negM (nu: Lit) (n: PA): M bool :=
  match n with
  | ⟨⟩     => ret false
  | ⟨n, x⟩ => bind (mget (neg_key x)) (fun (b: bool) => if b && negb (x =? nu) then ret true else marked_negM nu n)
  | ⟨n; x⟩ => bind (mget (neg_key x)) (fun (b: bool) => if b && negb (x =? nu) then ret true else marked_negM nu n)
  end.

  Lemma marked_negM_spec: forall (nu: Lit) (n: PA) (st: Store), marked_negM nu n st = (marked_neg (smrk st) nu n, st).
  Proof.
    intros nu n st. induction n as [|n IH x|n IH x]; simpl.
    - reflexivity.
    - rewrite (bind_spec _ _ _ _ _ (mget_spec (neg_key x) st)). now destruct (tget (smrk st) (neg_key x) && negb (x =? nu)).
    - rewrite (bind_spec _ _ _ _ _ (mget_spec (neg_key x) st)). now destruct (tget (smrk st) (neg_key x) && negb (x =? nu)).
  Qed.

  (* The backjump for c, as plan. *)
  Definition planM (d: nat) (m: PA) (c: list Lit): M (option (Lit * (PA * Lit * PA))) :=
  bind (find_levelM d c) (fun (r: option Lit) =>
  match r with
  | None   => ret None
  | Some u =>
    let rest := filter (fun (y: Lit) => negb (y =? u)) c in
    bind (levelsM rest) (fun (ks: list nat) =>
    match split_levels (d - S (list_max ks)) m with
    | None             => ret None
    | Some (mt, d', n) =>
      let nu := ¬u in
      bind (all_falseM c) (fun (b: bool) =>
      bind (marked_negM nu ⟨∅; d'⟩) (fun (b_d: bool) =>
      bind (marked_negM nu n) (fun (b_n: bool) =>
      ret (if b && ((d' =? nu) || in_trail nu n) && negb (b_d || b_n)
           then Some (u, (mt, d', n))
           else None))))
    end)
  end).

  Lemma planM_spec: forall (d: nat) (m: PA) (c: list Lit) (st: Store),
    planM d m c st = (plan (svals st) (slvl st) d m (smrk st) c, st).
  Proof.
    intros d m c st. unfold planM, plan. rewrite (bind_spec _ _ _ _ _ (find_levelM_spec d c st)).
    destruct (find (fun (y: Lit) => Nat.eqb (tget (slvl st) (extract y)) d) c) as [u|].
    - cbv zeta. rewrite (bind_spec _ _ _ _ _ (levelsM_spec _ st)).
      destruct (split_levels _ m) as [[[mt d'] n]|].
      + cbv zeta. rewrite (bind_spec _ _ _ _ _ (all_falseM_spec c st)), (bind_spec _ _ _ _ _ (marked_negM_spec _ _ st)).
        now rewrite (bind_spec _ _ _ _ _ (marked_negM_spec _ _ st)).
      + reflexivity.
    - reflexivity.
  Qed.

  (* Remove the values of the literals of n and then d, as unassign_segment. *)
  Fixpoint unassign_segmentM (d: Lit) (n: PA): M unit :=
  match n with
  | ⟨⟩     => vset (extract d) None
  | ⟨n, x⟩ => bind (vset (extract x) None) (fun _ => unassign_segmentM d n)
  | ⟨n; x⟩ => bind (vset (extract x) None) (fun _ => unassign_segmentM d n)
  end.

  Lemma unassign_segmentM_spec: forall (d: Lit) (n: PA) (st: Store),
    unassign_segmentM d n st = (tt, with_vals st (unassign_segment (svals st) d n)).
  Proof.
    intros d n. induction n as [|n IH x|n IH x]; intros st; simpl.
    - reflexivity.
    - rewrite (bind_spec _ _ _ _ _ (vset_spec (extract x) None _)). apply IH.
    - rewrite (bind_spec _ _ _ _ _ (vset_spec (extract x) None _)). apply IH.
  Qed.

  (* Remove the values of the last decision level of m, as unassign_level. *)
  Fixpoint unassignM (m: PA): M unit :=
  match m with
  | ⟨⟩     => ret tt
  | ⟨m, l⟩ => bind (vset (extract l) None) (fun _ => unassignM m)
  | ⟨m; l⟩ => vset (extract l) None
  end.

  Lemma unassignM_spec: forall (m: PA) (st: Store), unassignM m st = (tt, with_vals st (unassign_level (svals st) m)).
  Proof.
    intros m. induction m as [|m IH l|m IH l]; intros st; simpl.
    - now destruct st.
    - rewrite (bind_spec _ _ _ _ _ (vset_spec (extract l) None _)). apply IH.
    - reflexivity.
  Qed.
End Analysis.

(* The frame after jumping back, as jump. *)
Definition jump_frame (y: Frame) (len c: nat) (sv: list nat) (d: nat): Frame :=
mkFrame len len (fshorts y) (fnlits y) c sv d (fnvars y).

(* Resolve the conflict on clause i, as resolve. *)
Definition resolveM (m: PA) (f: CNF) (y: Frame) (i: nat): M (option (State * Frame)) :=
bind (cget i) (fun (ci: option (list Lit)) =>
match ci with
| None    => ret None
| Some ls =>
  match split_last_decision m with
  | None         => ret (Some (fail, y))
  | Some (m', l) =>
    bind (set_marksM ls true) (fun _ =>
    bind (count_levelM (fdl y) ls) (fun (k: nat) =>
    bind (analyzeM (fdl y) m ls k) (fun (c: list Lit) =>
    bind (set_marksM c true) (fun _ =>
    bind (planM (fdl y) m c) (fun (p: option (Lit * (PA * Lit * PA))) =>
    bind (set_marksM c false) (fun _ =>
    match p with
    | Some (u, (mt, d, n)) =>
      match skipn (decisions n) (fsaved y) with
      | c0 :: sv =>
        bind (unassign_segmentM d n) (fun _ =>
        bind (assignM (jump_frame y (ftlen y - S (PA.length n)) c0 sv (fdl y - S (decisions n))) u 0) (fun (y': Frame) =>
        ret (Some (state ⟨mt, u⟩ f, y'))))
      | []       => ret None
      end
    | None =>
      match fsaved y with
      | c0 :: sv =>
        bind (unassignM m) (fun _ =>
        bind (assignM (jump_frame y (ftlen y - S (level_length m)) c0 sv (fdl y - 1)) (¬l) 0) (fun (y': Frame) =>
        ret (Some (state ⟨m', (¬l)⟩ f, y'))))
      | []       => ret None
      end
    end))))))
  end
end).

(* The result of a step on the store, as a result on the context. *)
Definition on_context (st: Store) (r: option (State * Frame)): option (State * Ctx) :=
option_map (fun (p: State * Frame) => (fst p, combine (snd p) st)) r.

Lemma resolveM_spec: forall (m: PA) (f: CNF) (y: Frame) (i: nat) (r: option (State * Frame)) (st st': Store),
  resolveM m f y i st = (r, st') -> resolve m f (combine y st) i = on_context st' r.
Proof.
  intros m f y i r st st' H. unfold resolveM in H. unfold resolve. simpl.
  rewrite (bind_spec _ _ _ _ _ (cget_spec i st)) in H. destruct (tget (scmap st) i) as [ls|].
  - destruct (split_last_decision m) as [[m' l]|].
    + rewrite (bind_spec _ _ _ _ _ (set_marksM_spec ls true st)) in H.
      rewrite (bind_spec _ _ _ _ _ (count_levelM_spec _ ls _)) in H. simpl in H.
      destruct (analyze (scmap st) (srsn st) (slvl st) (fdl y) m (set_marks (smrk st) ls true) ls
        (count_level (slvl st) (fdl y) ls)) as [c mk] eqn:Hanalyze.
      rewrite (bind_spec _ _ _ _ _ (analyzeM_spec (fdl y) m ls c _ mk (with_mrk st (set_marks (smrk st) ls true))
        Hanalyze)) in H.
      rewrite (bind_spec _ _ _ _ _ (set_marksM_spec c true _)) in H.
      rewrite (bind_spec _ _ _ _ _ (planM_spec _ m c _)) in H.
      rewrite (bind_spec _ _ _ _ _ (set_marksM_spec c false _)) in H. simpl in H.
      destruct (plan (svals st) (slvl st) (fdl y) m (set_marks mk c true) c) as [[u [[mt d] n]]|].
      * destruct (skipn (decisions n) (fsaved y)) as [|c0 sv].
        -- now injection H as <- <-.
        -- rewrite (bind_spec _ _ _ _ _ (unassign_segmentM_spec d n _)) in H.
           destruct (assignM (jump_frame y (ftlen y - S (PA.length n)) c0 sv (fdl y - S (decisions n))) u 0
             (with_vals (with_mrk (with_mrk (with_mrk st (set_marks (smrk st) ls true)) mk) (set_marks (set_marks mk c true) c false))
               (unassign_segment (svals st) d n))) as [y1 st1] eqn:Hassign.
           rewrite (bind_spec _ _ _ _ _ Hassign) in H. injection H as <- <-. unfold on_context. simpl.
           apply assignM_spec in Hassign. now rewrite Hassign.
      * destruct (fsaved y) as [|c0 sv].
        -- now injection H as <- <-.
        -- rewrite (bind_spec _ _ _ _ _ (unassignM_spec m _)) in H.
           destruct (assignM (jump_frame y (ftlen y - S (level_length m)) c0 sv (fdl y - 1)) (¬l) 0
             (with_vals (with_mrk (with_mrk (with_mrk st (set_marks (smrk st) ls true)) mk) (set_marks (set_marks mk c true) c false))
               (unassign_level (svals st) m))) as [y1 st1] eqn:Hassign.
           rewrite (bind_spec _ _ _ _ _ Hassign) in H. injection H as <- <-. unfold on_context. simpl.
           apply assignM_spec in Hassign. now rewrite Hassign.
    + now injection H as <- <-.
  - now injection H as <- <-.
Qed.

(* The frame without short clauses, with cursor c, and before deciding at cursor c. *)
Definition clear_frame (y: Frame): Frame :=
mkFrame (ftlen y) (fqhead y) [] (fnlits y) (fcur y) (fsaved y) (fdl y) (fnvars y).

Definition cursor_frame (y: Frame) (c: nat): Frame :=
mkFrame (ftlen y) (fqhead y) (fshorts y) (fnlits y) c (fsaved y) (fdl y) (fnvars y).

Definition open_frame (y: Frame) (c: nat): Frame :=
mkFrame (ftlen y) (fqhead y) (fshorts y) (fnlits y) c (c :: fsaved y) (S (fdl y)) (fnvars y).

(* One solver step on the store, as step. *)
Definition stepM (s: State) (y: Frame): M (option (State * Frame)) :=
match s with
| fail      => ret None
| state m f =>
  bind (check_shortsM (fshorts y) m y) (fun (r1: PA * Frame * option nat) =>
  match r1 with
  | (m1, y1, Some i) => resolveM m1 f y1 i
  | (m1, y1, None)   =>
    bind (propagateM (S (fnvars y1)) m1 (clear_frame y1)) (fun (r2: PA * Frame * option nat) =>
    match r2 with
    | (m2, y2, Some i) => resolveM m2 f y2 i
    | (m2, y2, None)   =>
      bind (skip_fromM (fnlits y2) (fnlits y2 - fcur y2) (fcur y2)) (fun (c: nat) =>
      if c <? fnlits y2 then
        bind (aget c) (fun (a: Lit) =>
        bind (phaseM a) (fun (l: Lit) =>
        bind (assignM (open_frame y2 c) l 0) (fun (y3: Frame) =>
        ret (Some (state ⟨m2; l⟩ f, y3)))))
      else if Nat.eqb (ftlen y2) (ftlen y) then ret None else ret (Some (state m2 f, cursor_frame y2 c)))
    end)
  end)
end.

Lemma stepM_spec: forall (s: State) (y: Frame) (r: option (State * Frame)) (st st': Store),
  stepM s y st = (r, st') -> step (s, combine y st) = on_context st' r.
Proof.
  intros [|m f] y r st st' H; simpl in H.
  - now injection H as <- <-.
  - cbn [step shorts combine].
    destruct (check_shortsM (fshorts y) m y st) as [[[m1 y1] r1] st1] eqn:Hcheck.
    rewrite (bind_spec _ _ _ _ _ Hcheck) in H. apply check_shortsM_spec in Hcheck. rewrite Hcheck.
    destruct r1 as [i|].
    + now apply resolveM_spec.
    + destruct (propagateM (S (fnvars y1)) m1 (clear_frame y1) st1) as [[[m2 y2] r2] st2] eqn:Hprop.
      rewrite (bind_spec _ _ _ _ _ Hprop) in H. apply propagateM_spec in Hprop.
      change (clear_shorts (combine y1 st1)) with (combine (clear_frame y1) st1). cbn [nvars combine]. rewrite Hprop.
      destruct r2 as [i|].
      * now apply resolveM_spec.
      * rewrite (bind_spec _ _ _ _ _ (skip_fromM_spec _ _ _ st2)) in H. cbn [vals alls nlits cur tlen combine].
        destruct (skip_from (svals st2) (salls st2) (fnlits y2) (fnlits y2 - fcur y2) (fcur y2) <? fnlits y2).
        -- rewrite (bind_spec _ _ _ _ _ (aget_spec _ st2)), (bind_spec _ _ _ _ _ (phaseM_spec _ st2)) in H.
           destruct (assignM (open_frame y2 (skip_from (svals st2) (salls st2) (fnlits y2) (fnlits y2 - fcur y2) (fcur y2)))
             (phase (sphs st2) (tget (salls st2) (skip_from (svals st2) (salls st2) (fnlits y2) (fnlits y2 - fcur y2)
               (fcur y2)))) 0 st2) as [y3 st3] eqn:Hassign.
           rewrite (bind_spec _ _ _ _ _ Hassign) in H. injection H as <- <-. unfold on_context. simpl.
           apply assignM_spec in Hassign. now rewrite Hassign.
        -- destruct (Nat.eqb (ftlen y2) (ftlen y)).
           ++ now injection H as <- <-.
           ++ now injection H as <- <-.
Qed.

(* The solver step on a frame and a store. The store is used linearly: it is passed on to the next step only. *)
Definition next_impl (p: State * (Frame * Store)): option (State * (Frame * Store)) :=
match p with
| (s, (y, st)) =>
  match runM (stepM s y) st with
  | (Some (s', y'), st') => Some (s', (y', st'))
  | (None, _)            => None
  end
end.

(* The frame and the store make a consistent context. *)
Definition ImpInv (s: State) (c: Frame * Store): Prop := StepInv s (combine (fst c) (snd c)).

Lemma next_impl_strategy: Strategy DPLL_BJ ImpInv next_impl.
Proof.
  destruct step_strategy as (Hfail & Hnone & Hstep). split.
  - intros [y st]. reflexivity.
  - split.
    + intros s [y st] Hinv Hnext. apply Hnone with (combine y st).
      * assumption.
      * unfold next_impl, runM in Hnext. destruct (stepM s y st) as [[[s' y']|] st'] eqn:Hstate.
        -- discriminate.
        -- now apply stepM_spec in Hstate.
    + intros s s' [y st] [y' st'] Hinv Hnext. unfold next_impl, runM in Hnext.
      destruct (stepM s y st) as [[[s'' y'']|] st''] eqn:Hstate.
      * injection Hnext as <- <- <-. apply stepM_spec in Hstate. unfold on_context in Hstate. simpl in Hstate.
        now apply (Hstep s s'' (combine y st) (combine y'' st'')).
      * discriminate.
Qed.

(* Clause k starts watching z, as add_watcher. *)
Definition add_watcherM (z: Lit) (k: nat): M unit :=
bind (lget (lit_key z)) (fun (ws: list nat) => lset (lit_key z) (ws ++ [k])).

(* Index the clauses lss from k on, as index. *)
Fixpoint indexM (k: nat) (lss: list (list Lit)) (sh: list nat): M (list nat) :=
match lss with
| []         => ret sh
| ls :: lss' =>
  bind (cset k (Some ls)) (fun _ =>
  bind (wset k (first_watches ls)) (fun _ =>
  bind (add_watcherM (fst (first_watches ls)) k) (fun _ =>
  bind (add_watcherM (snd (first_watches ls)) k) (fun _ =>
  indexM (S k) lss' (if length ls <=? 1 then k :: sh else sh)))))
end.

Lemma indexM_spec: forall (lss: list (list Lit)) (k: nat) (sh sh': list nat) (v ph: Values) (cm cm': ClauseMap)
  (w w': Watches) (wl wl': WatchLists) (trl al: Table Lit) (rs lv: Table nat) (mk: Table bool),
  index k lss cm w wl sh = (cm', w', wl', sh') ->
  indexM k lss sh (mkStore v cm w wl trl al rs lv mk ph) = (sh', mkStore v cm' w' wl' trl al rs lv mk ph).
Proof.
  intros lss. induction lss as [|ls lss IH]; intros k sh sh' v ph cm cm' w w' wl wl' trl al rs lv mk H; simpl in H |- *.
  - now injection H as <- <- <- <-.
  - cbv [bind cset wset add_watcherM lget lset with_cmap with_wat with_wls]. simpl. now apply IH.
Qed.

(* Fill the table of literals to decide on from position k, as fill. *)
Fixpoint fillM (k: nat) (ls: list Lit): M unit :=
match ls with
| []       => ret tt
| l :: ls' => bind (aset k l) (fun _ => fillM (S k) ls')
end.

Lemma fillM_spec: forall (ls: list Lit) (k: nat) (st: Store), fillM k ls st = (tt, with_alls st (fill (salls st) k ls)).
Proof.
  intros ls. induction ls as [|l ls IH]; intros k st; simpl.
  - now destruct st.
  - rewrite (bind_spec _ _ _ _ _ (aset_spec k l st)). apply IH.
Qed.

(* The frame and store of the initial state. *)
Definition initial_impl (f: CNF): Frame * Store :=
match runM (bind (fillM 0 (Clause.elements (formula_lits f))) (fun _ => indexM 0 (clause_lists f) []))
  (mkStore (tmake None) (tmake None) (tmake (Pos 0, Pos 0)) (tmake []) (tmake (Pos 0)) (tmake (Pos 0)) (tmake 0)
    (tmake 0) (tmake false) (tmake None)) with
| (sh, st) => (mkFrame 0 0 sh (length (Clause.elements (formula_lits f))) 0 [] 0 (S (max_atom_f f)), st)
end.

Lemma initial_impl_inv: forall (f: CNF), ImpInv (state ⟨⟩ f) (initial_impl f).
Proof.
  intros f. assert (Hinv := initial_ctx_inv f). unfold initial_impl, runM.
  rewrite (bind_spec _ _ _ _ _ (fillM_spec _ 0 _)). unfold initial_ctx, initial_of in Hinv.
  destruct (index 0 (clause_lists f) (tmake None) (tmake (Pos 0, Pos 0)) (tmake []) []) as [[[cm w] wl] sh] eqn:Hindex.
  cbv [with_alls]. simpl. rewrite (indexM_spec (clause_lists f) 0 [] sh _ _ (tmake None) cm (tmake (Pos 0, Pos 0)) w (tmake []) wl _ _ _ _ _
    Hindex).
  assumption.
Qed.
