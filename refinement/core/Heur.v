(* The decision heuristic: VSIDS as in MiniSat, in fixed point. Every atom has an
   activity; the analysis of a conflict bumps the atoms it marks by the bump, which grows
   after every conflict (the decay of MiniSat: the bump grows by 1/0.95 = 20/19).
   Activities and the bump are integers (Z, as C ints, and so that their bounds stay small
   terms); when one would get too large, all are divided by 2^20 (rescale), which keeps
   their order. Decisions take the most active atom of a heap.

   The heuristic is a hint: nothing about the solver's correctness depends on it. A
   decision checks that the literal it takes is unassigned, and the solver falls back to
   its cursor when the heap gives none. So no invariant of the heap is proved, only bounds
   (HeurOk), which the C code needs to stay within its arrays. *)
From Stdlib Require Import Arith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table.
From RocqSAT.refinement Require Import Lookup.

(* The state of the heuristic. *)
Record Heur: Type := mkHeur {
  act: Table Z;             (* the activity of each atom *)
  inc: Z;                   (* the bump *)
  heap: Table nat;          (* atoms, a heap by activity at positions 0 .. hsize - 1 *)
  hpos: Table (option nat); (* the position of each atom in the heap, if it is there *)
  hsize: nat;
  dlit: Table (option Lit)  (* the literal to decide on for each atom, if there is one *)
}.

(* Activities stay below act_lim, so that C adds two of them without overflow. *)
Definition act_lim: Z := 2 ^ 30.

(* Rescaling divides by 2^20. *)
Definition act_shift: Z := 2 ^ 20.

Section Operations.
  (* Divide the activities of the k atoms from a on by act_shift. *)
  Fixpoint shift_acts (t: Table Z) (a k: nat): Table Z :=
  match k with
  | 0    => t
  | S k' => shift_acts (tset t a (tget t a / act_shift)%Z) (S a) k'
  end.

  (* Divide the activities of the n atoms by act_shift, and make the bump c divided by it,
     at least 1. *)
  Definition rescale (h: Heur) (n: nat) (c: Z): Heur :=
  mkHeur (shift_acts (act h) 0 n) (Z.max 1 (c / act_shift)) (heap h) (hpos h) (hsize h)
    (dlit h).

  (* Atom b at heap position i. *)
  Definition place (h: Heur) (i b: nat): Heur :=
  mkHeur (act h) (inc h) (tset (heap h) i b) (tset (hpos h) b (Some i)) (hsize h)
    (dlit h).

  (* Move atom a up from position i while its parent has a lower activity, at most fuel
     times: the heap with the parents moved down, and the position left for a. *)
  Fixpoint up_loop (h: Heur) (a i fuel: nat): Heur * nat :=
  match fuel with
  | 0       => (h, i)
  | S fuel' =>
    if i <=? 0 then (h, i) else
    let b := tget (heap h) ((i - 1) / 2) in
    if (tget (act h) a <=? tget (act h) b)%Z then (h, i)
    else up_loop (place h i b) a ((i - 1) / 2) fuel'
  end.

  (* Move the atom at position i up (at most hsize times). *)
  Definition heap_up (h: Heur) (i: nat): Heur :=
  let a := tget (heap h) i in
  match up_loop h a i (hsize h) with
  | (h', i') => place h' i' a
  end.

  (* The child of position i to move up: the more active of 2i + 1 and 2i + 2, of the n
     positions. *)
  Definition child (h: Heur) (n i: nat): nat :=
  if S (S (2 * i)) <? n then
    if (tget (act h) (tget (heap h) (S (2 * i)))
          <? tget (act h) (tget (heap h) (S (S (2 * i)))))%Z
    then S (S (2 * i)) else S (2 * i)
  else S (2 * i).

  (* Move atom a down from position i of the n positions while a child has a higher
     activity, at most fuel times. *)
  Fixpoint down_loop (h: Heur) (n a i fuel: nat): Heur * nat :=
  match fuel with
  | 0       => (h, i)
  | S fuel' =>
    if n <=? S (2 * i) then (h, i) else
    let c := child h n i in
    let b := tget (heap h) c in
    if (tget (act h) b <=? tget (act h) a)%Z then (h, i)
    else down_loop (place h i b) n a c fuel'
  end.

  (* Move the atom at position i down (at most hsize times). *)
  Definition heap_down (h: Heur) (i: nat): Heur :=
  let a := tget (heap h) i in
  match down_loop h (hsize h) a i (hsize h) with
  | (h', i') => place h' i' a
  end.

  (* Put atom a in the heap of room n, unless it is there, is not decided on, or the heap
     is full. *)
  Definition heap_insert (h: Heur) (n a: nat): Heur :=
  match tget (hpos h) a, tget (dlit h) a with
  | None, Some _ =>
    if n <=? hsize h then h
    else heap_up (mkHeur (act h) (inc h) (tset (heap h) (hsize h) a)
                   (tset (hpos h) a (Some (hsize h))) (S (hsize h)) (dlit h)) (hsize h)
  | _, _         => h
  end.

  (* Take the atom at the top out of the non-empty heap. *)
  Definition heap_pop (h: Heur): Heur * nat :=
  let a := tget (heap h) 0 in
  let n := hsize h - 1 in
  let h1 := mkHeur (act h) (inc h) (heap h) (tset (hpos h) a None) n (dlit h) in
  if 0 <? n then (heap_down (place h1 0 (tget (heap h) n)) 0, a) else (h1, a).

  (* Raise the activity of atom a by the bump, rescaling the n atoms first if it would
     reach act_lim. *)
  Definition bump (h: Heur) (n a: nat): Heur :=
  let h1 := if (act_lim - inc h <=? tget (act h) a)%Z then rescale h n (inc h) else h in
  let h2 := mkHeur (tset (act h1) a (tget (act h1) a + inc h1)%Z) (inc h1) (heap h1)
              (hpos h1) (hsize h1) (dlit h1) in
  match tget (hpos h2) a with
  | Some i => heap_up h2 i
  | None   => h2
  end.

  (* Raise the bump by 1/19 after a conflict, rescaling the n atoms when it reaches
     act_lim / 2. *)
  Definition decay (h: Heur) (n: nat): Heur :=
  let c := (inc h + inc h / 19)%Z in
  if (act_lim / 2 <=? c)%Z then rescale h n c
  else mkHeur (act h) c (heap h) (hpos h) (hsize h) (dlit h).

  (* Take atoms out of the heap, at most fuel of them, until the literal of one is
     unassigned in v. *)
  Fixpoint pick (v: Values) (h: Heur) (fuel: nat): Heur * option Lit :=
  match fuel with
  | 0       => (h, None)
  | S fuel' =>
    if hsize h <=? 0 then (h, None) else
    match heap_pop h with
    | (h1, b) =>
      match tget (dlit h1) b with
      | Some l => if lookup_undef v l then (h1, Some l) else pick v h1 fuel'
      | None   => pick v h1 fuel'
      end
    end
  end.

  (* Put the atoms of the trail positions j .. q - 1 back in the heap of room n, from q -
     1 down; k = q - j positions to go. *)
  Fixpoint reinsert (h: Heur) (tr: Table Lit) (n j q k: nat): Heur :=
  match k with
  | 0    => h
  | S k' => reinsert (heap_insert h n (extract (tget tr (q - 1)))) tr n j (q - 1) k'
  end.

  (* The heuristic for n atoms before its literals to decide on are added: empty, with no
     literals. *)
  Definition empty_heur (nl: nat): Heur :=
  mkHeur (tmake 0%Z) (Z.of_nat nl + 1) (tmake 0) (tmake None) 0 (tmake None).

  (* Add the literals to decide on alls from position k on, k2 = nl - k of the nl of them:
     the first literal of each atom is its literal, with activity nl - k, and the atom
     goes into the heap of room n. *)
  Fixpoint add_atoms (h: Heur) (alls: Table Lit) (n nl k k2: nat): Heur :=
  match k2 with
  | 0     => h
  | S k2' =>
    let l := tget alls k in
    let b := extract l in
    match tget (dlit h) b with
    | None   =>
      add_atoms (heap_insert (mkHeur (tset (act h) b (Z.of_nat (nl - k))) (inc h) (heap h)
                                (hpos h) (hsize h) (tset (dlit h) b (Some l))) n b)
        alls n nl (S k) k2'
    | Some _ => add_atoms h alls n nl (S k) k2'
    end
  end.

  (* The initial heuristic for n atoms and the nl literals to decide on alls. *)
  Definition init_heur (alls: Table Lit) (n nl: nat): Heur :=
  add_atoms (empty_heur nl) alls n nl 0 nl.
End Operations.

(* The property P holds for every literal to decide on of h. *)
Abbreviation DlitAll P h := (forall (a: nat) (l: Lit), tget (dlit h) a = Some l -> P l).

Section Dlit.
  (* No operation but add_atoms changes the literals to decide on. *)
  Lemma up_loop_dlit: forall (h: Heur) (a i fuel: nat),
    dlit (fst (up_loop h a i fuel)) = dlit h.
  Proof.
    intros h a i fuel. revert h i.
    induction fuel as [|fuel IH]; intros h i; cbn [up_loop].
    - reflexivity.
    - destruct (i <=? 0).
      + reflexivity.
      + destruct (_ <=? _)%Z.
        * reflexivity.
        * rewrite IH. reflexivity.
  Qed.

  Lemma heap_up_dlit: forall (h: Heur) (i: nat), dlit (heap_up h i) = dlit h.
  Proof.
    intros h i. unfold heap_up.
    pose proof (up_loop_dlit h (tget (heap h) i) i (hsize h)) as Hd.
    destruct (up_loop h (tget (heap h) i) i (hsize h)) as [h' i']. cbn [fst] in Hd.
    cbn [place dlit]. assumption.
  Qed.

  Lemma down_loop_dlit: forall (h: Heur) (n a i fuel: nat),
    dlit (fst (down_loop h n a i fuel)) = dlit h.
  Proof.
    intros h n a i fuel. revert h i.
    induction fuel as [|fuel IH]; intros h i; cbn [down_loop].
    - reflexivity.
    - destruct (n <=? S (2 * i)).
      + reflexivity.
      + destruct (_ <=? _)%Z.
        * reflexivity.
        * rewrite IH. reflexivity.
  Qed.

  Lemma heap_down_dlit: forall (h: Heur) (i: nat), dlit (heap_down h i) = dlit h.
  Proof.
    intros h i. unfold heap_down.
    pose proof (down_loop_dlit h (hsize h) (tget (heap h) i) i (hsize h)) as Hd.
    destruct (down_loop h (hsize h) (tget (heap h) i) i (hsize h)) as [h' i'].
    cbn [fst] in Hd. cbn [place dlit]. assumption.
  Qed.

  Lemma heap_insert_dlit: forall (h: Heur) (n a: nat), dlit (heap_insert h n a) = dlit h.
  Proof.
    intros h n a. unfold heap_insert.
    destruct (tget (hpos h) a) as [i|], (tget (dlit h) a) as [l|].
    - reflexivity.
    - reflexivity.
    - destruct (n <=? hsize h).
      + reflexivity.
      + rewrite heap_up_dlit. reflexivity.
    - reflexivity.
  Qed.

  Lemma heap_pop_dlit: forall (h: Heur), dlit (fst (heap_pop h)) = dlit h.
  Proof.
    intros h. unfold heap_pop. destruct (0 <? hsize h - 1).
    - cbn [fst]. rewrite heap_down_dlit. reflexivity.
    - reflexivity.
  Qed.

  Lemma rescale_dlit: forall (h: Heur) (n: nat) (c: Z), dlit (rescale h n c) = dlit h.
  Proof. reflexivity. Qed.

  Lemma bump_dlit: forall (h: Heur) (n a: nat), dlit (bump h n a) = dlit h.
  Proof.
    intros h n a. unfold bump.
    assert (Hh1: dlit (if (act_lim - inc h <=? tget (act h) a)%Z then rescale h n (inc h)
                       else h) = dlit h).
    { destruct (_ <=? _)%Z.
      - apply rescale_dlit.
      - reflexivity. }
    destruct (tget (hpos _) a) as [i|].
    - rewrite heap_up_dlit. cbn [dlit]. assumption.
    - cbn [dlit]. assumption.
  Qed.

  Lemma decay_dlit: forall (h: Heur) (n: nat), dlit (decay h n) = dlit h.
  Proof.
    intros h n. unfold decay. destruct (_ <=? _)%Z; reflexivity.
  Qed.

  Lemma pick_dlit: forall (v: Values) (h: Heur) (fuel: nat),
    dlit (fst (pick v h fuel)) = dlit h.
  Proof.
    intros v h fuel. revert h. induction fuel as [|fuel IH]; intros h; cbn [pick].
    - reflexivity.
    - destruct (hsize h <=? 0).
      + reflexivity.
      + pose proof (heap_pop_dlit h) as Hpop.
        destruct (heap_pop h) as [h1 b]. cbn [fst] in Hpop.
        destruct (tget (dlit h1) b) as [l|].
        * destruct (lookup_undef v l).
          -- assumption.
          -- rewrite IH. assumption.
        * rewrite IH. assumption.
  Qed.

  Lemma reinsert_dlit: forall (h: Heur) (tr: Table Lit) (n j q k: nat),
    dlit (reinsert h tr n j q k) = dlit h.
  Proof.
    intros h tr n j q k. revert h q. induction k as [|k IH]; intros h q; cbn [reinsert].
    - reflexivity.
    - rewrite IH. apply heap_insert_dlit.
  Qed.

  (* add_atoms adds literals to decide on from alls at positions k .. k + k2 - 1: a
     property of these and of the literals of h holds for all literals of the result. *)
  Lemma add_atoms_dlit: forall (P: Lit -> Prop) (h: Heur) (alls: Table Lit)
    (n nl k k2: nat),
    DlitAll P h -> (forall (j: nat), k <= j < k + k2 -> P (tget alls j)) ->
    DlitAll P (add_atoms h alls n nl k k2).
  Proof.
    intros P h alls n nl k k2. revert h k.
    induction k2 as [|k2 IH]; intros h k Hh Hall; cbn [add_atoms].
    - assumption.
    - destruct (tget (dlit h) (extract (tget alls k))) as [l'|].
      + apply IH.
        * assumption.
        * intros j Hj. apply Hall. lia.
      + apply IH.
        * intros a l Hl. rewrite heap_insert_dlit in Hl. cbn [dlit] in Hl.
          rewrite tget_tset in Hl. destruct (Nat.eq_dec (extract (tget alls k)) a).
          -- injection Hl as <-. apply Hall. lia.
          -- apply (Hh a). assumption.
        * intros j Hj. apply Hall. lia.
  Qed.

  (* A property of the literals to decide on alls holds for those of init_heur. *)
  Lemma init_heur_dlit: forall (P: Lit -> Prop) (alls: Table Lit) (n nl: nat),
    (forall (j: nat), j < nl -> P (tget alls j)) -> DlitAll P (init_heur alls n nl).
  Proof.
    intros P alls n nl Hall a l Hl. unfold init_heur in Hl.
    apply (add_atoms_dlit P (empty_heur nl) alls n nl 0 nl) with a.
    - intros a' l' Hl'. cbn [empty_heur dlit] in Hl'. rewrite tget_tmake in Hl'.
      discriminate.
    - intros j Hj. apply Hall. lia.
    - assumption.
  Qed.

  (* A literal pick gives is unassigned, and one of the literals to decide on. *)
  Lemma pick_some: forall (v: Values) (h h': Heur) (fuel: nat) (l: Lit),
    pick v h fuel = (h', Some l) ->
    lookup v l = None /\ exists (b: nat), tget (dlit h) b = Some l.
  Proof.
    intros v h h' fuel l. revert h.
    induction fuel as [|fuel IH]; intros h Hpick; cbn [pick] in Hpick.
    - discriminate.
    - destruct (hsize h <=? 0).
      + discriminate.
      + pose proof (heap_pop_dlit h) as Hpop.
        destruct (heap_pop h) as [h1 b]. cbn [fst] in Hpop.
        destruct (tget (dlit h1) b) as [l'|] eqn:Hb.
        * destruct (lookup_undef v l') eqn:Hu.
          -- injection Hpick as _ <-. split.
             ++ unfold lookup_undef in Hu. destruct (lookup v l').
                ** discriminate.
                ** reflexivity.
             ++ exists b. rewrite <- Hpop. assumption.
          -- rewrite <- Hpop. apply (IH h1 Hpick).
        * rewrite <- Hpop. apply (IH h1 Hpick).
  Qed.
  #[global] Arguments pick_some {v h h' fuel l}.
End Dlit.

(* The bounds the C code needs to stay within its arrays and ints, for n atoms: activities
   from 0 below act_lim, the bump from 1 below act_lim / 2, heap entries and positions
   below n, at most n atoms in the heap, and literals to decide on of atoms below n.
   Nothing more about the heap is needed: it is a hint. *)
Record HeurOk {n: nat} {h: Heur}: Prop := {
  ho_act: forall (a: nat), a < n -> (0 <= tget (act h) a < act_lim)%Z;
  ho_inc: (1 <= inc h < act_lim / 2)%Z;
  ho_heap: forall (i: nat), i < n -> tget (heap h) i < n;
  ho_hpos: forall (a i: nat), a < n -> tget (hpos h) a = Some i -> i < n;
  ho_hsize: hsize h <= n;
  ho_dlit: forall (a: nat) (l: Lit), a < n -> tget (dlit h) a = Some l -> extract l < n
}.
Arguments HeurOk : clear implicits.

Section Setters.
  (* One field of the heuristic at a time, as the stores of the C code change it. *)
  Definition set_act (h: Heur) (a: nat) (v: Z): Heur :=
  mkHeur (tset (act h) a v) (inc h) (heap h) (hpos h) (hsize h) (dlit h).

  Definition set_inc (h: Heur) (v: Z): Heur :=
  mkHeur (act h) v (heap h) (hpos h) (hsize h) (dlit h).

  Definition set_heap (h: Heur) (i b: nat): Heur :=
  mkHeur (act h) (inc h) (tset (heap h) i b) (hpos h) (hsize h) (dlit h).

  Definition set_hpos (h: Heur) (a: nat) (o: option nat): Heur :=
  mkHeur (act h) (inc h) (heap h) (tset (hpos h) a o) (hsize h) (dlit h).

  Definition set_hsize (h: Heur) (n: nat): Heur :=
  mkHeur (act h) (inc h) (heap h) (hpos h) n (dlit h).

  Definition set_dlit (h: Heur) (a: nat) (o: option Lit): Heur :=
  mkHeur (act h) (inc h) (heap h) (hpos h) (hsize h) (tset (dlit h) a o).

  Variables (n: nat) (h: Heur).
  Hypothesis Hok: HeurOk n h.

  (* Each setter keeps the bounds when the new value is within them. *)
  Lemma heur_ok_act: forall (a: nat) (v: Z),
    (0 <= v < act_lim)%Z -> HeurOk n (set_act h a v).
  Proof.
    intros a v Hv. destruct Hok as [Hact Hinc Hheap Hhpos Hhsize Hdlit]. split.
    - intros a' Ha'. cbn [set_act act]. rewrite tget_tset.
      destruct (Nat.eq_dec a a') as [<- | Hne].
      + assumption.
      + apply Hact. assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
  Qed.

  Lemma heur_ok_inc: forall (v: Z), (1 <= v < act_lim / 2)%Z -> HeurOk n (set_inc h v).
  Proof.
    intros v Hv. destruct Hok as [Hact Hinc Hheap Hhpos Hhsize Hdlit]. split; assumption.
  Qed.

  Lemma heur_ok_heap: forall (i b: nat), b < n -> HeurOk n (set_heap h i b).
  Proof.
    intros i b Hb. destruct Hok as [Hact Hinc Hheap Hhpos Hhsize Hdlit]. split.
    - assumption.
    - assumption.
    - intros i' Hi'. cbn [set_heap heap]. rewrite tget_tset.
      destruct (Nat.eq_dec i i') as [<- | Hne].
      + assumption.
      + apply Hheap. assumption.
    - assumption.
    - assumption.
    - assumption.
  Qed.

  Lemma heur_ok_hpos: forall (a: nat) (o: option nat),
    (forall (i: nat), o = Some i -> i < n) -> HeurOk n (set_hpos h a o).
  Proof.
    intros a o Ho. destruct Hok as [Hact Hinc Hheap Hhpos Hhsize Hdlit]. split.
    - assumption.
    - assumption.
    - assumption.
    - intros a' i Ha' Hi. cbn [set_hpos hpos] in Hi. rewrite tget_tset in Hi.
      destruct (Nat.eq_dec a a') as [<- | Hne].
      + apply Ho. assumption.
      + apply (Hhpos a' i Ha' Hi).
    - assumption.
    - assumption.
  Qed.

  Lemma heur_ok_hsize: forall (k: nat), k <= n -> HeurOk n (set_hsize h k).
  Proof.
    intros k Hk. destruct Hok as [Hact Hinc Hheap Hhpos Hhsize Hdlit]. split; assumption.
  Qed.

  Lemma heur_ok_dlit: forall (a: nat) (o: option Lit),
    (forall (l: Lit), o = Some l -> extract l < n) -> HeurOk n (set_dlit h a o).
  Proof.
    intros a o Ho. destruct Hok as [Hact Hinc Hheap Hhpos Hhsize Hdlit]. split.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - intros a' l Ha' Hl. cbn [set_dlit dlit] in Hl. rewrite tget_tset in Hl.
      destruct (Nat.eq_dec a a') as [<- | Hne].
      + apply Ho. assumption.
      + apply (Hdlit a' l Ha' Hl).
  Qed.
End Setters.

(* The child heap_down looks at is a position of the heap. *)
Lemma child_lt: forall (h: Heur) (n i: nat), (S (2 * i) < n)%nat ->
  (child h n i < n)%nat.
Proof.
  intros h n i Hi. unfold child.
  destruct (Nat.ltb_spec (S (S (2 * i))) n).
  - destruct (_ <? _)%Z; assumption.
  - assumption.
Qed.

(* The atom heap_pop takes out is the one at the top. *)
Lemma heap_pop_snd: forall (h: Heur), snd (heap_pop h) = tget (heap h) 0.
Proof.
  intros h. unfold heap_pop. destruct (0 <? hsize h - 1)%nat; reflexivity.
Qed.

(* Reinserting from q > j on is inserting the atom at q - 1 and reinserting from q - 1
   on. *)
Lemma reinsert_last: forall (h: Heur) (tr: Table Lit) (n j q: nat), (j < q)%nat ->
  reinsert (heap_insert h n (extract (tget tr (q - 1)))) tr n j (q - 1) (q - 1 - j)
  = reinsert h tr n j q (q - j).
Proof.
  intros h tr n j q Hjq. replace (q - j)%nat with (S (q - 1 - j)) by lia.
  reflexivity.
Qed.

(* The bump below act_lim / 2 is also below act_lim. *)
Lemma half_lim: (act_lim / 2 < act_lim)%Z.
Proof. reflexivity. Qed.

(* shift_acts from a0 on leaves the activities below a0 alone. *)
Lemma shift_acts_below: forall (k: nat) (t: Table Z) (a0 a: nat), (a < a0)%nat ->
  tget (shift_acts t a0 k) a = tget t a.
Proof.
  intros k. induction k as [|k IH]; intros t a0 a Ha; cbn [shift_acts].
  - reflexivity.
  - rewrite IH by lia. apply tget_tset_other. lia.
Qed.

(* shift_acts divides the activities of the k atoms from a0 on by act_shift. *)
Lemma shift_acts_in: forall (k: nat) (t: Table Z) (a0 a: nat), (a0 <= a < a0 + k)%nat ->
  tget (shift_acts t a0 k) a = (tget t a / act_shift)%Z.
Proof.
  intros k. induction k as [|k IH]; intros t a0 a Ha; cbn [shift_acts].
  - lia.
  - destruct (Nat.eq_dec a0 a) as [<- | Hne].
    + rewrite shift_acts_below by lia. apply tget_tset_same.
    + rewrite IH by lia. rewrite tget_tset_other by assumption. reflexivity.
Qed.
