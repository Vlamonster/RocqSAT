From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT Require Import Clause.
From RocqSAT Require Import CNF.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Search.

(* A key for each literal: 2p for Pos p and 2p + 1 for Neg p. *)
Definition lit_key (l: Lit): nat :=
match l with
| Pos p => 2 * p
| Neg p => S (2 * p)
end.

Lemma lit_key_inj: forall (l l': Lit), lit_key l = lit_key l' -> l = l'.
Proof. intros [p|p] [p'|p'] Heq; simpl in Heq; f_equal; lia. Qed.

(* The clauses of the formula by index, each with its list of literals; the two watched literals of each
   clause; and for each literal (by lit_key) the clauses that watch it. All three are tables, so their
   lookups take constant time. *)
Definition ClauseMap: Type := Table (option (Clause * list Lit)).
Definition Watches: Type := Table (option (Lit * Lit)).
Definition WatchLists: Type := Table (list nat).

Definition watching (wl: WatchLists) (l: Lit): list nat := tget wl (lit_key l).

(* Clause i starts or stops watching l. *)
Definition watch (wl: WatchLists) (l: Lit) (i: nat): WatchLists :=
tset wl (lit_key l) (i :: watching wl l).

Lemma watching_add: forall (wl: WatchLists) (l l': Lit) (ns: list nat),
  watching (tset wl (lit_key l) ns) l' = if Lit.eq_dec l l' then ns else watching wl l'.
Proof.
  intros wl l l' ns. unfold watching. destruct (Lit.eq_dec l l') as [<-|Hneq].
  - apply tget_tset_same.
  - apply tget_tset_other. intros Heq. apply Hneq. now apply lit_key_inj.
Qed.

Lemma watching_watch: forall (wl: WatchLists) (l l': Lit) (i j: nat),
  In j (watching (watch wl l i) l') <-> (l = l' /\ j = i) \/ In j (watching wl l').
Proof.
  intros wl l l' i j. unfold watch. rewrite watching_add. destruct (Lit.eq_dec l l') as [<-|Hneq].
  - split.
    + intros [<-|Hin].
      * left. now split.
      * now right.
    + intros [[_ ->]|Hin].
      * now left.
      * now right.
  - split.
    + intros Hin. now right.
    + intros [[Heq _]|Hin].
      * contradiction.
      * assumption.
Qed.

(* Clause i is still to visit as a watcher of the false literal x: x has a pending item that contains i. *)
Definition Pending (todo: list (Lit * list nat)) (i: nat) (x: Lit): Prop :=
  exists (ws: list nat), In (x, ws) todo /\ In i ws.

Lemma pending_cons: forall (todo: list (Lit * list nat)) (p x: Lit) (ws: list nat) (i: nat),
  Pending ((p, ws) :: todo) i x <-> (x = p /\ In i ws) \/ Pending todo i x.
Proof.
  intros todo p x ws i. split.
  - intros [ws' [[Heq|Hin] Hi]].
    + injection Heq as -> ->. left. now split.
    + right. now exists ws'.
  - intros [[-> Hi]|[ws' [Hin Hi]]].
    + exists ws. split.
      * now left.
      * assumption.
    + exists ws'. split.
      * now right.
      * assumption.
Qed.

(* Every clause comes with its literals and has two watched literals, which are literals of the clause unless
   it is empty; for each of them, the clause is in its watch list or pending in its item. *)
Definition WatchStruct (cm: ClauseMap) (w: Watches) (wl: WatchLists) (todo: list (Lit * list nat)): Prop :=
  forall (i: nat) (c: Clause) (ls: list Lit), tget cm i = Some (c, ls) ->
  ls = Clause.elements c /\
  exists (w1 w2: Lit), tget w i = Some (w1, w2) /\
  (In i (watching wl w1) \/ Pending todo i w1) /\ (In i (watching wl w2) \/ Pending todo i w2) /\
  (ls = [] \/ (w1 ∈ c /\ w2 ∈ c)).

(* The watched literals of c are fine: one of them is true, or both are distinct, unassigned literals of c. *)
Definition WatchOK (v: Values) (c: Clause) (w1 w2: Lit): Prop :=
  (w1 ∈ c /\ lookup v w1 = Some true) \/
  (w2 ∈ c /\ lookup v w2 = Some true) \/
  (w1 ∈ c /\ w2 ∈ c /\ w1 <> w2 /\ lookup v w1 = None /\ lookup v w2 = None).

(* Every clause has fine watched literals or is pending under one of them. *)
Definition Covered (v: Values) (cm: ClauseMap) (w: Watches) (todo: list (Lit * list nat)): Prop :=
  forall (i: nat) (c: Clause) (ls: list Lit), tget cm i = Some (c, ls) ->
  exists (w1 w2: Lit), tget w i = Some (w1, w2) /\ (WatchOK v c w1 w2 \/ Pending todo i w1 \/ Pending todo i w2).

Lemma watch_ok_settled: forall (v: Values) (c: Clause) (w1 w2: Lit), WatchOK v c w1 w2 -> Settled v c.
Proof.
  intros v c w1 w2 [[Hw1 Hl1]|[[Hw2 Hl2]|(Hw1 & Hw2 & Hneq & Hl1 & Hl2)]].
  - left. now exists w1.
  - left. now exists w2.
  - right. now exists w1, w2.
Qed.

(* Assigning an unassigned literal l keeps the watched literals fine, unless one of them is ¬l. *)
Lemma watch_ok_cons: forall (v: Values) (c: Clause) (w1 w2 l: Lit),
  WatchOK v c w1 w2 -> lookup v l = None -> w1 <> ¬l -> w2 <> ¬l ->
  WatchOK (set_value v l) c w1 w2.
Proof.
  intros v c w1 w2 l [[Hw1 Hl1]|[[Hw2 Hl2]|(Hw1 & Hw2 & Hneq & Hl1 & Hl2)]] Hl Hneg1 Hneg2.
  - left. split.
    + assumption.
    + rewrite lookup_add_other.
      * assumption.
      * intros ->. congruence.
      * assumption.
  - right. left. split.
    + assumption.
    + rewrite lookup_add_other.
      * assumption.
      * intros ->. congruence.
      * assumption.
  - destruct (Lit.eq_dec w1 l) as [->|Hneq1].
    + left. split.
      * assumption.
      * apply lookup_add_self.
    + destruct (Lit.eq_dec w2 l) as [->|Hneq2].
      * right. left. split.
        -- assumption.
        -- apply lookup_add_self.
      * right. right. rewrite !lookup_add_other.
        -- now repeat split.
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
Qed.

(* Whether l is not false. *)
Definition not_false (v: Values) (l: Lit): bool :=
match lookup v l with
| Some false => false
| _          => true
end.

(* A watched literal of a clause with literals ls other than other: w if it is not false, otherwise the first
   literal of ls that is not false. *)
Definition replace_watch (v: Values) (ls: list Lit) (w other: Lit): option Lit :=
if not_false v w && negb (w =? other) then Some w
else find (fun (r: Lit) => not_false v r && negb (r =? other)) ls.

Lemma replace_watch_spec: forall (v: Values) (c: Clause) (ls: list Lit) (w other r: Lit),
  (forall (l: Lit), In l ls <-> l ∈ c) ->
  w ∈ c ->
  replace_watch v ls w other = Some r -> r ∈ c /\ lookup v r <> Some false /\ r <> other.
Proof.
  intros v c ls w other r Hls Hw. unfold replace_watch.
  destruct (not_false v w && negb (w =? other)) eqn:Hkeep.
  - intros Heq. injection Heq as <-. apply andb_prop in Hkeep as [Hnot_false Hneq]. split.
    + assumption.
    + split.
      * unfold not_false in Hnot_false. destruct (lookup v w) as [[|]|]; easy.
      * apply negb_true_iff in Hneq. now apply Lit.eqb_neq in Hneq.
  - intros Hfind. apply find_some in Hfind as [Hin Hr]. apply andb_prop in Hr as [Hnot_false Hneq]. split.
    + now apply Hls.
    + split.
      * unfold not_false in Hnot_false. destruct (lookup v r) as [[|]|]; easy.
      * apply negb_true_iff in Hneq. now apply Lit.eqb_neq in Hneq.
Qed.

Lemma replace_watch_exists: forall (v: Values) (c: Clause) (ls: list Lit) (w other r: Lit),
  (forall (l: Lit), In l ls <-> l ∈ c) ->
  r ∈ c -> lookup v r <> Some false -> r <> other -> exists (r': Lit), replace_watch v ls w other = Some r'.
Proof.
  intros v c ls w other r Hls Hr_in Hr Hneq. unfold replace_watch.
  destruct (not_false v w && negb (w =? other)).
  - now exists w.
  - destruct (find (fun (r: Lit) => not_false v r && negb (r =? other)) ls) as [r'|] eqn:Hfind.
    + now exists r'.
    + exfalso. apply find_none with (x := r) in Hfind.
      * apply andb_false_iff in Hfind as [Hfalse|Heq].
        -- unfold not_false in Hfalse. destruct (lookup v r) as [[|]|]; easy.
        -- apply negb_false_iff in Heq. now apply Lit.eqb_eq in Heq.
      * now apply Hls.
Qed.

(* New watched literals for a clause with literals ls: keep them if one is true, otherwise move each false one
   to another literal that is not false. None if that is impossible, i.e. if the clause is false or unit. *)
Definition repair (v: Values) (ls: list Lit) (w1 w2: Lit): option (Lit * Lit) :=
match ls with
| [] => None
| _  =>
  if lookup_true v w1 || lookup_true v w2 then Some (w1, w2) else
  match replace_watch v ls w1 w2 with
  | None   => None
  | Some a =>
    match replace_watch v ls w2 a with
    | Some b => Some (a, b)
    | None   => if lookup_true v a then Some (a, w2) else None
    end
  end
end.

Lemma repair_spec: forall (v: Values) (c: Clause) (ls: list Lit) (w1 w2 a b: Lit),
  (forall (l: Lit), In l ls <-> l ∈ c) ->
  ls = [] \/ (w1 ∈ c /\ w2 ∈ c) ->
  repair v ls w1 w2 = Some (a, b) -> WatchOK v c a b /\ a ∈ c /\ b ∈ c.
Proof.
  intros v c ls w1 w2 a b Hls Hmembers. unfold repair. destruct ls as [|l0 ls'].
  - discriminate.
  - destruct Hmembers as [Hnil|[Hw1 Hw2]].
    + discriminate.
    + destruct (lookup_true v w1 || lookup_true v w2) eqn:Htrue.
      * intros Heq. injection Heq as <- <-. split.
        -- apply orb_true_iff in Htrue as [Htrue|Htrue].
          ++ left. split.
            ** assumption.
            ** unfold lookup_true in Htrue. destruct (lookup v w1) as [[|]|]; easy.
          ++ right. left. split.
            ** assumption.
            ** unfold lookup_true in Htrue. destruct (lookup v w2) as [[|]|]; easy.
        -- now split.
      * destruct (replace_watch v (l0 :: ls') w1 w2) as [a'|] eqn:Ha.
        -- apply (replace_watch_spec v c) in Ha as (Ha_in & Ha & _).
          ++ destruct (replace_watch v (l0 :: ls') w2 a') as [b'|] eqn:Hb.
            ** intros Heq. injection Heq as <- <-. apply (replace_watch_spec v c) in Hb as (Hb_in & Hb & Hneq).
              --- split.
                +++ destruct (lookup v a') as [[|]|] eqn:Ha'.
                  *** left. now split.
                  *** contradiction.
                  *** destruct (lookup v b') as [[|]|] eqn:Hb'.
                    ---- right. left. now split.
                    ---- contradiction.
                    ---- right. right. split.
                      ++++ assumption.
                      ++++ split.
                        **** assumption.
                        **** split.
                          ----- intros ->. now apply Hneq.
                          ----- now split.
                +++ now split.
              --- assumption.
              --- assumption.
            ** destruct (lookup_true v a') eqn:Ha_true.
              --- intros Heq. injection Heq as <- <-. split.
                +++ left. split.
                  *** assumption.
                  *** unfold lookup_true in Ha_true. destruct (lookup v a') as [[|]|]; easy.
                +++ now split.
              --- discriminate.
          ++ assumption.
          ++ assumption.
        -- discriminate.
Qed.

(* The watched literals of a settled clause can always be repaired. *)
Lemma repair_settled: forall (v: Values) (c: Clause) (ls: list Lit) (w1 w2: Lit),
  (forall (l: Lit), In l ls <-> l ∈ c) ->
  ls = [] \/ (w1 ∈ c /\ w2 ∈ c) ->
  Settled v c -> exists (p: Lit * Lit), repair v ls w1 w2 = Some p.
Proof.
  intros v c ls w1 w2 Hls Hmembers Hsettled. unfold repair. destruct ls as [|l0 ls'].
  - exfalso. destruct Hsettled as [[t [Ht_in _]]|[u1 [_ [Hu1_in _]]]].
    + now apply Hls in Ht_in.
    + now apply Hls in Hu1_in.
  - destruct Hmembers as [Hnil|[Hw1 Hw2]].
    + discriminate.
    + destruct (lookup_true v w1 || lookup_true v w2) eqn:Htrue.
      * now exists (w1, w2).
      * apply orb_false_iff in Htrue as [_ Hw2_true].
        destruct Hsettled as [[t [Ht_in Ht]]|[u1 [u2 [Hu1_in [Hu2_in [Hneq [Hu1 Hu2]]]]]]].
        (* A true literal t *)
        -- assert (Ht_w2: t <> w2).
          ++ intros ->. unfold lookup_true in Hw2_true. now rewrite Ht in Hw2_true.
          ++ destruct (replace_watch v (l0 :: ls') w1 w2) as [a|] eqn:Ha.
            ** destruct (replace_watch v (l0 :: ls') w2 a) as [b|] eqn:Hb.
              --- now exists (a, b).
              --- destruct (lookup_true v a) eqn:Ha_true.
                +++ now exists (a, w2).
                +++ destruct (replace_watch_exists v c (l0 :: ls') w2 a t) as [b Hb'].
                  *** assumption.
                  *** assumption.
                  *** congruence.
                  *** intros ->. unfold lookup_true in Ha_true. now rewrite Ht in Ha_true.
                  *** congruence.
            ** destruct (replace_watch_exists v c (l0 :: ls') w1 w2 t) as [a Ha'].
              --- assumption.
              --- assumption.
              --- congruence.
              --- assumption.
              --- congruence.
        (* Two unassigned literals u1 and u2 *)
        -- destruct (replace_watch v (l0 :: ls') w1 w2) as [a|] eqn:Ha.
          ++ destruct (replace_watch v (l0 :: ls') w2 a) as [b|] eqn:Hb.
            ** now exists (a, b).
            ** exfalso. destruct (Lit.eq_dec u1 a) as [->|Hu1_a].
              --- destruct (replace_watch_exists v c (l0 :: ls') w2 a u2) as [b Hb'].
                +++ assumption.
                +++ assumption.
                +++ congruence.
                +++ intros ->. now apply Hneq.
                +++ congruence.
              --- destruct (replace_watch_exists v c (l0 :: ls') w2 a u1) as [b Hb'].
                +++ assumption.
                +++ assumption.
                +++ congruence.
                +++ assumption.
                +++ congruence.
          ++ exfalso. destruct (Lit.eq_dec u1 w2) as [->|Hu1_w2].
            ** destruct (replace_watch_exists v c (l0 :: ls') w1 w2 u2) as [a Ha'].
              --- assumption.
              --- assumption.
              --- congruence.
              --- intros ->. now apply Hneq.
              --- congruence.
            ** destruct (replace_watch_exists v c (l0 :: ls') w1 w2 u1) as [a Ha'].
              --- assumption.
              --- assumption.
              --- congruence.
              --- assumption.
              --- congruence.
Qed.

(* The watch lists while visiting the watchers of p: the clauses that keep watching p are collected in keep, and
   added to the watch list of p at the end. *)
Definition with_kept (wl: WatchLists) (p: Lit) (keep: list nat): WatchLists :=
tset wl (lit_key p) (keep ++ watching wl p).

Lemma watching_with_kept: forall (wl: WatchLists) (p y: Lit) (keep: list nat) (j: nat),
  In j (watching (with_kept wl p keep) y) <-> (y = p /\ In j keep) \/ In j (watching wl y).
Proof.
  intros wl p y keep j. unfold with_kept. rewrite watching_add. destruct (Lit.eq_dec p y) as [<-|Hneq].
  - rewrite in_app_iff. split.
    + intros [Hk|Hw].
      * left. now split.
      * now right.
    + intros [[_ Hk]|Hw].
      * now left.
      * now right.
  - split.
    + intros Hw. now right.
    + intros [[-> _]|Hw].
      * contradiction.
      * assumption.
Qed.

(* Collecting more kept clauses and adding to the watch lists keeps every clause in the lists it was in. *)
Lemma with_kept_mono: forall (wl wl': WatchLists) (p y: Lit) (keep keep': list nat) (j: nat),
  (forall (z: Lit), In j (watching wl z) -> In j (watching wl' z)) ->
  (In j keep -> In j keep') ->
  In j (watching (with_kept wl p keep) y) -> In j (watching (with_kept wl' p keep') y).
Proof.
  intros wl wl' p y keep keep' j Hwl Hkeep Hin. apply watching_with_kept. apply watching_with_kept in Hin as [[-> Hk]|Hw].
  - left. split.
    + reflexivity.
    + now apply Hkeep.
  - right. now apply Hwl.
Qed.

(* Clause i, which watched w1 and w2, now also watches x: add it to the watch list of x, unless x was already
   one of its watches or is p, whose watchers are collected separately. *)
Definition add_watch (wl: WatchLists) (i: nat) (p w1 w2 x: Lit): WatchLists :=
if (x =? p) || (x =? w1) || (x =? w2) then wl else watch wl x i.

Lemma add_watch_keep: forall (wl: WatchLists) (i j: nat) (p w1 w2 x y: Lit),
  In j (watching wl y) -> In j (watching (add_watch wl i p w1 w2 x) y).
Proof.
  intros wl i j p w1 w2 x y Hin. unfold add_watch. destruct ((x =? p) || (x =? w1) || (x =? w2)).
  - assumption.
  - apply watching_watch. now right.
Qed.

Lemma add_watch_new: forall (wl: WatchLists) (i: nat) (p w1 w2 x: Lit),
  x <> p -> x <> w1 -> x <> w2 -> In i (watching (add_watch wl i p w1 w2 x) x).
Proof.
  intros wl i p w1 w2 x Hp Hw1 Hw2. unfold add_watch. apply Lit.eqb_neq in Hp, Hw1, Hw2.
  rewrite Hp, Hw1, Hw2. simpl. apply watching_watch. now left.
Qed.

(* Visit the clauses ws watching the false literal p: drop those that no longer watch p, repair the watches of
   the others, collecting those that keep watching p, until one cannot be repaired. Returns the clauses still to
   visit, starting with that one. *)
Fixpoint visit (v: Values) (cm: ClauseMap) (p: Lit) (w: Watches) (wl: WatchLists) (keep ws: list nat):
  Watches * WatchLists * list nat * list nat :=
match ws with
| []        => (w, wl, keep, [])
| i :: rest =>
  match tget cm i, tget w i with
  | Some (_, ls), Some (w1, w2) =>
    if (w1 =? p) || (w2 =? p) then
      match repair v ls w1 w2 with
      | Some (a, b) =>
        if (a =? w1) && (b =? w2) then visit v cm p w wl (i :: keep) rest
        else visit v cm p (tset w i (Some (a, b))) (add_watch (add_watch wl i p w1 w2 a) i p w1 w2 b)
          (if (a =? p) || (b =? p) then i :: keep else keep) rest
      | None        => (w, wl, keep, ws)
      end
    else visit v cm p w wl keep rest
  | _, _ => visit v cm p w wl keep rest
  end
end.

(* A stuck clause i: its watches cannot be repaired. *)
Definition Stuck (v: Values) (cm: ClauseMap) (w: Watches) (i: nat): Prop :=
  exists (c: Clause) (ls: list Lit) (w1 w2: Lit), tget cm i = Some (c, ls) /\ tget w i = Some (w1, w2) /\
  repair v ls w1 w2 = None.

Lemma visit_spec: forall (v: Values) (cm: ClauseMap) (p: Lit) (todo: list (Lit * list nat)) (ws keep: list nat)
  (w w': Watches) (wl wl': WatchLists) (keep' ws': list nat),
  WatchStruct cm w (with_kept wl p keep) ((p, ws) :: todo) ->
  Covered v cm w ((p, ws) :: todo) ->
  visit v cm p w wl keep ws = (w', wl', keep', ws') ->
  WatchStruct cm w' (with_kept wl' p keep') ((p, ws') :: todo) /\ Covered v cm w' ((p, ws') :: todo) /\
  (ws' = [] \/ exists (i: nat) (rest: list nat), ws' = i :: rest /\ Stuck v cm w' i).
Proof.
  intros v cm p todo ws. induction ws as [|i rest IH]; intros keep w w' wl wl' keep' ws' Hstruct Hcover Hvisit;
    simpl in Hvisit.
  - injection Hvisit as <- <- <- <-. split.
    + assumption.
    + split.
      * assumption.
      * now left.
  - (* Dropping i from the pending item of p keeps a clause pending under x, unless it is i and x is p *)
    assert (Hdrop: forall (j: nat) (x: Lit), j <> i \/ x <> p ->
      Pending ((p, i :: rest) :: todo) j x -> Pending ((p, rest) :: todo) j x).
    + intros j x Hji Hpend. apply pending_cons. apply pending_cons in Hpend as [[-> [<-|Hj]]|Hpend].
      * destruct Hji as [Hji|Hxp].
        -- contradiction.
        -- contradiction.
      * left. now split.
      * now right.
    + (* A clause other than i, or i under a watch other than p, stays where it was *)
      assert (Hmove: forall (wl2: WatchLists) (keep2: list nat) (j: nat) (x: Lit),
        (forall (z: Lit), In j (watching wl z) -> In j (watching wl2 z)) -> (In j keep -> In j keep2) ->
        j <> i \/ x <> p ->
        In j (watching (with_kept wl p keep) x) \/ Pending ((p, i :: rest) :: todo) j x ->
        In j (watching (with_kept wl2 p keep2) x) \/ Pending ((p, rest) :: todo) j x).
      * intros wl2 keep2 j x Hwl Hkeep Hji [Hin|Hpend].
        -- left. now apply (with_kept_mono wl wl2 p x keep keep2 j).
        -- right. now apply Hdrop.
      * destruct (tget cm i) as [[c ls]|] eqn:Hc.
        -- destruct (Hstruct i c ls Hc) as [Hls (w1 & w2 & Hw & Hin1 & Hin2 & Hmembers)]. rewrite Hw in Hvisit.
           assert (Hls_iff: forall (l: Lit), In l ls <-> l ∈ c).
          ++ intros l. subst ls. apply clause_elements_iff.
          ++ destruct ((w1 =? p) || (w2 =? p)) eqn:Hwatch.
            ** destruct (repair v ls w1 w2) as [[a b]|] eqn:Hrepair.
              --- apply (repair_spec v c ls w1 w2 a b Hls_iff Hmembers) in Hrepair as (Hok & Ha & Hb).
                  destruct ((a =? w1) && (b =? w2)) eqn:Hsame.
                (* The watches of i stay the same, and so it keeps watching p *)
                +++ apply andb_prop in Hsame as [Ha1 Hb2]. apply Lit.eqb_eq in Ha1, Hb2. subst a b.
                    apply (IH (i :: keep) w w' wl wl' keep' ws').
                  *** intros j c' ls' Hj. destruct (Hstruct j c' ls' Hj) as [Hls' (w1' & w2' & Hw' & Hj1 & Hj2 & Hm')].
                      split.
                    ---- assumption.
                    ---- exists w1', w2'. split.
                      ++++ assumption.
                      ++++ destruct (Nat.eq_dec j i) as [->|Hneq].
                        **** rewrite Hw in Hw'. injection Hw' as <- <-. split.
                          ----- destruct (Lit.eq_dec w1 p) as [->|Hw1p].
                            +++++ left. apply watching_with_kept. left. split.
                              ***** reflexivity.
                              ***** now left.
                            +++++ apply (Hmove wl (i :: keep) i w1).
                              ***** easy.
                              ***** intros Hk. now right.
                              ***** now right.
                              ***** assumption.
                          ----- split.
                            +++++ destruct (Lit.eq_dec w2 p) as [->|Hw2p].
                              ***** left. apply watching_with_kept. left. split.
                                ------ reflexivity.
                                ------ now left.
                              ***** apply (Hmove wl (i :: keep) i w2).
                                ------ easy.
                                ------ intros Hk. now right.
                                ------ now right.
                                ------ assumption.
                            +++++ assumption.
                        **** split.
                          ----- apply (Hmove wl (i :: keep) j w1').
                            +++++ easy.
                            +++++ intros Hk. now right.
                            +++++ now left.
                            +++++ assumption.
                          ----- split.
                            +++++ apply (Hmove wl (i :: keep) j w2').
                              ***** easy.
                              ***** intros Hk. now right.
                              ***** now left.
                              ***** assumption.
                            +++++ assumption.
                  *** intros j c' ls' Hj. destruct (Hcover j c' ls' Hj) as (w1' & w2' & Hw' & Hcase).
                      exists w1', w2'. split.
                    ---- assumption.
                    ---- destruct (Nat.eq_dec j i) as [->|Hneq].
                      ++++ rewrite Hc in Hj. injection Hj as <- <-. rewrite Hw in Hw'. injection Hw' as <- <-.
                           now left.
                      ++++ destruct Hcase as [Hok'|[Hpend1|Hpend2]].
                        **** now left.
                        **** right. left. apply Hdrop.
                          ----- now left.
                          ----- assumption.
                        **** right. right. apply Hdrop.
                          ----- now left.
                          ----- assumption.
                  *** assumption.
                (* i moves its watches to a and b *)
                +++ set (wl2 := add_watch (add_watch wl i p w1 w2 a) i p w1 w2 b).
                    set (keep2 := if (a =? p) || (b =? p) then i :: keep else keep).
                    assert (Hwl2: forall (j: nat) (z: Lit), In j (watching wl z) -> In j (watching wl2 z)).
                  *** intros j z Hin. now apply add_watch_keep, add_watch_keep.
                  *** assert (Hkeep2: forall (j: nat), In j keep -> In j keep2).
                    ---- intros j Hk. unfold keep2. destruct ((a =? p) || (b =? p)).
                      ++++ now right.
                      ++++ assumption.
                    ---- (* Under each new watch x, i is in the watch list of x or among the kept clauses *)
                         assert (Hnew: forall (x: Lit), x = a \/ x = b ->
                           In i (watching (with_kept wl2 p keep2) x) \/ Pending ((p, rest) :: todo) i x).
                      ++++ intros x Hx. destruct (Lit.eq_dec x p) as [->|Hxp].
                        **** left. apply watching_with_kept. left. split.
                          ----- reflexivity.
                          ----- unfold keep2. destruct Hx as [<- | <-].
                            +++++ rewrite Lit.eqb_refl. simpl. now left.
                            +++++ rewrite Lit.eqb_refl, orb_true_r. now left.
                        **** destruct (Lit.eq_dec x w1) as [->|Hxw1].
                          ----- apply (Hmove wl2 keep2 i w1).
                            +++++ intros z. apply Hwl2.
                            +++++ apply Hkeep2.
                            +++++ now right.
                            +++++ assumption.
                          ----- destruct (Lit.eq_dec x w2) as [->|Hxw2].
                            +++++ apply (Hmove wl2 keep2 i w2).
                              ***** intros z. apply Hwl2.
                              ***** apply Hkeep2.
                              ***** now right.
                              ***** assumption.
                            +++++ left. apply watching_with_kept. right. unfold wl2. destruct Hx as [-> | ->].
                              ***** apply add_watch_keep. now apply add_watch_new.
                              ***** now apply add_watch_new.
                      ++++ apply (IH keep2 (tset w i (Some (a, b))) w' wl2 wl' keep' ws').
                        **** intros j c' ls' Hj. destruct (Hstruct j c' ls' Hj) as [Hls' (w1' & w2' & Hw' & Hj1 & Hj2 & Hm')].
                             split.
                          ----- assumption.
                          ----- rewrite tget_tset. destruct (Nat.eq_dec i j) as [<-|Hneq].
                            +++++ rewrite Hc in Hj. injection Hj as <- <-. exists a, b. split.
                              ***** reflexivity.
                              ***** split.
                                ------ apply Hnew. now left.
                                ------ split.
                                  ++++++ apply Hnew. now right.
                                  ++++++ right. now split.
                            +++++ exists w1', w2'. split.
                              ***** assumption.
                              ***** split.
                                ------ apply (Hmove wl2 keep2 j w1').
                                  ++++++ intros z. apply Hwl2.
                                  ++++++ apply Hkeep2.
                                  ++++++ left. intros ->. now apply Hneq.
                                  ++++++ assumption.
                                ------ split.
                                  ++++++ apply (Hmove wl2 keep2 j w2').
                                    ******* intros z. apply Hwl2.
                                    ******* apply Hkeep2.
                                    ******* left. intros ->. now apply Hneq.
                                    ******* assumption.
                                  ++++++ assumption.
                        **** intros j c' ls' Hj. rewrite tget_tset. destruct (Nat.eq_dec i j) as [<-|Hneq].
                          ----- rewrite Hc in Hj. injection Hj as <- <-. exists a, b. split.
                            +++++ reflexivity.
                            +++++ now left.
                          ----- destruct (Hcover j c' ls' Hj) as (w1' & w2' & Hw' & [Hok'|[Hpend1|Hpend2]]).
                            +++++ exists w1', w2'. split.
                              ***** assumption.
                              ***** now left.
                            +++++ exists w1', w2'. split.
                              ***** assumption.
                              ***** right. left. apply Hdrop.
                                ------ left. intros ->. now apply Hneq.
                                ------ assumption.
                            +++++ exists w1', w2'. split.
                              ***** assumption.
                              ***** right. right. apply Hdrop.
                                ------ left. intros ->. now apply Hneq.
                                ------ assumption.
                        **** assumption.
              (* i is stuck *)
              --- injection Hvisit as <- <- <- <-. split.
                +++ assumption.
                +++ split.
                  *** assumption.
                  *** right. exists i, rest. split.
                    ---- reflexivity.
                    ---- now exists c, ls, w1, w2.
            (* i no longer watches p: drop it *)
            ** apply orb_false_iff in Hwatch as [Hw1p Hw2p]. apply Lit.eqb_neq in Hw1p, Hw2p.
               apply (IH keep w w' wl wl' keep' ws').
              --- intros j c' ls' Hj. destruct (Hstruct j c' ls' Hj) as [Hls' (w1' & w2' & Hw' & Hj1 & Hj2 & Hm')].
                  split.
                +++ assumption.
                +++ exists w1', w2'. split.
                  *** assumption.
                  *** assert (Hji: forall (x: Lit), x = w1' \/ x = w2' -> j <> i \/ x <> p).
                    ---- intros x Hx. destruct (Nat.eq_dec j i) as [->|Hneq].
                      ++++ rewrite Hw in Hw'. injection Hw' as <- <-. right. destruct Hx as [-> | ->].
                        **** assumption.
                        **** assumption.
                      ++++ now left.
                    ---- split.
                      ++++ apply (Hmove wl keep j w1').
                        **** easy.
                        **** easy.
                        **** apply Hji. now left.
                        **** assumption.
                      ++++ split.
                        **** apply (Hmove wl keep j w2').
                          ----- easy.
                          ----- easy.
                          ----- apply Hji. now right.
                          ----- assumption.
                        **** assumption.
              --- intros j c' ls' Hj. destruct (Hcover j c' ls' Hj) as (w1' & w2' & Hw' & [Hok|[Hpend1|Hpend2]]).
                +++ exists w1', w2'. split.
                  *** assumption.
                  *** now left.
                +++ exists w1', w2'. split.
                  *** assumption.
                  *** right. left. apply Hdrop.
                    ---- destruct (Nat.eq_dec j i) as [->|Hneq].
                      ++++ rewrite Hw in Hw'. injection Hw' as <- <-. now right.
                      ++++ now left.
                    ---- assumption.
                +++ exists w1', w2'. split.
                  *** assumption.
                  *** right. right. apply Hdrop.
                    ---- destruct (Nat.eq_dec j i) as [->|Hneq].
                      ++++ rewrite Hw in Hw'. injection Hw' as <- <-. now right.
                      ++++ now left.
                    ---- assumption.
              --- assumption.
        (* i is not a clause: drop it *)
        -- apply (IH keep w w' wl wl' keep' ws').
          ++ intros j c' ls' Hj. destruct (Hstruct j c' ls' Hj) as [Hls' (w1' & w2' & Hw' & Hj1 & Hj2 & Hm')].
             assert (Hneq: j <> i).
            ** intros ->. congruence.
            ** split.
              --- assumption.
              --- exists w1', w2'. split.
                +++ assumption.
                +++ split.
                  *** apply (Hmove wl keep j w1').
                    ---- easy.
                    ---- easy.
                    ---- now left.
                    ---- assumption.
                  *** split.
                    ---- apply (Hmove wl keep j w2').
                      ++++ easy.
                      ++++ easy.
                      ++++ now left.
                      ++++ assumption.
                    ---- assumption.
          ++ intros j c' ls' Hj. assert (Hneq: j <> i).
            ** intros ->. congruence.
            ** destruct (Hcover j c' ls' Hj) as (w1' & w2' & Hw' & [Hok|[Hpend1|Hpend2]]).
              --- exists w1', w2'. split.
                +++ assumption.
                +++ now left.
              --- exists w1', w2'. split.
                +++ assumption.
                +++ right. left. apply Hdrop.
                  *** now left.
                  *** assumption.
              --- exists w1', w2'. split.
                +++ assumption.
                +++ right. right. apply Hdrop.
                  *** now left.
                  *** assumption.
          ++ assumption.
Qed.

(* The first two literals of a clause with literals ls, to watch initially. *)
Definition first_watches (ls: list Lit): Lit * Lit :=
match ls with
| a :: b :: _ => (a, b)
| [a]         => (a, a)
| []          => (Pos 0, Pos 0)
end.

Lemma first_watches_in: forall (ls: list Lit),
  ls = [] \/ (In (fst (first_watches ls)) ls /\ In (snd (first_watches ls)) ls).
Proof.
  intros [|a [|b ls]]; simpl.
  - now left.
  - right. split.
    + now left.
    + now left.
  - right. split.
    + now left.
    + right. now left.
Qed.


(* Visit the pending items in turn, until a clause is stuck: it is then the first clause of the first item. *)
Fixpoint process (v: Values) (cm: ClauseMap) (w: Watches) (wl: WatchLists) (todo: list (Lit * list nat)):
  Watches * WatchLists * list (Lit * list nat) :=
match todo with
| []             => (w, wl, [])
| (p, ws) :: rest =>
  match visit v cm p w wl [] ws with
  | (w', wl', keep, [])  => process v cm w' (with_kept wl' p keep) rest
  | (w', wl', keep, ws') => (w', with_kept wl' p keep, (p, ws') :: rest)
  end
end.

Lemma pending_empty_item: forall (todo: list (Lit * list nat)) (p x: Lit) (i: nat),
  Pending ((p, []) :: todo) i x -> Pending todo i x.
Proof. intros todo p x i Hpend. apply pending_cons in Hpend as [[_ []]|Hpend]. assumption. Qed.

Lemma process_spec: forall (v: Values) (cm: ClauseMap) (todo: list (Lit * list nat)) (w w': Watches)
  (wl wl': WatchLists) (todo': list (Lit * list nat)),
  WatchStruct cm w wl todo ->
  Covered v cm w todo ->
  process v cm w wl todo = (w', wl', todo') ->
  WatchStruct cm w' wl' todo' /\ Covered v cm w' todo' /\
  (todo' = [] \/ exists (p: Lit) (i: nat) (ws: list nat) (rest: list (Lit * list nat)),
    todo' = (p, i :: ws) :: rest /\ Stuck v cm w' i).
Proof.
  intros v cm todo. induction todo as [|[p ws] rest IH]; intros w w' wl wl' todo' Hstruct Hcover Hprocess;
    simpl in Hprocess.
  - injection Hprocess as <- <- <-. split.
    + assumption.
    + split.
      * assumption.
      * now left.
  - destruct (visit v cm p w wl [] ws) as [[[w1 wl1] keep1] ws1] eqn:Hvisit.
    assert (Hstruct0: WatchStruct cm w (with_kept wl p []) ((p, ws) :: rest)).
    + intros j c ls Hj. destruct (Hstruct j c ls Hj) as [Hls (w1' & w2' & Hw & Hj1 & Hj2 & Hmembers)]. split.
      * assumption.
      * exists w1', w2'. split.
        -- assumption.
        -- split.
          ++ destruct Hj1 as [Hj1|Hpend1].
            ** left. apply watching_with_kept. now right.
            ** now right.
          ++ split.
            ** destruct Hj2 as [Hj2|Hpend2].
              --- left. apply watching_with_kept. now right.
              --- now right.
            ** assumption.
    + destruct (visit_spec v cm p rest ws [] w w1 wl wl1 keep1 ws1 Hstruct0 Hcover Hvisit)
        as (Hstruct1 & Hcover1 & Hstuck).
      destruct ws1 as [|i ws1].
      * apply (IH w1 w' (with_kept wl1 p keep1) wl' todo').
        -- intros j c ls Hj. destruct (Hstruct1 j c ls Hj) as [Hls (w1' & w2' & Hw & Hj1 & Hj2 & Hmembers)]. split.
          ++ assumption.
          ++ exists w1', w2'. split.
            ** assumption.
            ** split.
              --- destruct Hj1 as [Hj1|Hpend1].
                +++ now left.
                +++ right. now apply pending_empty_item in Hpend1.
              --- split.
                +++ destruct Hj2 as [Hj2|Hpend2].
                  *** now left.
                  *** right. now apply pending_empty_item in Hpend2.
                +++ assumption.
        -- intros j c ls Hj. destruct (Hcover1 j c ls Hj) as (w1' & w2' & Hw & [Hok|[Hpend1|Hpend2]]).
          ++ exists w1', w2'. split.
            ** assumption.
            ** now left.
          ++ exists w1', w2'. split.
            ** assumption.
            ** right. left. now apply pending_empty_item in Hpend1.
          ++ exists w1', w2'. split.
            ** assumption.
            ** right. right. now apply pending_empty_item in Hpend2.
        -- assumption.
      * injection Hprocess as <- <- <-. split.
        -- assumption.
        -- split.
          ++ assumption.
          ++ right. destruct Hstuck as [Hnil|(i' & ws' & Heq & Hstuck)].
            ** discriminate.
            ** injection Heq as <- <-. now exists p, i, ws1, rest.
Qed.

(* Index the clauses cs from k on, with their first literals watched, and each pending under its first watch so
   that it is checked once. *)
Fixpoint index_clauses (k: nat) (cs: list Clause) (cm: ClauseMap) (w: Watches) (wl: WatchLists)
  (todo: list (Lit * list nat)): ClauseMap * Watches * WatchLists * list (Lit * list nat) :=
match cs with
| []      => (cm, w, wl, todo)
| c :: cs =>
  let ls := Clause.elements c in
  index_clauses (S k) cs (tset cm k (Some (c, ls))) (tset w k (Some (first_watches ls)))
    (watch (watch wl (fst (first_watches ls)) k) (snd (first_watches ls)) k) ((fst (first_watches ls), [k]) :: todo)
end.

(* Every clause watches two of its literals and is in both their watch lists. *)
Definition IndexOK (cm: ClauseMap) (w: Watches) (wl: WatchLists): Prop :=
  forall (i: nat) (c: Clause) (ls: list Lit), tget cm i = Some (c, ls) ->
  ls = Clause.elements c /\
  exists (w1 w2: Lit), tget w i = Some (w1, w2) /\ In i (watching wl w1) /\ In i (watching wl w2) /\
  (ls = [] \/ (w1 ∈ c /\ w2 ∈ c)).

(* Every clause is pending under its first watch. *)
Definition IndexPending (cm: ClauseMap) (w: Watches) (todo: list (Lit * list nat)): Prop :=
  forall (i: nat) (c: Clause) (ls: list Lit), tget cm i = Some (c, ls) ->
  exists (w1 w2: Lit), tget w i = Some (w1, w2) /\ Pending todo i w1.

Lemma index_clauses_spec: forall (cs: list Clause) (k: nat) (cm cm': ClauseMap) (w w': Watches)
  (wl wl': WatchLists) (todo todo': list (Lit * list nat)),
  (forall (i: nat) (c: Clause) (ls: list Lit), tget cm i = Some (c, ls) -> i < k) ->
  IndexOK cm w wl ->
  IndexPending cm w todo ->
  index_clauses k cs cm w wl todo = (cm', w', wl', todo') ->
  IndexOK cm' w' wl' /\ IndexPending cm' w' todo' /\
  (forall (i: nat) (c: Clause) (ls: list Lit), tget cm' i = Some (c, ls) ->
    tget cm i = Some (c, ls) \/ In c cs) /\
  (forall (c: Clause), In c cs -> exists (i: nat) (ls: list Lit), tget cm' i = Some (c, ls)) /\
  (forall (i: nat) (c: Clause) (ls: list Lit), tget cm i = Some (c, ls) -> tget cm' i = Some (c, ls)).
Proof.
  induction cs as [|c cs IH]; intros k cm cm' w w' wl wl' todo todo' Hfresh Hok Hpending Hindex; simpl in Hindex.
  - injection Hindex as <- <- <- <-. split.
    + assumption.
    + split.
      * assumption.
      * split.
        -- intros i c ls Hi. now left.
        -- split.
          ++ intros c [].
          ++ easy.
  - set (ls := Clause.elements c) in Hindex.
    destruct (IH (S k) (tset cm k (Some (c, ls))) cm' (tset w k (Some (first_watches ls))) w'
      (watch (watch wl (fst (first_watches ls)) k) (snd (first_watches ls)) k) wl'
      ((fst (first_watches ls), [k]) :: todo) todo') as (Hok' & Hpending' & Hsound & Hcomplete & Hkeep).
    + intros i c' ls' Hi. rewrite tget_tset in Hi. destruct (Nat.eq_dec k i) as [<-|Hneq].
      * lia.
      * apply Hfresh in Hi. lia.
    + intros i c' ls' Hi. rewrite tget_tset in Hi. rewrite tget_tset. destruct (Nat.eq_dec k i) as [<-|Hneq].
      * injection Hi as <- <-. split.
        -- reflexivity.
        -- exists (fst (first_watches ls)), (snd (first_watches ls)). split.
          ++ now destruct (first_watches ls).
          ++ split.
            ** apply watching_watch. right. apply watching_watch. now left.
            ** split.
              --- apply watching_watch. now left.
              --- destruct (first_watches_in ls) as [Hnil|[Hin1 Hin2]].
                +++ now left.
                +++ right. split.
                  *** now apply clause_elements_iff.
                  *** now apply clause_elements_iff.
      * destruct (Hok i c' ls' Hi) as [Hls (w1 & w2 & Hw & Hin1 & Hin2 & Hmembers)]. split.
        -- assumption.
        -- exists w1, w2. split.
          ++ assumption.
          ++ split.
            ** apply watching_watch. right. apply watching_watch. now right.
            ** split.
              --- apply watching_watch. right. apply watching_watch. now right.
              --- assumption.
    + intros i c' ls' Hi. rewrite tget_tset in Hi. rewrite tget_tset. destruct (Nat.eq_dec k i) as [<-|Hneq].
      * exists (fst (first_watches ls)), (snd (first_watches ls)). split.
        -- now destruct (first_watches ls).
        -- apply pending_cons. left. split.
          ++ reflexivity.
          ++ now left.
      * destruct (Hpending i c' ls' Hi) as (w1 & w2 & Hw & Hpend). exists w1, w2. split.
        -- assumption.
        -- apply pending_cons. now right.
    + assumption.
    + split.
      * assumption.
      * split.
        -- assumption.
        -- split.
          ++ intros i c' ls' Hi. apply Hsound in Hi as [Hi|Hin].
            ** rewrite tget_tset in Hi. destruct (Nat.eq_dec k i) as [<-|Hneq].
              --- injection Hi as <- <-. right. now left.
              --- now left.
            ** right. now right.
          ++ split.
            ** intros c' [<-|Hin].
              --- exists k, ls. apply Hkeep. rewrite tget_tset. destruct (Nat.eq_dec k k) as [_|Hneq].
                +++ reflexivity.
                +++ contradiction.
              --- now apply Hcomplete.
            ** intros i c' ls' Hi. apply Hkeep. rewrite tget_tset. destruct (Nat.eq_dec k i) as [<-|Hneq].
              --- apply Hfresh in Hi. lia.
              --- assumption.
Qed.

(* A stuck clause is not settled: it is false or unit. *)
Lemma stuck_unsettled: forall (v: Values) (cm: ClauseMap) (w: Watches) (wl: WatchLists) (todo: list (Lit * list nat))
  (i: nat) (c: Clause) (ls: list Lit) (w1 w2: Lit),
  WatchStruct cm w wl todo ->
  tget cm i = Some (c, ls) -> tget w i = Some (w1, w2) -> repair v ls w1 w2 = None -> ~ Settled v c.
Proof.
  intros v cm w wl todo i c ls w1 w2 Hstruct Hc Hw Hrepair Hsettled.
  destruct (Hstruct i c ls Hc) as [Hls (w1' & w2' & Hw' & _ & _ & Hmembers)]. rewrite Hw in Hw'.
  injection Hw' as <- <-. destruct (repair_settled v c ls w1 w2) as [p Hp].
  - intros l. subst ls. apply clause_elements_iff.
  - assumption.
  - assumption.
  - congruence.
Qed.

(* In a clause that is not settled, the first literal that is not false is its unit literal, and if there is
   none, all its literals are false. *)
Lemma unsettled_unit: forall (v: Values) (c: Clause) (ls: list Lit) (u: Lit),
  ~ Settled v c ->
  (forall (l: Lit), In l ls <-> l ∈ c) ->
  find (not_false v) ls = Some u ->
  u ∈ c /\ lookup v u = None /\ forall (l: Lit), l ∈ c -> l <> u -> lookup v l = Some false.
Proof.
  intros v c ls u Hunsettled Hls Hfind. apply find_some in Hfind as [Hu_in Hu]. apply Hls in Hu_in.
  assert (Hu_undef: lookup v u = None).
  - unfold not_false in Hu. destruct (lookup v u) as [[|]|] eqn:Hu'.
    + exfalso. apply Hunsettled. left. now exists u.
    + discriminate.
    + reflexivity.
  - split.
    + assumption.
    + split.
      * assumption.
      * intros l Hl_in Hneq. destruct (lookup v l) as [[|]|] eqn:Hl.
        -- exfalso. apply Hunsettled. left. now exists l.
        -- reflexivity.
        -- exfalso. apply Hunsettled. right. now exists l, u.
Qed.

Lemma unsettled_conflict: forall (v: Values) (c: Clause) (ls: list Lit),
  (forall (l: Lit), In l ls <-> l ∈ c) ->
  find (not_false v) ls = None ->
  forall (l: Lit), l ∈ c -> lookup v l = Some false.
Proof.
  intros v c ls Hls Hfind l Hl_in. apply Hls in Hl_in. apply find_none with (x := l) in Hfind.
  - unfold not_false in Hfind. destruct (lookup v l) as [[|]|]; easy.
  - assumption.
Qed.
