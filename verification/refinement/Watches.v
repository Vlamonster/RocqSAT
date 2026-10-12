From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
Import ListNotations.

From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Lookup.

(* A key for each literal: 2p for Pos p and 2p + 1 for Neg p. *)
Definition lit_key (l: Lit): nat :=
match l with
| Pos p => 2 * p
| Neg p => S (2 * p)
end.

Lemma lit_key_inj: forall (l l': Lit), lit_key l = lit_key l' -> l = l'.
Proof. intros [p|p] [p'|p'] Heq; simpl in Heq; f_equal; lia. Qed.

(* The literals of each clause of the formula by index; the two watched literals of each clause; and for each
   literal (by lit_key) the clauses that watch it. All three are tables, so their lookups take constant time. *)
Definition ClauseMap: Type := Table (option (list Lit)).
Definition Watches: Type := Table (Lit * Lit).
Definition WatchLists: Type := Table (list nat).

Definition watching (wl: WatchLists) (l: Lit): list nat := tget wl (lit_key l).

(* Clause i starts watching l. *)
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

(* Dropping clause i from the pending item of p keeps every other clause pending, and i under other literals. *)
Lemma pending_drop: forall (todo: list (Lit * list nat)) (p x: Lit) (rest: list nat) (i j: nat),
  j <> i \/ x <> p -> Pending ((p, i :: rest) :: todo) j x -> Pending ((p, rest) :: todo) j x.
Proof.
  intros todo p x rest i j Hji Hpend. apply pending_cons. apply pending_cons in Hpend as [[-> [<-|Hj]]|Hpend].
  - destruct Hji as [Hji|Hxp].
    + contradiction.
    + contradiction.
  - left. now split.
  - now right.
Qed.

(* Clause i is watched by x: it is in the watch list of x or pending under x. *)
Definition Watched (wl: WatchLists) (todo: list (Lit * list nat)) (i: nat) (x: Lit): Prop :=
  In i (watching wl x) \/ Pending todo i x.

(* A clause stays watched when the watch lists grow and its pending item is dropped, unless it is i under p. *)
Lemma watched_drop: forall (wl wl': WatchLists) (todo: list (Lit * list nat)) (p x: Lit) (rest: list nat) (i j: nat),
  (forall (z: Lit), In j (watching wl z) -> In j (watching wl' z)) ->
  j <> i \/ x <> p ->
  Watched wl ((p, i :: rest) :: todo) j x -> Watched wl' ((p, rest) :: todo) j x.
Proof.
  intros wl wl' todo p x rest i j Hwl Hji [Hin|Hpend].
  - left. now apply Hwl.
  - right. now apply (pending_drop todo p x rest i j).
Qed.

(* Each clause is watched by its two watched literals, which are literals of the clause, or equal if it is
   empty. *)
Definition WatchStruct (cm: ClauseMap) (w: Watches) (wl: WatchLists) (todo: list (Lit * list nat)): Prop :=
  forall (i: nat) (ls: list Lit) (w1 w2: Lit), tget cm i = Some ls -> tget w i = (w1, w2) ->
  Watched wl todo i w1 /\ Watched wl todo i w2 /\ ((ls = [] /\ w1 = w2) \/ (In w1 ls /\ In w2 ls)).

(* The watched literals of a clause with literals ls are fine: one of them is true, or both are distinct,
   unassigned literals of the clause. *)
Definition WatchOK (v: Values) (ls: list Lit) (w1 w2: Lit): Prop :=
  (In w1 ls /\ lookup v w1 = Some true) \/
  (In w2 ls /\ lookup v w2 = Some true) \/
  (In w1 ls /\ In w2 ls /\ w1 <> w2 /\ lookup v w1 = None /\ lookup v w2 = None).

(* Whether watched literals are fine depends only on the values of literals. *)
Lemma watch_ok_ext: forall (v v': Values) (ls: list Lit) (w1 w2: Lit),
  (forall (l: Lit), lookup v l = lookup v' l) -> WatchOK v ls w1 w2 -> WatchOK v' ls w1 w2.
Proof. intros v v' ls w1 w2 Hext Hok. unfold WatchOK in *. now rewrite <- !Hext. Qed.

(* Every clause has fine watched literals or is pending under one of them. *)
Definition Covered (v: Values) (cm: ClauseMap) (w: Watches) (todo: list (Lit * list nat)): Prop :=
  forall (i: nat) (ls: list Lit) (w1 w2: Lit), tget cm i = Some ls -> tget w i = (w1, w2) ->
  WatchOK v ls w1 w2 \/ Pending todo i w1 \/ Pending todo i w2.

(* The clause with literals ls is neither false nor unit under v: it has a true literal or two unassigned ones. *)
Definition Settled (v: Values) (ls: list Lit): Prop :=
  (exists (l: Lit), In l ls /\ lookup v l = Some true) \/
  (exists (l1 l2: Lit), In l1 ls /\ In l2 ls /\ l1 <> l2 /\ lookup v l1 = None /\ lookup v l2 = None).

Lemma watch_ok_settled: forall (v: Values) (ls: list Lit) (w1 w2: Lit), WatchOK v ls w1 w2 -> Settled v ls.
Proof.
  intros v ls w1 w2 [[Hw1 Hl1]|[[Hw2 Hl2]|(Hw1 & Hw2 & Hneq & Hl1 & Hl2)]].
  - left. now exists w1.
  - left. now exists w2.
  - right. now exists w1, w2.
Qed.

(* Assigning an unassigned literal l keeps the watched literals fine, unless one of them is ¬l. *)
Lemma watch_ok_cons: forall (v: Values) (ls: list Lit) (w1 w2 l: Lit),
  WatchOK v ls w1 w2 -> lookup v l = None -> w1 <> ¬l -> w2 <> ¬l ->
  WatchOK (set_value v l) ls w1 w2.
Proof.
  intros v ls w1 w2 l [[Hw1 Hl1]|[[Hw2 Hl2]|(Hw1 & Hw2 & Hneq & Hl1 & Hl2)]] Hl Hneg1 Hneg2.
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

Lemma replace_watch_spec: forall (v: Values) (ls: list Lit) (w other r: Lit),
  In w ls -> replace_watch v ls w other = Some r -> In r ls /\ lookup v r <> Some false /\ r <> other.
Proof.
  intros v ls w other r Hw. unfold replace_watch.
  destruct (not_false v w && negb (w =? other)) eqn:Hkeep.
  - intros Heq. injection Heq as <-. apply andb_prop in Hkeep as [Hnot_false Hneq]. split.
    + assumption.
    + split.
      * unfold not_false in Hnot_false. destruct (lookup v w) as [[|]|]; easy.
      * apply negb_true_iff in Hneq. now apply Lit.eqb_neq in Hneq.
  - intros Hfind. apply find_some in Hfind as [Hin Hr]. apply andb_prop in Hr as [Hnot_false Hneq]. split.
    + assumption.
    + split.
      * unfold not_false in Hnot_false. destruct (lookup v r) as [[|]|]; easy.
      * apply negb_true_iff in Hneq. now apply Lit.eqb_neq in Hneq.
Qed.

Lemma replace_watch_exists: forall (v: Values) (ls: list Lit) (w other r: Lit),
  In r ls -> lookup v r <> Some false -> r <> other -> exists (r': Lit), replace_watch v ls w other = Some r'.
Proof.
  intros v ls w other r Hr_in Hr Hneq. unfold replace_watch.
  destruct (not_false v w && negb (w =? other)).
  - now exists w.
  - destruct (find (fun (r: Lit) => not_false v r && negb (r =? other)) ls) as [r'|] eqn:Hfind.
    + now exists r'.
    + exfalso. apply find_none with (x := r) in Hfind.
      * apply andb_false_iff in Hfind as [Hfalse|Heq].
        -- unfold not_false in Hfalse. destruct (lookup v r) as [[|]|]; easy.
        -- apply negb_false_iff in Heq. now apply Lit.eqb_eq in Heq.
      * assumption.
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

Lemma repair_spec: forall (v: Values) (ls: list Lit) (w1 w2 a b: Lit),
  (ls = [] /\ w1 = w2) \/ (In w1 ls /\ In w2 ls) ->
  repair v ls w1 w2 = Some (a, b) -> WatchOK v ls a b /\ In a ls /\ In b ls.
Proof.
  intros v ls w1 w2 a b Hmembers. unfold repair. destruct ls as [|l0 ls'].
  - discriminate.
  - destruct Hmembers as [[Hnil _]|[Hw1 Hw2]].
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
        -- apply (replace_watch_spec v) in Ha as (Ha_in & Ha & _).
          ++ destruct (replace_watch v (l0 :: ls') w2 a') as [b'|] eqn:Hb.
            ** intros Heq. injection Heq as <- <-. apply (replace_watch_spec v) in Hb as (Hb_in & Hb & Hneq).
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
            ** destruct (lookup_true v a') eqn:Ha_true.
              --- intros Heq. injection Heq as <- <-. split.
                +++ left. split.
                  *** assumption.
                  *** unfold lookup_true in Ha_true. destruct (lookup v a') as [[|]|]; easy.
                +++ now split.
              --- discriminate.
          ++ assumption.
        -- discriminate.
Qed.

(* The watched literals of a settled clause can always be repaired. *)
Lemma repair_settled: forall (v: Values) (ls: list Lit) (w1 w2: Lit),
  (ls = [] /\ w1 = w2) \/ (In w1 ls /\ In w2 ls) ->
  Settled v ls -> exists (p: Lit * Lit), repair v ls w1 w2 = Some p.
Proof.
  intros v ls w1 w2 Hmembers Hsettled. unfold repair. destruct ls as [|l0 ls'].
  - exfalso. destruct Hsettled as [[t [[] _]]|[u1 [_ [[] _]]]].
  - destruct Hmembers as [[Hnil _]|[Hw1 Hw2]].
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
                +++ destruct (replace_watch_exists v (l0 :: ls') w2 a t) as [b Hb'].
                  *** assumption.
                  *** congruence.
                  *** intros ->. unfold lookup_true in Ha_true. now rewrite Ht in Ha_true.
                  *** congruence.
            ** destruct (replace_watch_exists v (l0 :: ls') w1 w2 t) as [a Ha'].
              --- assumption.
              --- congruence.
              --- assumption.
              --- congruence.
        (* Two unassigned literals u1 and u2 *)
        -- destruct (replace_watch v (l0 :: ls') w1 w2) as [a|] eqn:Ha.
          ++ destruct (replace_watch v (l0 :: ls') w2 a) as [b|] eqn:Hb.
            ** now exists (a, b).
            ** exfalso. destruct (Lit.eq_dec u1 a) as [->|Hu1_a].
              --- destruct (replace_watch_exists v (l0 :: ls') w2 a u2) as [b Hb'].
                +++ assumption.
                +++ congruence.
                +++ intros ->. now apply Hneq.
                +++ congruence.
              --- destruct (replace_watch_exists v (l0 :: ls') w2 a u1) as [b Hb'].
                +++ assumption.
                +++ congruence.
                +++ assumption.
                +++ congruence.
          ++ exfalso. destruct (Lit.eq_dec u1 w2) as [->|Hu1_w2].
            ** destruct (replace_watch_exists v (l0 :: ls') w1 w2 u2) as [a Ha'].
              --- assumption.
              --- congruence.
              --- intros ->. now apply Hneq.
              --- congruence.
            ** destruct (replace_watch_exists v (l0 :: ls') w1 w2 u1) as [a Ha'].
              --- assumption.
              --- congruence.
              --- assumption.
              --- congruence.
Qed.

(* The watched literals of every clause are fine with respect to v. *)
Definition AllWatchOK (v: Values) (cm: ClauseMap) (w: Watches): Prop :=
  forall (i: nat) (ls: list Lit) (w1 w2: Lit), tget cm i = Some ls -> tget w i = (w1, w2) -> WatchOK v ls w1 w2.

(* Two distinct literals of a clause that are not false with respect to v are fine watches with respect to the
   earlier values v'. *)
Lemma watch_ok_not_false: forall (v' v: Values) (ls: list Lit) (a b: Lit),
  Incl v' v -> In a ls -> In b ls -> a <> b -> lookup v a <> Some false -> lookup v b <> Some false ->
  WatchOK v' ls a b.
Proof.
  intros v' v ls a b Hincl Ha_in Hb_in Hneq Ha Hb. destruct (lookup v' a) as [[|]|] eqn:Ha'.
  - left. now split.
  - apply Hincl in Ha'. contradiction.
  - destruct (lookup v' b) as [[|]|] eqn:Hb'.
    + right. left. now split.
    + apply Hincl in Hb'. contradiction.
    + right. right. now repeat split.
Qed.

(* Repairing watches that are fine with respect to the earlier values v' keeps them fine with respect to v':
   watches are only moved to literals that are not false, so a backtrack to v' can keep them. *)
Lemma repair_watch_ok_incl: forall (v' v: Values) (ls: list Lit) (w1 w2 a b: Lit),
  Incl v' v -> WatchOK v' ls w1 w2 -> repair v ls w1 w2 = Some (a, b) -> WatchOK v' ls a b.
Proof.
  intros v' v ls w1 w2 a b Hincl Hok. unfold repair. destruct ls as [|l0 ls'].
  - discriminate.
  - destruct (lookup_true v w1 || lookup_true v w2) eqn:Htrue.
    + intros Heq. injection Heq as <- <-. assumption.
    + apply orb_false_iff in Htrue as [Hw1_true Hw2_true].
      destruct Hok as [[_ Hl1]|[[_ Hl2]|(Hw1 & Hw2 & Hneq & Hl1 & Hl2)]].
      (* A watch that is true with respect to v' is true with respect to v *)
      * apply Hincl in Hl1. unfold lookup_true in Hw1_true. now rewrite Hl1 in Hw1_true.
      * apply Hincl in Hl2. unfold lookup_true in Hw2_true. now rewrite Hl2 in Hw2_true.
      * destruct (replace_watch v (l0 :: ls') w1 w2) as [a'|] eqn:Ha.
        -- apply (replace_watch_spec v) in Ha as (Ha_in & Ha & Ha_w2).
          ++ destruct (replace_watch v (l0 :: ls') w2 a') as [b'|] eqn:Hb.
            ** intros Heq. injection Heq as <- <-. apply (replace_watch_spec v) in Hb as (Hb_in & Hb & Hb_a).
              --- apply (watch_ok_not_false v' v).
                +++ assumption.
                +++ assumption.
                +++ assumption.
                +++ intros ->. now apply Hb_a.
                +++ assumption.
                +++ assumption.
              --- assumption.
            (* a' is true and w2 stays: it is unassigned with respect to v' *)
            ** destruct (lookup_true v a').
              --- intros Heq. injection Heq as <- <-. destruct (lookup v' a') as [[|]|] eqn:Ha'.
                +++ left. now split.
                +++ apply Hincl in Ha'. contradiction.
                +++ right. right. now repeat split.
              --- discriminate.
          ++ assumption.
        -- discriminate.
Qed.

(* Clause i, which watched w1 and w2 and is visited as a watcher of p, now watches x: add it to the watch list of
   x, unless it is still there, i.e. x is w1 or w2 but not p, whose watch list i was taken out of. *)
Definition add_watch (wl: WatchLists) (i: nat) (p w1 w2 x: Lit): WatchLists :=
if ((x =? w1) || (x =? w2)) && negb (x =? p) then wl else watch wl x i.

Lemma add_watch_keep: forall (wl: WatchLists) (i j: nat) (p w1 w2 x y: Lit),
  In j (watching wl y) -> In j (watching (add_watch wl i p w1 w2 x) y).
Proof.
  intros wl i j p w1 w2 x y Hin. unfold add_watch. destruct (((x =? w1) || (x =? w2)) && negb (x =? p)).
  - assumption.
  - apply watching_watch. now right.
Qed.

Lemma add_watch_new: forall (wl: WatchLists) (i: nat) (p w1 w2 x: Lit),
  x = p \/ (x <> w1 /\ x <> w2) -> In i (watching (add_watch wl i p w1 w2 x) x).
Proof.
  intros wl i p w1 w2 x Hx. unfold add_watch. destruct (((x =? w1) || (x =? w2)) && negb (x =? p)) eqn:Hskip.
  - exfalso. apply andb_prop in Hskip as [Hw Hp]. destruct Hx as [->|[Hw1 Hw2]].
    + rewrite Lit.eqb_refl in Hp. discriminate.
    + apply orb_true_iff in Hw as [Heq|Heq].
      * apply Lit.eqb_eq in Heq. contradiction.
      * apply Lit.eqb_eq in Heq. contradiction.
  - apply watching_watch. now left.
Qed.

(* Visit the clauses ws watching the false literal p: drop those that no longer watch p, put those whose other
   watch is true back into the watch list of p without looking at their literals, and repair the watches of the
   others, putting those that keep watching p back as well, until one cannot be repaired. Returns the clauses
   still to visit, starting with that one. *)
Fixpoint visit (v: Values) (cm: ClauseMap) (p: Lit) (w: Watches) (wl: WatchLists) (ws: list nat):
  Watches * WatchLists * list nat :=
match ws with
| []        => (w, wl, [])
| i :: rest =>
  match tget w i with
  | (w1, w2) =>
    if (w1 =? p) || (w2 =? p) then
      let o := if w1 =? p then w2 else w1 in
      if negb (o =? p) && lookup_true v o then visit v cm p w (watch wl p i) rest else
      match tget cm i with
      | Some ls =>
        match repair v ls w1 w2 with
        | Some (a, b) =>
          if (a =? w1) && (b =? w2) then visit v cm p w (watch wl p i) rest
          else visit v cm p (tset w i (a, b)) (add_watch (add_watch wl i p w1 w2 a) i p w1 w2 b) rest
        | None        => (w, wl, ws)
        end
      | None    => visit v cm p w wl rest
      end
    else visit v cm p w wl rest
  end
end.

(* A stuck clause i: its watches cannot be repaired. *)
Definition Stuck (v: Values) (cm: ClauseMap) (w: Watches) (i: nat): Prop :=
  exists (ls: list Lit) (w1 w2: Lit), tget cm i = Some ls /\ tget w i = (w1, w2) /\ repair v ls w1 w2 = None.

(* Dropping clause i from the pending item of p, when it is not a clause or no longer watches p, while the watch
   lists grow. *)
Lemma struct_drop: forall (cm: ClauseMap) (w: Watches) (wl wl': WatchLists) (todo: list (Lit * list nat)) (p: Lit)
  (rest: list nat) (i: nat),
  WatchStruct cm w wl ((p, i :: rest) :: todo) ->
  (forall (j: nat) (z: Lit), In j (watching wl z) -> In j (watching wl' z)) ->
  (forall (ls: list Lit) (w1 w2: Lit), tget cm i = Some ls -> tget w i = (w1, w2) -> w1 <> p /\ w2 <> p) ->
  WatchStruct cm w wl' ((p, rest) :: todo).
Proof.
  intros cm w wl wl' todo p rest i Hstruct Hwl Hnot j ls w1 w2 Hj Hw. destruct (Hstruct j ls w1 w2 Hj Hw) as (H1 & H2 & Hm).
  assert (Hji: forall (x: Lit), x = w1 \/ x = w2 -> j <> i \/ x <> p).
  - intros x Hx. destruct (Nat.eq_dec j i) as [->|Hneq].
    + right. destruct (Hnot ls w1 w2 Hj Hw) as [Hw1 Hw2]. destruct Hx as [-> | ->].
      * assumption.
      * assumption.
    + now left.
  - split.
    + apply (watched_drop wl wl' todo p w1 rest i j).
      * intros z. apply Hwl.
      * apply Hji. now left.
      * assumption.
    + split.
      * apply (watched_drop wl wl' todo p w2 rest i j).
        -- intros z. apply Hwl.
        -- apply Hji. now right.
        -- assumption.
      * assumption.
Qed.

Lemma covered_drop: forall (v: Values) (cm: ClauseMap) (w: Watches) (todo: list (Lit * list nat)) (p: Lit)
  (rest: list nat) (i: nat),
  Covered v cm w ((p, i :: rest) :: todo) ->
  (forall (ls: list Lit) (w1 w2: Lit), tget cm i = Some ls -> tget w i = (w1, w2) -> w1 <> p /\ w2 <> p) ->
  Covered v cm w ((p, rest) :: todo).
Proof.
  intros v cm w todo p rest i Hcover Hnot j ls w1 w2 Hj Hw.
  assert (Hji: forall (x: Lit), x = w1 \/ x = w2 -> j <> i \/ x <> p).
  - intros x Hx. destruct (Nat.eq_dec j i) as [->|Hneq].
    + right. destruct (Hnot ls w1 w2 Hj Hw) as [Hw1 Hw2]. destruct Hx as [-> | ->].
      * assumption.
      * assumption.
    + now left.
  - destruct (Hcover j ls w1 w2 Hj Hw) as [Hok|[Hpend1|Hpend2]].
    + now left.
    + right. left. apply (pending_drop todo p w1 rest i j).
      * apply Hji. now left.
      * assumption.
    + right. right. apply (pending_drop todo p w2 rest i j).
      * apply Hji. now right.
      * assumption.
Qed.

(* Giving clause i, pending under p, the fine watches a and b, in which it is watched, and adding to the watch
   lists keeps the structure without its pending item. *)
Lemma struct_move: forall (v: Values) (cm: ClauseMap) (w w': Watches) (wl wl': WatchLists)
  (todo: list (Lit * list nat)) (p: Lit) (rest: list nat) (i: nat) (ls: list Lit) (a b: Lit),
  WatchStruct cm w wl ((p, i :: rest) :: todo) ->
  Covered v cm w ((p, i :: rest) :: todo) ->
  tget cm i = Some ls ->
  tget w' i = (a, b) ->
  (forall (j: nat), i <> j -> tget w' j = tget w j) ->
  (forall (j: nat) (z: Lit), In j (watching wl z) -> In j (watching wl' z)) ->
  Watched wl' ((p, rest) :: todo) i a ->
  Watched wl' ((p, rest) :: todo) i b ->
  WatchOK v ls a b -> In a ls -> In b ls ->
  WatchStruct cm w' wl' ((p, rest) :: todo) /\ Covered v cm w' ((p, rest) :: todo).
Proof.
  intros v cm w w' wl wl' todo p rest i ls a b Hstruct Hcover Hc Hw Hother Hwl Ha Hb Hok Ha_in Hb_in. split.
  - intros j ls' w1 w2 Hj Hwj. destruct (Nat.eq_dec i j) as [<-|Hneq].
    + rewrite Hw in Hwj. injection Hwj as <- <-. rewrite Hc in Hj. injection Hj as <-. split.
      * assumption.
      * split.
        -- assumption.
        -- right. now split.
    + rewrite Hother in Hwj.
      2: assumption.
      destruct (Hstruct j ls' w1 w2 Hj Hwj) as (Hj1 & Hj2 & Hm). split.
      * apply (watched_drop wl wl' todo p w1 rest i j).
        -- intros z. apply Hwl.
        -- left. intros ->. now apply Hneq.
        -- assumption.
      * split.
        -- apply (watched_drop wl wl' todo p w2 rest i j).
          ++ intros z. apply Hwl.
          ++ left. intros ->. now apply Hneq.
          ++ assumption.
        -- assumption.
  - intros j ls' w1 w2 Hj Hwj. destruct (Nat.eq_dec i j) as [<-|Hneq].
    + rewrite Hw in Hwj. injection Hwj as <- <-. rewrite Hc in Hj. injection Hj as <-. now left.
    + rewrite Hother in Hwj.
      2: assumption.
      destruct (Hcover j ls' w1 w2 Hj Hwj) as [Hok'|[Hpend1|Hpend2]].
      * now left.
      * right. left. apply (pending_drop todo p w1 rest i j).
        -- left. intros ->. now apply Hneq.
        -- assumption.
      * right. right. apply (pending_drop todo p w2 rest i j).
        -- left. intros ->. now apply Hneq.
        -- assumption.
Qed.

Lemma visit_spec: forall (v: Values) (cm: ClauseMap) (p: Lit) (todo: list (Lit * list nat)) (ws: list nat)
  (w w': Watches) (wl wl': WatchLists) (ws': list nat),
  WatchStruct cm w wl ((p, ws) :: todo) ->
  Covered v cm w ((p, ws) :: todo) ->
  visit v cm p w wl ws = (w', wl', ws') ->
  WatchStruct cm w' wl' ((p, ws') :: todo) /\ Covered v cm w' ((p, ws') :: todo) /\
  (ws' = [] \/ exists (i: nat) (rest: list nat), ws' = i :: rest /\ Stuck v cm w' i).
Proof.
  intros v cm p todo ws. induction ws as [|i rest IH]; intros w w' wl wl' ws' Hstruct Hcover Hvisit; simpl in Hvisit.
  - injection Hvisit as <- <- <-. split.
    + assumption.
    + split.
      * assumption.
      * now left.
  - destruct (tget w i) as [w1 w2] eqn:Hw. destruct ((w1 =? p) || (w2 =? p)) eqn:Hwatch.
    + (* Putting i back into the watch list of p keeps it watched by each literal *)
      assert (Hgrow: forall (j: nat) (z: Lit), In j (watching wl z) -> In j (watching (watch wl p i) z)).
      * intros j z Hz. apply watching_watch. now right.
      * assert (Hback: forall (x: Lit), Watched wl ((p, i :: rest) :: todo) i x ->
          Watched (watch wl p i) ((p, rest) :: todo) i x).
        -- intros x Hx. destruct (Lit.eq_dec x p) as [->|Hxp].
          ++ left. apply watching_watch. left. now split.
          ++ apply (watched_drop wl (watch wl p i) todo p x rest i i).
            ** intros z. apply Hgrow.
            ** now right.
            ** assumption.
        -- set (o := if w1 =? p then w2 else w1) in Hvisit.
           destruct (negb (o =? p) && lookup_true v o) eqn:Hfast.
          (* The other watch o is true: i goes back into the watch list of p *)
          ++ apply andb_prop in Hfast as [Hop Ho_true]. apply negb_true_iff, Lit.eqb_neq in Hop.
             assert (Ho: o = w1 \/ o = w2).
            ** unfold o. destruct (w1 =? p).
              --- now right.
              --- now left.
            ** destruct (tget cm i) as [ls|] eqn:Hc.
              --- destruct (Hstruct i ls w1 w2 Hc Hw) as (Hin1 & Hin2 & Hmembers).
                  (* i is not empty: an empty clause watches p twice, so its other watch is p *)
                  assert (Hm: In w1 ls /\ In w2 ls).
                +++ destruct Hmembers as [[_ Heq]|Hm].
                  *** exfalso. apply Hop. unfold o. rewrite <- Heq in Hwatch |- *. rewrite orb_diag in Hwatch.
                      rewrite Hwatch. simpl. now apply Lit.eqb_eq in Hwatch.
                  *** assumption.
                +++ destruct Hm as [Hm1 Hm2].
                    destruct (struct_move v cm w w wl (watch wl p i) todo p rest i ls w1 w2) as [Hstruct' Hcover'].
                  *** assumption.
                  *** assumption.
                  *** assumption.
                  *** assumption.
                  *** easy.
                  *** assumption.
                  *** now apply Hback.
                  *** now apply Hback.
                  *** unfold lookup_true in Ho_true. destruct Ho as [Heq|Heq].
                    ---- left. split.
                      ++++ assumption.
                      ++++ rewrite <- Heq. destruct (lookup v o) as [[|]|]; easy.
                    ---- right. left. split.
                      ++++ assumption.
                      ++++ rewrite <- Heq. destruct (lookup v o) as [[|]|]; easy.
                  *** assumption.
                  *** assumption.
                  *** now apply (IH w w' (watch wl p i) wl' ws').
              --- assert (Hnot: forall (ls: list Lit) (w1' w2': Lit), tget cm i = Some ls -> tget w i = (w1', w2') ->
                    w1' <> p /\ w2' <> p).
                +++ intros ls w1' w2' Hi. congruence.
                +++ apply (IH w w' (watch wl p i) wl' ws').
                  *** now apply (struct_drop cm w wl (watch wl p i) todo p rest i).
                  *** now apply (covered_drop v cm w todo p rest i).
                  *** assumption.
          ++ destruct (tget cm i) as [ls|] eqn:Hc.
            ** destruct (Hstruct i ls w1 w2 Hc Hw) as (Hin1 & Hin2 & Hmembers).
               destruct (repair v ls w1 w2) as [[a b]|] eqn:Hrepair.
              --- apply (repair_spec v ls w1 w2 a b Hmembers) in Hrepair as (Hok & Ha & Hb).
                  destruct ((a =? w1) && (b =? w2)) eqn:Hsame.
                (* The watches of i stay the same, and i goes back into the watch list of p *)
                +++ apply andb_prop in Hsame as [Ha1 Hb2]. apply Lit.eqb_eq in Ha1, Hb2. subst a b.
                    destruct (struct_move v cm w w wl (watch wl p i) todo p rest i ls w1 w2) as [Hstruct' Hcover'].
                  *** assumption.
                  *** assumption.
                  *** assumption.
                  *** assumption.
                  *** easy.
                  *** assumption.
                  *** now apply Hback.
                  *** now apply Hback.
                  *** assumption.
                  *** assumption.
                  *** assumption.
                  *** now apply (IH w w' (watch wl p i) wl' ws').
                (* i moves its watches to a and b *)
                +++ set (wl2 := add_watch (add_watch wl i p w1 w2 a) i p w1 w2 b).
                    assert (Hwl2: forall (j: nat) (z: Lit), In j (watching wl z) -> In j (watching wl2 z)).
                  *** intros j z Hin. now apply add_watch_keep, add_watch_keep.
                  *** (* Each new watch x of i watches it: as before if it is w1 or w2 but not p, otherwise newly
                         added *)
                      assert (Hnew: forall (x: Lit), x = a \/ x = b -> Watched wl2 ((p, rest) :: todo) i x).
                    ---- intros x Hx. destruct (Lit.eq_dec x p) as [->|Hxp].
                      ++++ left. unfold wl2. destruct Hx as [<- | <-].
                        **** apply add_watch_keep. apply add_watch_new. now left.
                        **** apply add_watch_new. now left.
                      ++++ destruct (Lit.eq_dec x w1) as [->|Hxw1].
                        **** apply (watched_drop wl wl2 todo p w1 rest i i).
                          ----- intros z. apply Hwl2.
                          ----- now right.
                          ----- assumption.
                        **** destruct (Lit.eq_dec x w2) as [->|Hxw2].
                          ----- apply (watched_drop wl wl2 todo p w2 rest i i).
                            +++++ intros z. apply Hwl2.
                            +++++ now right.
                            +++++ assumption.
                          ----- left. unfold wl2. destruct Hx as [-> | ->].
                            +++++ apply add_watch_keep. apply add_watch_new. right. now split.
                            +++++ apply add_watch_new. right. now split.
                    ---- destruct (struct_move v cm w (tset w i (a, b)) wl wl2 todo p rest i ls a b) as [Hstruct' Hcover'].
                      ++++ assumption.
                      ++++ assumption.
                      ++++ assumption.
                      ++++ apply tget_tset_same.
                      ++++ intros j Hneq. now apply tget_tset_other.
                      ++++ assumption.
                      ++++ apply Hnew. now left.
                      ++++ apply Hnew. now right.
                      ++++ assumption.
                      ++++ assumption.
                      ++++ assumption.
                      ++++ now apply (IH (tset w i (a, b)) w' wl2 wl' ws').
              (* i is stuck *)
              --- injection Hvisit as <- <- <-. split.
                +++ assumption.
                +++ split.
                  *** assumption.
                  *** right. exists i, rest. split.
                    ---- reflexivity.
                    ---- now exists ls, w1, w2.
            (* i is not a clause: drop it *)
            ** assert (Hnot: forall (ls: list Lit) (w1' w2': Lit), tget cm i = Some ls -> tget w i = (w1', w2') ->
                 w1' <> p /\ w2' <> p).
              --- intros ls w1' w2' Hi. congruence.
              --- apply (IH w w' wl wl' ws').
                +++ now apply (struct_drop cm w wl wl todo p rest i).
                +++ now apply (covered_drop v cm w todo p rest i).
                +++ assumption.
    (* i no longer watches p: drop it *)
    + apply orb_false_iff in Hwatch as [Hw1p Hw2p]. apply Lit.eqb_neq in Hw1p, Hw2p.
      assert (Hnot: forall (ls': list Lit) (w1' w2': Lit), tget cm i = Some ls' -> tget w i = (w1', w2') ->
        w1' <> p /\ w2' <> p).
      * intros ls' w1' w2' _ Hw'. rewrite Hw in Hw'. injection Hw' as <- <-. now split.
      * apply (IH w w' wl wl' ws').
        -- now apply (struct_drop cm w wl wl todo p rest i).
        -- now apply (covered_drop v cm w todo p rest i).
        -- assumption.
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

(* A property of the watched literals of each clause that repair keeps also holds after visiting. *)
Lemma visit_watches: forall (Q: list Lit -> Lit -> Lit -> Prop) (v: Values) (cm: ClauseMap) (p: Lit)
  (ws: list nat) (w w': Watches) (wl wl': WatchLists) (ws': list nat),
  (forall (ls: list Lit) (w1 w2 a b: Lit), Q ls w1 w2 -> repair v ls w1 w2 = Some (a, b) -> Q ls a b) ->
  (forall (i: nat) (ls: list Lit) (w1 w2: Lit), tget cm i = Some ls -> tget w i = (w1, w2) -> Q ls w1 w2) ->
  visit v cm p w wl ws = (w', wl', ws') ->
  forall (i: nat) (ls: list Lit) (w1 w2: Lit), tget cm i = Some ls -> tget w' i = (w1, w2) -> Q ls w1 w2.
Proof.
  intros Q v cm p ws. induction ws as [|i rest IH]; intros w w' wl wl' ws' Hrepair Hw Hvisit; simpl in Hvisit.
  - injection Hvisit as <- _ _. assumption.
  - destruct (tget w i) as [w1 w2] eqn:Hwi. destruct ((w1 =? p) || (w2 =? p)).
    + destruct (negb ((if w1 =? p then w2 else w1) =? p) && lookup_true v (if w1 =? p then w2 else w1)).
      * now apply (IH w w' (watch wl p i) wl' ws').
      * destruct (tget cm i) as [ls|] eqn:Hc.
        -- destruct (repair v ls w1 w2) as [[a b]|] eqn:Hrepair_i.
          ++ destruct ((a =? w1) && (b =? w2)).
            ** now apply (IH w w' (watch wl p i) wl' ws').
            ** apply (IH (tset w i (a, b)) w' (add_watch (add_watch wl i p w1 w2 a) i p w1 w2 b) wl' ws').
              --- assumption.
              --- intros j ls' w1' w2' Hj Hwj. rewrite tget_tset in Hwj. destruct (Nat.eq_dec i j) as [<-|Hneq].
                +++ injection Hwj as <- <-. rewrite Hc in Hj. injection Hj as <-. apply Hrepair with w1 w2.
                  *** now apply (Hw i).
                  *** assumption.
                +++ now apply (Hw j).
              --- assumption.
          ++ injection Hvisit as <- _ _. assumption.
        -- now apply (IH w w' wl wl' ws').
    + now apply (IH w w' wl wl' ws').
Qed.

(* Visit the pending items in turn, until a clause is stuck: it is then the first clause of the first item. *)
Fixpoint process (v: Values) (cm: ClauseMap) (w: Watches) (wl: WatchLists) (todo: list (Lit * list nat)):
  Watches * WatchLists * list (Lit * list nat) :=
match todo with
| []              => (w, wl, [])
| (p, ws) :: rest =>
  match visit v cm p w wl ws with
  | (w', wl', [])  => process v cm w' wl' rest
  | (w', wl', ws') => (w', wl', (p, ws') :: rest)
  end
end.

Lemma pending_empty_item: forall (todo: list (Lit * list nat)) (p x: Lit) (i: nat),
  Pending ((p, []) :: todo) i x -> Pending todo i x.
Proof. intros todo p x i Hpend. apply pending_cons in Hpend as [[_ []]|Hpend]. assumption. Qed.

Lemma watched_empty_item: forall (wl: WatchLists) (todo: list (Lit * list nat)) (p x: Lit) (i: nat),
  Watched wl ((p, []) :: todo) i x -> Watched wl todo i x.
Proof.
  intros wl todo p x i [Hin|Hpend].
  - now left.
  - right. now apply pending_empty_item in Hpend.
Qed.

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
  - destruct (visit v cm p w wl ws) as [[w1 wl1] ws1] eqn:Hvisit.
    destruct (visit_spec v cm p rest ws w w1 wl wl1 ws1 Hstruct Hcover Hvisit) as (Hstruct1 & Hcover1 & Hstuck).
    destruct ws1 as [|i ws1].
    + apply (IH w1 w' wl1 wl' todo').
      * intros j ls w1' w2' Hj Hw. destruct (Hstruct1 j ls w1' w2' Hj Hw) as (Hj1 & Hj2 & Hmembers). split.
        -- now apply watched_empty_item in Hj1.
        -- split.
          ++ now apply watched_empty_item in Hj2.
          ++ assumption.
      * intros j ls w1' w2' Hj Hw. destruct (Hcover1 j ls w1' w2' Hj Hw) as [Hok|[Hpend1|Hpend2]].
        -- now left.
        -- right. left. now apply pending_empty_item in Hpend1.
        -- right. right. now apply pending_empty_item in Hpend2.
      * assumption.
    + injection Hprocess as <- <- <-. split.
      * assumption.
      * split.
        -- assumption.
        -- right. destruct Hstuck as [Hnil|(i' & ws' & Heq & Hstuck)].
          ++ discriminate.
          ++ injection Heq as <- <-. now exists p, i, ws1, rest.
Qed.

(* Index the clauses with literals lss from k on, with their first literals watched, and each pending under its
   first watch so that it is checked once. *)
Fixpoint index_clauses (k: nat) (lss: list (list Lit)) (cm: ClauseMap) (w: Watches) (wl: WatchLists)
  (todo: list (Lit * list nat)): ClauseMap * Watches * WatchLists * list (Lit * list nat) :=
match lss with
| []        => (cm, w, wl, todo)
| ls :: lss =>
  index_clauses (S k) lss (tset cm k (Some ls)) (tset w k (first_watches ls))
    (watch (watch wl (fst (first_watches ls)) k) (snd (first_watches ls)) k) ((fst (first_watches ls), [k]) :: todo)
end.

(* Every clause is pending under its first watch. *)
Definition IndexPending (cm: ClauseMap) (w: Watches) (todo: list (Lit * list nat)): Prop :=
  forall (i: nat) (ls: list Lit) (w1 w2: Lit), tget cm i = Some ls -> tget w i = (w1, w2) -> Pending todo i w1.

Lemma index_clauses_spec: forall (lss: list (list Lit)) (k: nat) (cm cm': ClauseMap) (w w': Watches)
  (wl wl': WatchLists) (todo todo': list (Lit * list nat)),
  (forall (i: nat) (ls: list Lit), tget cm i = Some ls -> i < k) ->
  WatchStruct cm w wl todo ->
  IndexPending cm w todo ->
  index_clauses k lss cm w wl todo = (cm', w', wl', todo') ->
  WatchStruct cm' w' wl' todo' /\ IndexPending cm' w' todo' /\
  (forall (i: nat) (ls: list Lit), tget cm' i = Some ls -> tget cm i = Some ls \/ In ls lss) /\
  (forall (ls: list Lit), In ls lss -> exists (i: nat), tget cm' i = Some ls) /\
  (forall (i: nat) (ls: list Lit), tget cm i = Some ls -> tget cm' i = Some ls).
Proof.
  induction lss as [|ls lss IH]; intros k cm cm' w w' wl wl' todo todo' Hfresh Hstruct Hpending Hindex;
    simpl in Hindex.
  - injection Hindex as <- <- <- <-. split.
    + assumption.
    + split.
      * assumption.
      * split.
        -- intros i ls Hi. now left.
        -- split.
          ++ intros ls [].
          ++ easy.
  - set (todo1 := (fst (first_watches ls), [k]) :: todo) in Hindex.
    set (wl1 := watch (watch wl (fst (first_watches ls)) k) (snd (first_watches ls)) k) in Hindex.
    (* Every clause watched before stays watched *)
    assert (Hwatched: forall (j: nat) (x: Lit), Watched wl todo j x -> Watched wl1 todo1 j x).
    + intros j x [Hin|Hpend].
      * left. apply watching_watch. right. apply watching_watch. now right.
      * right. apply pending_cons. now right.
    + destruct (IH (S k) (tset cm k (Some ls)) cm' (tset w k (first_watches ls)) w' wl1 wl' todo1 todo')
        as (Hstruct' & Hpending' & Hsound & Hcomplete & Hkeep).
      * intros i ls' Hi. rewrite tget_tset in Hi. destruct (Nat.eq_dec k i) as [<-|Hneq].
        -- lia.
        -- apply Hfresh in Hi. lia.
      * intros i ls' w1 w2 Hi Hw. rewrite tget_tset in Hi. rewrite tget_tset in Hw. destruct (Nat.eq_dec k i) as [<-|Hneq].
        -- injection Hi as <-. split.
          ++ left. apply watching_watch. right. apply watching_watch. left. split.
            ** now rewrite Hw.
            ** reflexivity.
          ++ split.
            ** left. apply watching_watch. left. split.
              --- now rewrite Hw.
              --- reflexivity.
            ** destruct (first_watches_in ls) as [Hnil|[Hin1 Hin2]].
              --- left. split.
                +++ assumption.
                +++ rewrite Hnil in Hw. injection Hw as <- <-. reflexivity.
              --- right. rewrite Hw in Hin1, Hin2. now split.
        -- destruct (Hstruct i ls' w1 w2 Hi Hw) as (H1 & H2 & Hmembers). split.
          ++ now apply Hwatched.
          ++ split.
            ** now apply Hwatched.
            ** assumption.
      * intros i ls' w1 w2 Hi Hw. rewrite tget_tset in Hi. rewrite tget_tset in Hw. apply pending_cons.
        destruct (Nat.eq_dec k i) as [<-|Hneq].
        -- left. split.
          ++ now rewrite Hw.
          ++ now left.
        -- right. now apply (Hpending i ls' w1 w2).
      * assumption.
      * split.
        -- assumption.
        -- split.
          ++ assumption.
          ++ split.
            ** intros i ls' Hi. apply Hsound in Hi as [Hi|Hin].
              --- rewrite tget_tset in Hi. destruct (Nat.eq_dec k i) as [<-|Hneq].
                +++ injection Hi as <-. right. now left.
                +++ now left.
              --- right. now right.
            ** split.
              --- intros ls' [<-|Hin].
                +++ exists k. apply Hkeep. apply tget_tset_same.
                +++ now apply Hcomplete.
              --- intros i ls' Hi. apply Hkeep. rewrite tget_tset. destruct (Nat.eq_dec k i) as [<-|Hneq].
                +++ apply Hfresh in Hi. lia.
                +++ assumption.
Qed.

(* A property of the watched literals of each clause that repair keeps also holds after processing. *)
Lemma process_watches: forall (Q: list Lit -> Lit -> Lit -> Prop) (v: Values) (cm: ClauseMap)
  (todo: list (Lit * list nat)) (w w': Watches) (wl wl': WatchLists) (todo': list (Lit * list nat)),
  (forall (ls: list Lit) (w1 w2 a b: Lit), Q ls w1 w2 -> repair v ls w1 w2 = Some (a, b) -> Q ls a b) ->
  (forall (i: nat) (ls: list Lit) (w1 w2: Lit), tget cm i = Some ls -> tget w i = (w1, w2) -> Q ls w1 w2) ->
  process v cm w wl todo = (w', wl', todo') ->
  forall (i: nat) (ls: list Lit) (w1 w2: Lit), tget cm i = Some ls -> tget w' i = (w1, w2) -> Q ls w1 w2.
Proof.
  intros Q v cm todo. induction todo as [|[p ws] rest IH]; intros w w' wl wl' todo' Hrepair Hw Hprocess;
    simpl in Hprocess.
  - injection Hprocess as <- _ _. assumption.
  - destruct (visit v cm p w wl ws) as [[w0 wl0] ws0] eqn:Hvisit.
    assert (Hw0: forall (i: nat) (ls: list Lit) (w1 w2: Lit), tget cm i = Some ls -> tget w0 i = (w1, w2) -> Q ls w1 w2).
    + now apply (visit_watches Q v cm p ws w w0 wl wl0 ws0).
    + destruct ws0 as [|j ws0].
      * now apply (IH w0 w' wl0 wl' todo').
      * injection Hprocess as <- _ _. assumption.
Qed.

(* Processing with respect to v keeps the watches fine with respect to the earlier values v'. *)
Lemma process_watch_ok: forall (v' v: Values) (cm: ClauseMap) (todo: list (Lit * list nat)) (w w': Watches)
  (wl wl': WatchLists) (todo': list (Lit * list nat)),
  Incl v' v ->
  WatchStruct cm w wl todo ->
  AllWatchOK v' cm w ->
  process v cm w wl todo = (w', wl', todo') ->
  AllWatchOK v' cm w'.
Proof.
  intros v' v cm todo w w' wl wl' todo' Hincl Hstruct Hok Hprocess i ls w1 w2 Hc Hw.
  apply (process_watches (fun (ls: list Lit) (w1 w2: Lit) =>
    ((ls = [] /\ w1 = w2) \/ (In w1 ls /\ In w2 ls)) /\ WatchOK v' ls w1 w2)
    v cm todo w w' wl wl' todo') with i ls w1 w2 in Hprocess as [_ Hok'].
  - assumption.
  - intros ls' x y a b [Hmembers Hok_xy] Hrepair.
    destruct (repair_spec v ls' x y a b Hmembers Hrepair) as (_ & Ha & Hb). split.
    + right. now split.
    + now apply (repair_watch_ok_incl v' v ls' x y).
  - intros j ls' x y Hj Hwj. destruct (Hstruct j ls' x y Hj Hwj) as (_ & _ & Hmembers). split.
    + assumption.
    + now apply (Hok j ls').
  - assumption.
  - assumption.
Qed.

(* Put the clauses of the pending items back into the watch lists of their literals, without visiting them. *)
Fixpoint unpend (wl: WatchLists) (todo: list (Lit * list nat)): WatchLists :=
match todo with
| []              => wl
| (p, ws) :: rest => unpend (tset wl (lit_key p) (ws ++ watching wl p)) rest
end.

Lemma watching_unpend: forall (todo: list (Lit * list nat)) (wl: WatchLists) (i: nat) (x: Lit),
  Watched wl todo i x -> In i (watching (unpend wl todo) x).
Proof.
  intros todo. induction todo as [|[p ws] rest IH]; intros wl i x Hin; simpl.
  - destruct Hin as [Hin|[ws [[] _]]]. assumption.
  - apply IH. unfold Watched. rewrite watching_add. destruct Hin as [Hin|Hpend].
    + left. destruct (Lit.eq_dec p x) as [<-|Hneq].
      * apply in_app_iff. now right.
      * assumption.
    + apply pending_cons in Hpend as [[-> Hi]|Hpend].
      * left. destruct (Lit.eq_dec p p) as [_|Hneq].
        -- apply in_app_iff. now left.
        -- contradiction.
      * now right.
Qed.

(* After putting the pending clauses back, no clause is pending. *)
Lemma unpend_struct: forall (cm: ClauseMap) (w: Watches) (wl: WatchLists) (todo: list (Lit * list nat)),
  WatchStruct cm w wl todo -> WatchStruct cm w (unpend wl todo) [].
Proof.
  intros cm w wl todo Hstruct i ls w1 w2 Hi Hw. destruct (Hstruct i ls w1 w2 Hi Hw) as (H1 & H2 & Hmembers). split.
  - left. now apply watching_unpend.
  - split.
    + left. now apply watching_unpend.
    + assumption.
Qed.

(* A stuck clause is not settled: it is false or unit. *)
Lemma stuck_unsettled: forall (v: Values) (cm: ClauseMap) (w: Watches) (wl: WatchLists) (todo: list (Lit * list nat))
  (i: nat) (ls: list Lit) (w1 w2: Lit),
  WatchStruct cm w wl todo ->
  tget cm i = Some ls -> tget w i = (w1, w2) -> repair v ls w1 w2 = None -> ~ Settled v ls.
Proof.
  intros v cm w wl todo i ls w1 w2 Hstruct Hc Hw Hrepair Hsettled.
  destruct (Hstruct i ls w1 w2 Hc Hw) as (_ & _ & Hmembers). destruct (repair_settled v ls w1 w2) as [p Hp].
  - assumption.
  - assumption.
  - congruence.
Qed.

(* In a clause that is not settled, the first literal that is not false is its unit literal, and if there is
   none, all its literals are false. *)
Lemma unsettled_unit: forall (v: Values) (ls: list Lit) (u: Lit),
  ~ Settled v ls ->
  find (not_false v) ls = Some u ->
  In u ls /\ lookup v u = None /\ forall (l: Lit), In l ls -> l <> u -> lookup v l = Some false.
Proof.
  intros v ls u Hunsettled Hfind. apply find_some in Hfind as [Hu_in Hu].
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

Lemma unsettled_conflict: forall (v: Values) (ls: list Lit),
  find (not_false v) ls = None -> forall (l: Lit), In l ls -> lookup v l = Some false.
Proof.
  intros v ls Hfind l Hl_in. apply find_none with (x := l) in Hfind.
  - unfold not_false in Hfind. destruct (lookup v l) as [[|]|]; easy.
  - assumption.
Qed.

(* Make the watchers of the literals ls pending, emptying their watch lists, as after a restart. *)
Fixpoint pend_all (wl: WatchLists) (ls: list Lit) (todo: list (Lit * list nat)): WatchLists * list (Lit * list nat) :=
match ls with
| []       => (wl, todo)
| l :: ls' => pend_all (tset wl (lit_key l) []) ls' ((l, watching wl l) :: todo)
end.

(* Moving the watch list of l into the pending items keeps every clause watched. *)
Lemma watched_pend: forall (wl: WatchLists) (todo: list (Lit * list nat)) (l x: Lit) (i: nat),
  Watched wl todo i x -> Watched (tset wl (lit_key l) []) ((l, watching wl l) :: todo) i x.
Proof.
  intros wl todo l x i [Hin|Hpend].
  - unfold Watched. rewrite watching_add. destruct (Lit.eq_dec l x) as [<-|Hneq].
    + right. apply pending_cons. left. now split.
    + now left.
  - right. apply pending_cons. now right.
Qed.

Lemma pend_all_watched: forall (ls: list Lit) (wl wl': WatchLists) (todo todo': list (Lit * list nat)) (i: nat)
  (x: Lit),
  pend_all wl ls todo = (wl', todo') -> Watched wl todo i x -> Watched wl' todo' i x.
Proof.
  intros ls. induction ls as [|l ls IH]; intros wl wl' todo todo' i x Hpend Hx; simpl in Hpend.
  - now injection Hpend as <- <-.
  - apply (IH _ _ _ _ _ _ Hpend). now apply watched_pend.
Qed.

(* Afterwards the watch lists of ls are empty. *)
Lemma pend_all_empty: forall (ls: list Lit) (wl wl': WatchLists) (todo todo': list (Lit * list nat)) (x: Lit),
  pend_all wl ls todo = (wl', todo') -> watching wl x = [] \/ In x ls -> watching wl' x = [].
Proof.
  intros ls. induction ls as [|l ls IH]; intros wl wl' todo todo' x Hpend Hx; simpl in Hpend.
  - injection Hpend as <- <-. now destruct Hx as [Hx|[]].
  - apply (IH _ _ _ _ _ Hpend). rewrite watching_add. destruct (Lit.eq_dec l x) as [<-|Hneq].
    + now left.
    + destruct Hx as [Hx|[<-|Hin]].
      * now left.
      * contradiction.
      * now right.
Qed.

(* So a clause watching a literal of ls becomes pending. *)
Lemma pend_all_pending: forall (ls: list Lit) (wl wl': WatchLists) (todo todo': list (Lit * list nat)) (i: nat)
  (x: Lit),
  pend_all wl ls todo = (wl', todo') -> In x ls -> Watched wl todo i x -> Pending todo' i x.
Proof.
  intros ls wl wl' todo todo' i x Hpend Hx Hwatched. apply (pend_all_watched ls wl wl' todo todo' i x Hpend) in Hwatched.
  destruct Hwatched as [Hin|Hpending].
  - rewrite (pend_all_empty ls wl wl' todo todo' x Hpend) in Hin.
    + destruct Hin.
    + now right.
  - assumption.
Qed.

(* Pending clauses stay pending. *)
Lemma pend_all_pending_old: forall (ls: list Lit) (wl wl': WatchLists) (todo todo': list (Lit * list nat)) (i: nat)
  (x: Lit),
  pend_all wl ls todo = (wl', todo') -> Pending todo i x -> Pending todo' i x.
Proof.
  intros ls. induction ls as [|l ls IH]; intros wl wl' todo todo' i x Hpend Hx; simpl in Hpend.
  - now injection Hpend as <- <-.
  - apply (IH _ _ _ _ _ _ Hpend). apply pending_cons. now right.
Qed.

(* The watch structure survives. *)
Lemma pend_all_struct: forall (cm: ClauseMap) (w: Watches) (ls: list Lit) (wl wl': WatchLists)
  (todo todo': list (Lit * list nat)),
  pend_all wl ls todo = (wl', todo') -> WatchStruct cm w wl todo -> WatchStruct cm w wl' todo'.
Proof.
  intros cm w ls wl wl' todo todo' Hpend Hstruct i ls' w1 w2 Hi Hw.
  destruct (Hstruct i ls' w1 w2 Hi Hw) as (H1 & H2 & Hmembers). split.
  - now apply (pend_all_watched ls wl wl' todo todo').
  - split.
    + now apply (pend_all_watched ls wl wl' todo todo').
    + assumption.
Qed.
