(* unmark_lower unmarks the lower literals of the clause being analysed and finds the
   highest of their levels (unmark_lower). *)
From Stdlib Require Import List.
Import ListNotations.

From compcert Require Import Coqlib.
From compcert Require Import Maps.
From compcert Require Import Integers.
From compcert Require Import AST.
From compcert Require Import Values.
From compcert Require Import Memory.
From compcert Require Import Globalenvs.
From compcert Require Import Ctypes.
From compcert Require Import Cop.
From compcert Require Import Clight.
From compcert Require Import ClightBigstep.

From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table.
From RocqSAT.refinement Require Import Lookup.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement Require Import Analysis.
From RocqSAT.refinement.c Require Import Arrays.
From RocqSAT.refinement.c Require Import Logic.
From RocqSAT.refinement.c Require Import Common.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Rep.
From RocqSAT.refinement.c Require Import RepReasons.

(* The state of the loop of unmark_lower at q, with the context x1 and the highest level
   mx so far: the model from q on gives res, and only the marks changed since m. *)
Record UnmarkLowerInv {m: mem} {sh: Shape} {N: nat} {lss: list (list Lit)} {x: Ctx}
  {res: Ctx * nat} {q: nat} {x1: Ctx} {mx: nat} {le: temp_env} {m1: mem}: Prop := {
  ui_s: le ! _s = Some (sptr sh);
  ui_q: le ! _q = Some (vnat q);
  ui_mx: le ! _mx = Some (vnat mx);
  ui_le: (q <= length (lower x))%nat;
  ui_mx_le: (mx <= N)%nat;
  ui_lower: lower x1 = lower x;
  ui_res: unmark_lits x1 mx (skipn q (lower x)) = res;
  ui_rep: RepL m1 sh N lss x1;
  ui_frame: Mem.unchanged_on (AllBut (b_mrk sh)) m m1;
}.
Arguments UnmarkLowerInv : clear implicits.

(* The invariant of the loop: some state at q. *)
Definition unmark_lower_inv (m: mem) (sh: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (res: Ctx * nat) (q: nat) (le: temp_env) (m1: mem): Prop :=
  exists (x1: Ctx) (mx: nat), UnmarkLowerInv m sh N lss x res q x1 mx le m1.

(* After the state at q, the memory m2 with the literal y at q unmarked and the
   temporaries q + 1 and the new highest level give the invariant at q + 1. *)
Lemma unmark_inv_next: forall (m m1 m2: mem) (sh: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (res: Ctx * nat) (q: nat) (x1: Ctx) (mx: nat)
  (le le2: temp_env),
  UnmarkLowerInv m sh N lss x res q x1 mx le m1 -> (q < length (lower x))%nat ->
  RepL m2 sh N lss
    (x1 <| mrk := tset (mrk x1) (lit_key (nth q (lower x) (Pos 0%nat))) false |>) ->
  Mem.unchanged_on (AllBut (b_mrk sh)) m m2 ->
  le2 ! _s = Some (sptr sh) -> le2 ! _q = Some (vnat (S q)) ->
  le2 ! _mx = Some (vnat (Nat.max mx (level x1 (nth q (lower x) (Pos 0%nat))))) ->
  unmark_lower_inv m sh N lss x res (S q) le2 m2.
Proof.
  intros m m1 m2 sh N lss x res q x1 mx le le2 HI Hq HRep Hun Hs Hq' Hmx'.
  destruct HI as [_ _ _ _ Hmx Hlower Hres _ _].
  (* The level of the literal at q is at most N. *)
  assert (Hlv: (level x1 (nth q (lower x) (Pos 0%nat)) <= N)%nat).
  { apply (r_lvl_le HRep). apply (r_lt_atoms HRep). cbn [set_mrk lower].
    rewrite Hlower. apply nth_In. assumption. }
  exists (x1 <| mrk := tset (mrk x1) (lit_key (nth q (lower x) (Pos 0%nat))) false |>).
  exists (Nat.max mx (level x1 (nth q (lower x) (Pos 0%nat)))). constructor.
  - assumption.
  - assumption.
  - assumption.
  - lia.
  - lia.
  - assumption.
  - rewrite <- unmark_lits_skipn by assumption. assumption.
  - assumption.
  - assumption.
Qed.

(* unmark_lower unmarks the lower literals of x, one after the other, and takes the
   highest of their levels. Writing res for the model, unmark_lower x, and x1 for the
   current context:

     {{ RepL m sh N lss x }}
       int mx = 0;
       int q = 0;
     {{ unmark_lower_inv res 0: context x and mx = 0 }}
       while (q < s->ltlen) {
     {{ UnmarkLowerInv res q x1 mx /\ q < length (lower x) }}
         int y = s->lt[q];
         s->mrk[y] = 0;                                                   (rep_store_mrk)
         int v = s->lvl[y >> 1];
         if (v > mx) mx = v;
     {{ context x1 <| mrk := tset (mrk x1) y false |> /\ mx = Nat.max mx v }}
         q++;
     {{ unmark_lower_inv res (q + 1) }}                                 (unmark_inv_next)
       }
     {{ UnmarkLowerInv res (length (lower x)) x1 mx: res = (x1, mx) }}
       return mx;
     {{ RepL (fst res) /\ result = snd res /\ m' is m but for the marks }}

   The loop ends: length (lower x) - q decreases. *)
Lemma unmark_lower_correct: forall (sh: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx),
  {{ m | RepL m sh N lss x }}
    f_unmark_lower(sptr sh)
  {{ m', v | RepL m' sh N lss (fst (unmark_lower x)) /\
             v = vnat (snd (unmark_lower x)) /\
             Mem.unchanged_on (AllBut (b_mrk sh)) m m' }}.
Proof.
  intros sh N lss x m HRep. pose proof (r_n HRep) as HN.
  remember (unmark_lower x) as res eqn:Hres.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_unmark_lower. cbn [fn_body fn_return].
    (* int mx = 0; int q = 0; *)
    run.
    apply exec_loop with (R := ltof nat (fun (q: nat) => length (lower x) - q)%nat)
      (I := unmark_lower_inv m sh N lss x res) (a := 0%nat).
    + apply well_founded_ltof.
    + intros q le1 m1 (x1 & mx & HI).
      pose proof HI as [Hs Hq Hmx Hqle Hmxle Hlower Hacc HRep1 Hun].
      pose proof (r_nodup HRep1) as Hnd.
      pose proof (r_ltlen HRep1) as Fltlen.
      pose proof (r_lt_le HRep1) as Hltle.
      rewrite Hlower in Fltlen, Hltle.
      apply exec_seq.
      (* if (q < s->ltlen) ... else break; *)
      run. eapply exec_if_lt.
      * ev.
      * ev.
      * reflexivity.
      * lia.
      * (* q < length (lower x): the literal y at q *)
        intros Hlt. assert ((q < length (lower x))%nat) by lia.
        assert (Hy: (extract (nth q (lower x) (Pos 0%nat)) < N)%nat).
        { apply (r_lt_atoms HRep1). rewrite Hlower. apply nth_In. assumption. }
        pose proof (key_small _ N Hy HN) as Hkey.
        pose proof (lit_key_lt _ N Hy) as Hk.
        assert (Hadd: Int.add (Int.repr (Z.of_nat q)) (Int.repr 1)
                      = Int.repr (Z.of_nat (S q))).
        { rewrite add_repr by lia. f_equal. lia. }
        assert (Hshr: Int.shr (Int.repr (key (nth q (lower x) (Pos 0%nat))))
                        (Int.repr 1)
                      = Int.repr (Z.of_nat (extract (nth q (lower x) (Pos 0%nat))))).
        { apply shr_key. lia. }
        pose proof (r_lt HRep1) as Flt.
        pose proof (r_mrk HRep1) as Fmrk.
        pose proof (a_lt HRep1) as (tlt & Alt & Htlt). rewrite Hlower in Htlt.
        pose proof (a_mrk HRep1) as Amrk.
        (* int y = s->lt[q]; *)
        apply exec_skip. normal. run. rewrite (Htlt q) by assumption.
        (* s->mrk[y] = 0; *)
        eapply (exec_store_arr Amrk Hk).
        -- evl.
        -- ofs.
        -- reflexivity.
        -- ev.
        -- intros m2 Hst2. normal.
           assert (HRep2: RepL m2 sh N lss
                            (x1 <| mrk := tset (mrk x1)
                                    (lit_key (nth q (lower x) (Pos 0%nat))) false |>)).
           { apply (rep_store_mrk m1 m2 _ false HRep1 Hk Hst2). }
           assert (Hun2: Mem.unchanged_on
                           (AllBut (b_mrk sh)) m m2).
           { apply (store_unchanged _ m m1 m2 Mint32 (b_mrk sh)
                      (4 * Z.of_nat (lit_key (nth q (lower x) (Pos 0%nat))))
                      (vint 0)).
             - assumption.
             - assumption.
             - intros i Hi. now apply Hi. }
           keep_mem m2.
           pose proof (r_lvl HRep2) as Flvl.
           pose proof (a_lvl HRep2) as Alvl.
           cbn [set_mrk lvl] in Alvl.
           assert (Hlv: (level x1 (nth q (lower x) (Pos 0%nat))
                         <= N)%nat).
           { apply (r_lvl_le HRep1). assumption. }
           (* int v = s->lvl[y >> 1]; *)
           run.
           (* if (v > mx) mx = v; *)
           eapply exec_if_gt.
           ++ ev.
           ++ ev.
           ++ reflexivity.
           ++ lia.
           ++ (* a higher level: mx = v; q++; *)
              intros Hgt.
              run. ints. apply loopk_next with (S q).
              ** unfold ltof. lia.
              ** apply (unmark_inv_next m m1 m2 sh N lss x res q x1 mx le1).
                 --- assumption.
                 --- assumption.
                 --- assumption.
                 --- assumption.
                 --- tmp.
                 --- tmp.
                 --- rewrite Nat.max_r by lia. tmp.
           ++ (* not higher: q++; *)
              intros Hle.
              apply exec_skip. normal. run. ints.
              apply loopk_next with (S q).
              ** unfold ltof. lia.
              ** apply (unmark_inv_next m m1 m2 sh N lss x res q x1 mx le1).
                 --- assumption.
                 --- assumption.
                 --- assumption.
                 --- assumption.
                 --- tmp.
                 --- tmp.
                 --- rewrite Nat.max_l by lia. tmp.
      * (* q = length (lower x): break; return mx, and res = (mk, mx) *)
        intros Hge.
        assert (Hend: skipn q (lower x) = []) by (apply skipn_all2; lia).
        rewrite Hend in Hacc. cbn [unmark_lits] in Hacc. rewrite <- Hacc.
        apply exec_break. abrupt. apply loopk_break. normal.
        eapply exec_return.
        -- ev.
        -- exists (vnat mx). split.
           ++ apply result_int.
           ++ split.
              ** assumption.
              ** split.
                 --- reflexivity.
                 --- assumption.
    + (* The invariant holds at q = 0, with the marks of x and mx = 0. *)
      exists x, 0%nat. constructor.
      * tmp.
      * tmp.
      * tmp.
      * lia.
      * lia.
      * reflexivity.
      * rewrite Hres. reflexivity.
      * assumption.
      * apply Mem.unchanged_on_refl.
Qed.

Lemma unmark_lower_fun: FunAt _unmark_lower f_unmark_lower.
Proof. apply find_fun. reflexivity. Qed.
