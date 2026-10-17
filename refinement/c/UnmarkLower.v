(* unmark_lower unmarks the lower literals of the clause being analysed and finds the
   highest of their levels (unmark_lower). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Propagate Analysis.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep RepReasons.
Import ListNotations.

(* The model at position q of lt: it unmarks the literal there and takes the higher of
   its level and mx, and goes on with the rest. *)
Lemma unmark_lower_skipn: forall (lv: Table nat) (mk: Table bool) (mx: nat)
  (lt: list Lit) (q: nat), (q < length lt)%nat ->
  unmark_lower lv mk mx (skipn q lt)
  = unmark_lower lv (tset mk (lit_key (nth q lt (Pos 0%nat))) false)
      (Nat.max mx (tget lv (extract (nth q lt (Pos 0%nat))))) (skipn (Datatypes.S q) lt).
Proof.
  intros lv mk mx lt q Hq. rewrite (skipn_nth lt (Pos 0%nat) q Hq). reflexivity.
Qed.

(* The invariant of the loop of unmark_lower at q, for the memory m of the call: the
   temporaries hold s, q and the highest level mx so far, the model from marks mk and mx
   on the literals of lt from q on gives res (the loop follows the recursion of the
   model), and the memory m1 holds x with marks mk and is m but for the marks. *)
Record UnmarkInv (m: mem) (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (lt: list Lit) (res: Table bool * nat) (q: nat) (le: temp_env)
  (m1: mem): Prop := {
  ui_s: le ! _s = Some (sptr S);
  ui_q: le ! _q = Some (vint (Z.of_nat q));
  ui_le: (q <= length lt)%nat;
  ui_acc: exists (mk: Table bool) (mx: nat),
    le ! _mx = Some (vint (Z.of_nat mx)) /\ (mx <= N)%nat /\
    unmark_lower (lvl x) mk mx (skipn q lt) = res /\
    RepL m1 S N lss (set_mrk x mk) lims lt;
  ui_frame: Mem.unchanged_on (fun (b: block) (_: Z) => b <> b_mrk S) m m1;
}.

(* After the literal y at position q, with marks mk and highest level mx before it, the
   invariant holds at q + 1. *)
Lemma unmark_inv_next: forall (m m1: mem) (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (lt: list Lit) (res: Table bool * nat) (q: nat)
  (le: temp_env) (mk: Table bool) (mx: nat),
  (q < length lt)%nat -> (mx <= N)%nat ->
  unmark_lower (lvl x) mk mx (skipn q lt) = res ->
  RepL m1 S N lss (set_mrk x (tset mk (lit_key (nth q lt (Pos 0%nat))) false)) lims lt ->
  Mem.unchanged_on (fun (b: block) (_: Z) => b <> b_mrk S) m m1 ->
  le ! _s = Some (sptr S) -> le ! _q = Some (vint (Z.of_nat (Datatypes.S q))) ->
  le ! _mx = Some (vint (Z.of_nat
    (Nat.max mx (tget (lvl x) (extract (nth q lt (Pos 0%nat))))))) ->
  UnmarkInv m S N lss x lims lt res (Datatypes.S q) le m1.
Proof.
  intros m m1 S N lss x lims lt res q le mk mx Hq Hmx Hres HRep Hun Hs Hq' Hmx'.
  (* The level of the literal at q is at most N. *)
  assert (Hlv: (tget (lvl x) (extract (nth q lt (Pos 0%nat))) <= N)%nat).
  { apply (r_lvl_le _ _ _ _ _ _ _ HRep). apply (r_lt_atoms _ _ _ _ _ _ _ HRep).
    apply nth_In. assumption. }
  constructor.
  - assumption.
  - assumption.
  - lia.
  - exists (tset mk (lit_key (nth q lt (Pos 0%nat))) false).
    exists (Nat.max mx (tget (lvl x) (extract (nth q lt (Pos 0%nat))))). split.
    + assumption.
    + split.
      * lia.
      * split.
        -- rewrite <- unmark_lower_skipn by assumption. assumption.
        -- assumption.
  - assumption.
Qed.

(* unmark_lower unmarks the literals of lt, one after the other, and takes the highest of
   their levels. Writing res for the model, unmark_lower (lvl x) (mrk x) 0 lt:

     {{ RepL m S N lss x lims lt }}
       int mx = 0;
       int q = 0;
     {{ UnmarkInv res 0: marks mrk x and mx = 0 }}
       while (q < s->ltlen) {
     {{ UnmarkInv res q: marks mk and mx /\ q < length lt }}
         int y = s->lt[q];
         s->mrk[y] = 0;                                                   (rep_store_mrk)
         int v = s->lvl[y >> 1];
         if (v > mx) mx = v;
     {{ marks tset mk y false /\ mx = Nat.max mx v }}
         q++;
     {{ UnmarkInv res (q + 1) }}                                        (unmark_inv_next)
       }
     {{ UnmarkInv res (length lt): res = (mk, mx) }}
       return mx;
     {{ RepL (set_mrk x (fst res)) lt /\ result = snd res /\ m' is m but for the marks }}

   The loop ends: length lt - q decreases. *)
Lemma unmark_lower_correct {lt: list Lit}: forall (S: Shape) (N: nat)
  (lss: list (list Lit)) (x: Ctx) (lims: list nat),
  {{ m | RepL m S N lss x lims lt }}
    f_unmark_lower(sptr S)
  {{ m', v | RepL m' S N lss (set_mrk x (fst (unmark_lower (lvl x) (mrk x) 0 lt)))
               lims lt /\
             v = vint (Z.of_nat (snd (unmark_lower (lvl x) (mrk x) 0 lt))) /\
             Mem.unchanged_on (fun (b: block) (_: Z) => b <> b_mrk S) m m' }}.
Proof.
  intros S N lss x lims m HRep. pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  remember (unmark_lower (lvl x) (mrk x) 0 lt) as res eqn:Hres.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_unmark_lower. cbn [fn_body fn_return].
    (* int mx = 0; int q = 0; *)
    run.
    apply exec_loop with (R := ltof nat (fun (q: nat) => length lt - q)%nat)
      (I := UnmarkInv m S N lss x lims lt res) (a := 0%nat).
    + apply well_founded_ltof.
    + intros q le1 m1 HI.
      destruct HI as [Hs Hq Hqle (mk & mx & Hmx & Hmxle & Hacc & HRep1) Hun].
      pose proof (r_nodup _ _ _ _ _ _ _ HRep1) as Hnd.
      pose proof (r_ltlen _ _ _ _ _ _ _ HRep1) as Fltlen.
      pose proof (r_lt_le _ _ _ _ _ _ _ HRep1) as Hltle.
      apply exec_seq.
      (* if (q < s->ltlen) ... else break; *)
      run. eapply (exec_if_cmp _ _ _ Clt).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * unfold Small. lia.
      * unfold Small. lia.
      * destruct (Nat.lt_ge_cases q (length lt)) as [Hlt | Hge].
        -- (* q < length lt: the literal y at q *)
           replace (zcmp Clt (Z.of_nat q) (Z.of_nat (length lt))) with true
             by (symmetry; cbn [zcmp]; apply Z.ltb_lt; lia).
           assert (Hy: (extract (nth q lt (Pos 0%nat)) < N)%nat).
           { apply (r_lt_atoms _ _ _ _ _ _ _ HRep1). apply nth_In. assumption. }
           pose proof (key_small _ N Hy HN) as Hkey.
           pose proof (lit_key_lt _ N Hy) as Hk.
           assert (Hadd: Int.add (Int.repr (Z.of_nat q)) (Int.repr 1)
                         = Int.repr (Z.of_nat (Datatypes.S q))).
           { rewrite add_repr by lia. f_equal. lia. }
           assert (Hshr: Int.shr (Int.repr (key (nth q lt (Pos 0%nat)))) (Int.repr 1)
                         = Int.repr (Z.of_nat (extract (nth q lt (Pos 0%nat))))).
           { apply shr_key. lia. }
           pose proof (r_lt _ _ _ _ _ _ _ HRep1) as Flt.
           pose proof (r_mrk _ _ _ _ _ _ _ HRep1) as Fmrk.
           pose proof (a_lt _ _ _ _ _ _ _ HRep1) as (tlt & Alt & Htlt).
           pose proof (a_mrk _ _ _ _ _ _ _ HRep1) as Amrk.
           (* int y = s->lt[q]; *)
           cbv beta iota. apply exec_skip. normal. run. rewrite (Htlt q) by assumption.
           (* s->mrk[y] = 0; *)
           eapply exec_store.
           ++ evl.
           ++ ev.
           ++ reflexivity.
           ++ reflexivity.
           ++ ofs. bound.
           ++ ofs. cbn [cast_int_int].
              destruct (arr_storable m1 (b_mrk S) (2 * N)
                          (lit_key (nth q lt (Pos 0%nat))) _ 0 Amrk Hk) as [m2 Hst2].
              exists m2. split.
              ** apply Hst2.
              ** normal.
                 assert (HRep2: RepL m2 S N lss
                                  (set_mrk x (tset mk (lit_key (nth q lt (Pos 0%nat)))
                                     false)) lims lt).
                 { apply (rep_store_mrk m1 m2 S N lss (set_mrk x mk) lims _ false HRep1
                            Hk Hst2). }
                 assert (Hun2: Mem.unchanged_on
                                 (fun (b: block) (_: Z) => b <> b_mrk S) m m2).
                 { apply (store_unchanged _ m m1 m2 Mint32 (b_mrk S)
                            (4 * Z.of_nat (lit_key (nth q lt (Pos 0%nat)))) (vint 0)).
                   - assumption.
                   - assumption.
                   - intros i Hi. now apply Hi. }
                 keep_mem m2.
                 pose proof (r_lvl _ _ _ _ _ _ _ HRep2) as Flvl.
                 pose proof (a_lvl _ _ _ _ _ _ _ HRep2) as Alvl.
                 cbn [set_mrk lvl] in Alvl.
                 assert (Hlv: (tget (lvl x) (extract (nth q lt (Pos 0%nat))) <= N)%nat).
                 { apply (r_lvl_le _ _ _ _ _ _ _ HRep1). assumption. }
                 (* int v = s->lvl[y >> 1]; *)
                 run.
                 (* if (v > mx) mx = v; *)
                 eapply (exec_if_cmp _ _ _ Cgt).
                 --- ev.
                 --- ev.
                 --- reflexivity.
                 --- reflexivity.
                 --- unfold Small. lia.
                 --- unfold Small. lia.
                 --- cbn [zcmp].
                     destruct (Nat.ltb_spec mx
                                 (tget (lvl x) (extract (nth q lt (Pos 0%nat)))))
                       as [Hgt | Hle].
                     +++ (* a higher level: mx = v; q++; *)
                         replace (Z.of_nat mx <? Z.of_nat (tget (lvl x)
                                    (extract (nth q lt (Pos 0%nat))))) with true
                           by (symmetry; apply Z.ltb_lt; lia).
                         run. ints. apply loopk_next with (Datatypes.S q).
                         *** unfold ltof. lia.
                         *** apply (unmark_inv_next m m2 S N lss x lims lt res q _ mk
                                      mx).
                             ---- assumption.
                             ---- assumption.
                             ---- assumption.
                             ---- assumption.
                             ---- assumption.
                             ---- tmp.
                             ---- tmp.
                             ---- rewrite Nat.max_r by lia. tmp.
                     +++ (* not higher: q++; *)
                         replace (Z.of_nat mx <? Z.of_nat (tget (lvl x)
                                    (extract (nth q lt (Pos 0%nat))))) with false
                           by (symmetry; apply Z.ltb_ge; lia).
                         apply exec_skip. normal. run. ints.
                         apply loopk_next with (Datatypes.S q).
                         *** unfold ltof. lia.
                         *** apply (unmark_inv_next m m2 S N lss x lims lt res q _ mk
                                      mx).
                             ---- assumption.
                             ---- assumption.
                             ---- assumption.
                             ---- assumption.
                             ---- assumption.
                             ---- tmp.
                             ---- tmp.
                             ---- rewrite Nat.max_l by lia. tmp.
        -- (* q = length lt: break; return mx, and res = (mk, mx) *)
           replace (zcmp Clt (Z.of_nat q) (Z.of_nat (length lt))) with false
             by (symmetry; cbn [zcmp]; apply Z.ltb_ge; lia).
           assert (Hend: skipn q lt = []) by (apply skipn_all2; assumption).
           rewrite Hend in Hacc. cbn [unmark_lower] in Hacc. rewrite <- Hacc.
           cbv beta iota. apply exec_break. abrupt. apply loopk_break. normal.
           eapply exec_return.
           ++ ev.
           ++ exists (vint (Z.of_nat mx)). split.
              ** apply result_int.
              ** split.
                 --- assumption.
                 --- split.
                     +++ reflexivity.
                     +++ assumption.
    + (* The invariant holds at q = 0, with the marks of x and mx = 0. *)
      constructor.
      * tmp.
      * tmp.
      * lia.
      * exists (mrk x), 0%nat. split.
        -- tmp.
        -- split.
           ++ lia.
           ++ split.
              ** symmetry. assumption.
              ** destruct x. apply HRep.
      * apply Mem.unchanged_on_refl.
Qed.

Lemma unmark_lower_fun: exists (b: block),
  Genv.find_symbol ge _unmark_lower = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_unmark_lower).
Proof. apply find_fun. reflexivity. Qed.
