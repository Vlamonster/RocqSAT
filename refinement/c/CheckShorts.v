(* check_shorts checks the clauses with fewer than two literals (check_shorts_t), or
   gives up. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Propagate CStep.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep LitValue Assign Visit.
Import ListNotations.

(* The parts of check_shorts proved in lemmas of their own: its loop, and the body of the
   loop after its test. *)
Definition shorts_loop: statement := first_stmt (drop_stmts 1 (fn_body f_check_shorts)).
Definition shorts_body: statement := drop_stmts 1 (loop_body shorts_loop).

(* The invariant of the loop of check_shorts at q, for the result res of the model: the
   temporaries hold s and q, the memory represents a context xc with the short clauses of
   x, and res is what check_shorts_t gives on the short clauses still to check (the last
   q, which C reads from the end of its array). *)
Record ShortsInv (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx) (lims: list nat)
  (res: Ctx * option nat) (xc: Ctx) (q: nat) (le: temp_env) (m1: mem): Prop := {
  hi_s: le ! _s = Some (sptr S);
  hi_q: le ! _q = Some (vint (Z.of_nat q));
  hi_le: (q <= length (shorts x))%nat;
  hi_rep: Rep m1 S N lss xc lims;
  hi_shorts: shorts xc = shorts x;
  hi_res: res = check_shorts_t (skipn (length (shorts x) - q) (shorts x)) xc;
}.

(* What the loop of check_shorts ends in: no conflict, a conflict (return 1), or out of
   room (return -1); res is the result of the model. *)
Definition ShortsPost (S: Shape) (N: nat) (lss: list (list Lit)) (lims: list nat)
  (res: Ctx * option nat) (le: temp_env) (m: mem) (out: outcome): Prop :=
  (out = Out_normal /\ snd res = None /\ Rep m S N lss (fst res) lims) \/
  (out = Out_return (Some (vint 1, Ctypesdefs.tint)) /\ enc_conf (snd res) = 1 /\
   Rep m S N lss (fst res) lims) \/
  out = Out_return (Some (vint (-1), Ctypesdefs.tint)).

(* The variant and the invariant of the loop. *)
Definition shorts_variant: nat -> nat -> Prop := ltof nat (fun (q: nat) => q).
Definition shorts_inv (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (res: Ctx * option nat) (q: nat) (le: temp_env) (m1: mem): Prop :=
  exists (xc: Ctx), ShortsInv S N lss x lims res xc q le m1.

(* One pass of the loop, for the short clause i at position q - 1:

     {{ ShortsInv xc q /\ q > 0 }}
       int i = s->shorts[q - 1];
       int b = s->cstart[i];
       if (b == s->cstart[i + 1]) return 1;
     {{ result = 1: clause i is empty, a conflict }}
       int a = s->clits[b];
       int v = lit_value(s, a);
       if (v == -1) return 1;
     {{ result = 1: the first literal a of clause i is false, a conflict }}
     {{ ShortsInv xc q /\ a is true or unassigned }}
       if (v == 0) { if (!assign(s, a)) return -1; }
     {{ result = -1 (out of room) }}
     {{ ShortsInv xc' q, with xc' = xc if a is true and assign xc a (i + 1) otherwise }}
       q--;
     {{ ShortsInv xc' (q - 1) }}                                                       *)
Lemma shorts_body_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (res: Ctx * option nat) (xc: Ctx) (q: nat) (le: temp_env) (m1: mem),
  ShortsInv S N lss x lims res xc (Datatypes.S q) le m1 ->
  Exec ge le m1 shorts_body
    (LoopK shorts_variant (shorts_inv S N lss x lims res) (ShortsPost S N lss lims res)
       (Datatypes.S q)).
Proof.
  intros S N lss x lims res xc q le m1 HI.
  destruct HI as [Hs Hq Hqle [HRepc [tp [Apool Hpool]]] Hsh Hcheck].
  pose proof (r_n _ _ _ _ _ _ HRepc) as HN.
  pose proof HRepc as HRepc'. destruct HRepc'. destruct a_shorts as (tsh & Ash & Htsh).
  destruct a_lits as (tl & Alits & Hlits). unpack. rewrite Hsh in *.
  unfold shorts_body, shorts_loop, f_check_shorts.
  cbn [fn_body drop_stmts first_stmt loop_body Swhile].
  (* The short clause i at position q - 1 from the end: the next one of the model. *)
  assert (Hsub: Int.sub (Int.repr (Z.of_nat (Datatypes.S q))) (Int.repr 1)
                = Int.repr (Z.of_nat q)).
  { rewrite sub_repr. f_equal. lia. }
  assert (Hpos: (length (shorts x) - Datatypes.S q < length (shorts x))%nat) by lia.
  rewrite (skipn_nth _ 0%nat _ Hpos) in Hcheck.
  assert (Hi_in: In (nth (length (shorts x) - Datatypes.S q) (shorts x) 0%nat)
                    (shorts x)).
  { now apply nth_In. }
  assert (Hi_nth: nth q (rev (shorts x)) 0%nat
                  = nth (length (shorts x) - Datatypes.S q) (shorts x) 0%nat).
  { apply rev_nth. lia. }
  (* int i = s->shorts[q - 1]; *)
  run. rewrite (Htsh q), Hi_nth by lia.
  remember (nth (length (shorts x) - Datatypes.S q) (shorts x) 0%nat) as i eqn:Hi.
  pose proof (r_shorts_cls i Hi_in) as Hi_lt.
  pose proof (r_starts i Hi_lt) as Hrange.
  assert (Hadd: Int.add (Int.repr (Z.of_nat i)) (Int.repr 1)
                = Int.repr (Z.of_nat (Datatypes.S i))).
  { rewrite add_repr. f_equal. lia. }
  cbn [check_shorts_t] in Hcheck. rewrite (proj2 Hlits i Hi_lt) in Hcheck.
  (* int b = s->cstart[i]; if (b == s->cstart[i + 1]) return 1; *)
  run. eapply (exec_if_cmp _ _ _ Ceq).
  - ev.
  - ev.
  - reflexivity.
  - reflexivity.
  - unfold Small. lia.
  - unfold Small. lia.
  - destruct (Nat.eq_dec (starts S i) (starts S (Datatypes.S i))) as [Heq | Hne].
    + (* clause i is empty: a conflict, return 1; *)
      rewrite Heq, Nat.sub_diag in Hcheck. cbn [seq map] in Hcheck. rewrite Heq.
      replace (zcmp Ceq (Z.of_nat (starts S (Datatypes.S i)))
                 (Z.of_nat (starts S (Datatypes.S i))))
        with true by (symmetry; cbn [zcmp]; apply Z.eqb_refl).
      cbv beta iota. eapply exec_return.
      * ev.
      * ret. right. left. split.
        -- reflexivity.
        -- rewrite Hcheck. cbn [fst snd enc_conf]. split.
           ++ reflexivity.
           ++ split.
              ** assumption.
              ** exists tp. split; assumption.
    + (* clause i has a first literal a: int a = s->clits[b]; int v = lit_value(s, a); *)
      replace (zcmp Ceq (Z.of_nat (starts S i)) (Z.of_nat (starts S (Datatypes.S i))))
        with false by (symmetry; cbn [zcmp]; apply Z.eqb_neq; lia).
      replace (starts S (Datatypes.S i) - starts S i)%nat
        with (Datatypes.S (starts S (Datatypes.S i) - Datatypes.S (starts S i)))
        in Hcheck by lia.
      cbn [seq map] in Hcheck.
      (* its first literal a, whose key is at b *)
      destruct (proj1 Hlits (starts S i)) as [a [Hta Ha]].
      { lia. }
      rewrite Hta, lit_of_key in Hcheck.
      pose proof (key_small _ N Ha HN) as Hka.
      cbv beta iota. run. rewrite Hta. call lit_value_fun. eapply call_weaken.
      { apply (lit_value_correct S N lss xc lims a m1). split; assumption. }
      intros m2 v [-> ->]. normal. run.
      (* if (v == -1) return 1; *)
      eapply (exec_if_cmp _ _ _ Ceq _ _ _ (-1)).
      * ev.
      * ev.
      * reflexivity.
      * reflexivity.
      * apply enc_small.
      * unfold Small. lia.
      * destruct (Z.eqb_spec (enc_value (lookup (vals xc) a)) (-1))
          as [Hfalse | Hnotfalse].
        -- (* a is false: a conflict, return 1; *)
           assert (Hl: lookup (vals xc) a = Some false).
           { destruct (lookup (vals xc) a) as [[|]|].
             - discriminate.
             - reflexivity.
             - discriminate. }
           rewrite Hl in Hcheck.
           replace (zcmp Ceq (enc_value (lookup (vals xc) a)) (-1)) with true
             by (symmetry; cbn [zcmp]; apply Z.eqb_eq; assumption).
           cbv beta iota. eapply exec_return.
           ++ ev.
           ++ ret. right. left. split.
              ** reflexivity.
              ** rewrite Hcheck. cbn [fst snd enc_conf]. split.
                 --- reflexivity.
                 --- split.
                     +++ assumption.
                     +++ exists tp. split; assumption.
        -- (* a is true or unassigned *)
           replace (zcmp Ceq (enc_value (lookup (vals xc) a)) (-1)) with false
             by (symmetry; cbn [zcmp]; apply Z.eqb_neq; assumption).
           cbv beta iota. run.
           (* if (v == 0) { if (!assign(s, a)) return -1; } ends with a context xc' that
              the model goes on from, or returns -1. *)
           apply exec_weaken with (Q := fun (le': temp_env) (m3: mem) (out: outcome) =>
             (out = Out_normal /\ le' ! _s = Some (sptr S) /\
              le' ! _q = Some (vint (Z.of_nat (Datatypes.S q))) /\ exists (xc': Ctx),
                Rep m3 S N lss xc' lims /\ shorts xc' = shorts x /\
                res = check_shorts_t (skipn (length (shorts x) - q) (shorts x)) xc') \/
             out = Out_return (Some (vint (-1), Ctypesdefs.tint))).
           ++ eapply (exec_if_cmp _ _ _ Ceq _ _ _ 0).
              ** ev.
              ** ev.
              ** reflexivity.
              ** reflexivity.
              ** apply enc_small.
              ** unfold Small. lia.
              ** assert (Hnext: (Datatypes.S (length (shorts x) - Datatypes.S q)
                                 = length (shorts x) - q)%nat) by lia.
                 destruct (lookup (vals xc) a) as [[|]|] eqn:Hl.
                 --- (* a is true: nothing to do *)
                     change (zcmp Ceq (enc_value (Some true)) 0) with false.
                     cbv beta iota.
                     apply exec_skip. left. split.
                     +++ reflexivity.
                     +++ split.
                         *** tmp.
                         *** split.
                             ---- tmp.
                             ---- exists xc. split.
                                  ++++ split.
                                       **** assumption.
                                       **** exists tp. split; assumption.
                                  ++++ split.
                                       **** assumption.
                                       **** rewrite Hcheck, Hnext. reflexivity.
                 --- exfalso. apply Hnotfalse. reflexivity.
                 --- (* a is unassigned: assign it, with reason i + 1 *)
                     change (zcmp Ceq (enc_value None) 0) with true. cbv beta iota. run.
                     call assign_fun. eapply call_weaken.
                     { apply (assign_correct S N lss xc lims a (Datatypes.S i) tp m1).
                       split.
                       - assumption.
                       - split.
                         + assumption.
                         + assumption. }
                     intros m3 v Hv. normal.
                     destruct Hv as [-> | (-> & HRep3 & Apool3)].
                     +++ (* out of room: return -1; *)
                         eapply (exec_if_int _ _ _ _ 1).
                         *** ev.
                         *** reflexivity.
                         *** unfold Small. lia.
                         *** change (negb (Z.eqb 1 0)) with true. cbv beta iota.
                             eapply exec_return.
                             ---- ev.
                             ---- right. reflexivity.
                     +++ eapply (exec_if_int _ _ _ _ 0).
                         *** ev.
                         *** reflexivity.
                         *** unfold Small. lia.
                         *** change (negb (Z.eqb 0 0)) with false. cbv beta iota.
                             apply exec_skip. left. split.
                             ---- reflexivity.
                             ---- split.
                                  ++++ tmp.
                                  ++++ split.
                                       **** tmp.
                                       **** exists (assign xc a (Datatypes.S i)). split.
                                            ----- split.
                                                  +++++ assumption.
                                                  +++++ exists tp. split; assumption.
                                            ----- split.
                                                  +++++ assumption.
                                                  +++++ rewrite Hcheck, Hnext.
                                                        reflexivity.
           ++ intros le3 m3 out [(-> & Hs3 & Hq3 & xc' & HRep3 & Hsh3 & Hres3) | ->].
              ** (* q--; and the loop goes on *)
                 normal. run. ints. apply loopk_next with q.
                 --- unfold shorts_variant, ltof. lia.
                 --- exists xc'. constructor.
                     +++ tmp.
                     +++ tmp.
                     +++ lia.
                     +++ assumption.
                     +++ assumption.
                     +++ assumption.
              ** (* out of room *)
                 ret. right. right. reflexivity.
Qed.

(* The loop of check_shorts:

     {{ ShortsInv x (length (shorts x)) }}
       while (q > 0) { ... }                                    (shorts_body_correct)
     {{ ShortsInv xc 0 }} ->>
     {{ res = (xc, None): no conflict }}

   The loop ends: q decreases. *)
Lemma shorts_loop_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (res: Ctx * option nat) (le: temp_env) (m: mem),
  shorts_inv S N lss x lims res (length (shorts x)) le m ->
  Exec ge le m shorts_loop (ShortsPost S N lss lims res).
Proof.
  intros S N lss x lims res le m HI0.
  unfold shorts_loop, f_check_shorts. cbn [fn_body drop_stmts first_stmt]. unfold Swhile.
  apply exec_loop with (R := shorts_variant) (I := shorts_inv S N lss x lims res)
    (a := length (shorts x)).
  - apply well_founded_ltof.
  - intros q le1 m1 [xc HI]. pose proof HI as HI'.
    destruct HI' as [Hs Hq Hqle [HRepc Hpool] Hsh Hcheck].
    pose proof (r_shorts_le _ _ _ _ _ _ HRepc) as Hshle.
    pose proof (r_lss_small _ _ _ _ _ _ HRepc) as Hlss.
    rewrite Hsh in Hshle. apply exec_seq.
    (* if (q > 0) ... else break; *)
    eapply (exec_if_cmp _ _ _ Cgt _ _ _ 0).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + unfold Small. lia.
    + unfold Small. lia.
    + destruct q as [|q].
      * (* q = 0: break; every short clause is checked, without conflict *)
        change (zcmp Cgt (Z.of_nat 0) 0) with false. cbv beta iota.
        apply exec_break. abrupt. apply loopk_break. left. split.
        -- reflexivity.
        -- rewrite Nat.sub_0_r, skipn_all in Hcheck. rewrite Hcheck.
           cbn [check_shorts_t fst snd]. split.
           ++ reflexivity.
           ++ split; assumption.
      * (* q > 0: the body *)
        replace (zcmp Cgt (Z.of_nat (Datatypes.S q)) 0) with true
          by (symmetry; cbn [zcmp]; apply Z.ltb_lt; lia).
        cbv beta iota. apply exec_skip. normal.
        apply (shorts_body_correct S N lss x lims res xc q le1 m1). assumption.
  - assumption.
Qed.

(* check_shorts checks the short clauses from the last one, as check_shorts_t does from
   the first one of its list (they are kept in reverse):

     {{ Rep m S N lss x lims }}
       int q = s->nshorts;
     {{ ShortsInv x (length (shorts x)) }}
       while (q > 0) { ... }                                    (shorts_loop_correct)
     {{ the outcome of the model, or -1 }}
       return 0;                                                                  *)
Lemma check_shorts_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat),
  {{ m | Rep m S N lss x lims }}
    f_check_shorts(sptr S)
  {{ m', v | v = vint (-1) \/
             (v = vint (enc_conf (snd (check_shorts_t (shorts x) x))) /\
              Rep m' S N lss (fst (check_shorts_t (shorts x) x)) lims) }}.
Proof.
  intros S N lss x lims m HRep.
  remember (check_shorts_t (shorts x) x) as res eqn:Hres.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_check_shorts. cbn [fn_body fn_return].
    pose proof (r_nshorts _ _ _ _ _ _ (proj1 HRep)) as Fns.
    (* int q = s->nshorts; *)
    run. clear Fns.
    apply exec_weaken with (Q := ShortsPost S N lss lims res).
    + apply (shorts_loop_correct S N lss x lims res).
      exists x. constructor.
      * tmp.
      * tmp.
      * lia.
      * assumption.
      * reflexivity.
      * rewrite Nat.sub_diag. assumption.
    + intros le' m' out [(-> & Hnone & HRep') | [(-> & Hconf & HRep') | ->]].
      * (* no conflict: return 0; *)
        normal. eapply exec_return.
        -- ev.
        -- exists (vint 0). split.
           ++ apply result_int.
           ++ right. split.
              ** rewrite Hnone. reflexivity.
              ** assumption.
      * (* a conflict: return 1 *)
        abrupt. exists (vint 1). split.
        -- apply result_int.
        -- right. split.
           ++ rewrite Hconf. reflexivity.
           ++ assumption.
      * (* out of room: return -1 *)
        abrupt. exists (vint (-1)). split.
        -- apply result_int.
        -- now left.
Qed.

Lemma check_shorts_fun: exists (b: block),
  Genv.find_symbol ge _check_shorts = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_check_shorts).
Proof. apply find_fun. reflexivity. Qed.
