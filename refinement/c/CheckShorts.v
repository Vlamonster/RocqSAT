(* check_shorts checks the clauses with fewer than two literals (check_shorts), or
   gives up. *)
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
From RocqSAT.refinement Require Import Tactics.
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
From RocqSAT.refinement.c Require Import LitValue.
From RocqSAT.refinement.c Require Import Assign.
From RocqSAT.refinement.c Require Import Visit.

(* The parts of check_shorts proved in lemmas of their own: its loop, the body of the
   loop after its test, and in the body the test if (v == 0) that assigns the first
   literal of a short clause. *)
Definition shorts_loop: statement := first_stmt (drop_stmts 1 (fn_body f_check_shorts)).
Definition shorts_body: statement := drop_stmts 1 (loop_body shorts_loop).
Definition shorts_assign: statement := first_stmt (drop_stmts 6 shorts_body).

(* The last q short clauses of x. *)
Abbreviation last_shorts x q := (skipn (length (shorts x) - q) (shorts x)).

Section Loop.
  Variables (sh: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx) (res: Ctx * option nat).

  (* The invariant of the loop of check_shorts at q, for the result res of the model:
     the temporaries hold s and q, the memory represents a context xc with the short
     clauses of x, and res is what check_shorts gives on the last q short clauses (C
     reads them from the end of its array). *)
  Record ShortsInv {xc: Ctx} {q: nat} {le: temp_env} {m1: mem}: Prop := {
    hi_s: le ! _s = Some (sptr sh);
    hi_q: le ! _q = Some (vnat q);
    hi_le: (q <= length (shorts x))%nat;
    hi_rep: Rep m1 sh N lss xc;
    hi_shorts: shorts xc = shorts x;
    hi_res: res = check_shorts (last_shorts x q) xc;
  }.
  Arguments ShortsInv : clear implicits.

  (* The invariant at q: ShortsInv for some context xc. *)
  Definition shorts_inv (q: nat) (le: temp_env) (m1: mem): Prop :=
    exists (xc: Ctx), ShortsInv xc q le m1.

  (* The loop ends: q decreases. *)
  Definition shorts_variant: nat -> nat -> Prop := ltof nat (fun (q: nat) => q).

  (* What the test of v ends in: s and q kept and a context xc' with the short clauses
     of x that the model goes on from, or out of room (return -1). *)
  Definition ShortsAssignPost (q: nat) (le: temp_env) (m: mem) (out: outcome): Prop :=
    (out = Out_normal /\ le ! _s = Some (sptr sh) /\
     le ! _q = Some (vnat (S q)) /\ exists (xc': Ctx),
       Rep m sh N lss xc' /\ shorts xc' = shorts x /\
       res = check_shorts (last_shorts x q) xc') \/
    out = ret_int (-1).

  (* The test of v when the first literal a of clause i is true or unassigned (v is 1 or
     0); res is what the model gives on the short clauses after i:

       {{ Rep m1 xc /\ v = value of a, not false }}
         if (v == 0) {
       {{ a is unassigned }}
           if (!assign(s, a, i + 1)) return -1;
       {{ Rep (assign xc a (input i)) }}
         }
       {{ ShortsAssignPost: xc' = xc if a is true, assign xc a (input i) otherwise }}  *)
  Lemma shorts_assign_correct: forall (xc: Ctx) (q i: nat) (a: Lit) (le: temp_env)
    (m1: mem),
    le ! _s = Some (sptr sh) -> le ! _q = Some (vnat (S q)) ->
    le ! _i = Some (vnat i) -> le ! _a = Some (vint (key a)) ->
    le ! _v = Some (vint (enc_value (lookup (vals xc) a))) ->
    Rep m1 sh N lss xc -> shorts xc = shorts x ->
    (extract a < N)%nat -> (i < length lss)%nat ->
    enc_value (lookup (vals xc) a) <> -1 ->
    res = match lookup (vals xc) a with
          | Some true  => check_shorts (last_shorts x q) xc
          | Some false => (xc, Some i)
          | None       => check_shorts (last_shorts x q) (assign xc a (input i))
          end ->
    Exec ge le m1 shorts_assign (ShortsAssignPost q).
  Proof.
    intros xc q i a le m1 Hs Hq Hi_tmp Ha_tmp Hv_tmp HRep Hsh Ha Hi_lt Hnotfalse
      Hcheck.
    pose proof HRep as [HRepc [Hlow [tp [Apool Hpool]]]].
    unfold shorts_assign, shorts_body, shorts_loop, f_check_shorts.
    cbn [fn_body drop_stmts first_stmt loop_body Swhile].
    eapply (exec_if_eq _ 0).
    - ev.
    - ev.
    - reflexivity.
    - split.
      + apply enc_small.
      + lia.
    - (* a is unassigned: assign it, with reason i + 1 *)
      intros Hunassigned.
      assert (Hl: lookup (vals xc) a = None).
      { destruct (lookup (vals xc) a) as [[|]|].
        - discriminate.
        - discriminate.
        - reflexivity. }
      run.
      eapply (exec_call_triple assign_fun
                (assign_correct sh N lss xc a (input i) tp)).
      + reflexivity.
      + cbn [enc_reason]. unfold vint. rewrite <- add_repr. evs.
      + split.
        * assumption.
        * split.
          -- assumption.
          -- split; assumption.
      + intros m3 v Hassign. normal.
        destruct Hassign as [-> | (-> & HRep3 & Apool3)].
        * (* out of room: return -1; *)
          branch 1.
          -- intros Hnonzero. eapply exec_return.
             ++ ev.
             ++ right. reflexivity.
          -- intros Hzero. lia.
        * branch 0.
          -- intros Hnonzero. lia.
          -- intros Hzero. apply exec_skip. left. splits.
             ++ reflexivity.
             ++ tmp.
             ++ tmp.
             ++ exists (assign xc a (input i)). split.
                ** split.
                   --- assumption.
                   --- split.
                       +++ cbn [assign lower]. assumption.
                       +++ exists tp. split; assumption.
                ** split.
                   --- assumption.
                   --- rewrite Hl in Hcheck. assumption.
    - (* a is true: nothing to do *)
      intros Hassigned.
      assert (Hl: lookup (vals xc) a = Some true).
      { destruct (lookup (vals xc) a) as [[|]|].
        - reflexivity.
        - exfalso. apply Hnotfalse. reflexivity.
        - exfalso. apply Hassigned. reflexivity. }
      apply exec_skip. left. splits.
      + reflexivity.
      + tmp.
      + tmp.
      + exists xc. split.
        * assumption.
        * split.
          -- assumption.
          -- rewrite Hl in Hcheck. assumption.
  Qed.

  (* One pass of the loop, for the short clause i at position q - 1:

       {{ ShortsInv xc q /\ q > 0 }}
         int i = s->shorts[q - 1];
         int b = s->cstart[i];
         if (b == s->cstart[i + 1]) return i + 1;
       {{ result = i + 1: clause i is empty, a conflict }}
         int a = s->clits[b];
         int v = lit_value(s, a);
         if (v == -1) return i + 1;
       {{ result = i + 1: the first literal a of clause i is false, a conflict }}
       {{ ShortsInv xc q /\ a is true or unassigned }}
         if (v == 0) { if (!assign(s, a, i + 1)) return -1; }    (shorts_assign_correct)
       {{ result = -1 (out of room) }}
       {{ ShortsInv xc' q, with xc' = xc if a is true and assign xc a (input i)
          otherwise }}
         q--;
       {{ ShortsInv xc' (q - 1) }}                                                    *)
  Lemma shorts_body_correct: forall (xc: Ctx) (q: nat) (le: temp_env) (m1: mem),
    ShortsInv xc (S q) le m1 ->
    Exec ge le m1 shorts_body
      (LoopK shorts_variant shorts_inv (LoopOut sh N lss res) (S q)).
  Proof.
    intros xc q le m1 HI.
    destruct HI as [Hs Hq Hqle HRep Hsh Hcheck].
    pose proof HRep as [HRepc [Hlow [tp [Apool Hpool]]]].
    pose proof (r_n HRepc) as HN.
    pose proof HRepc as HRepc'. destruct HRepc'. destruct a_shorts as (tsh & Ash & Htsh).
    destruct a_lits as (tl & Alits & Hlits). unpack. rewrite Hsh in *.
    unfold shorts_body, shorts_loop, f_check_shorts.
    cbn [fn_body drop_stmts first_stmt loop_body Swhile].
    (* The short clause i at position q - 1 from the end: the next one of the model. *)
    assert (Hsub: Int.sub (Int.repr (Z.of_nat (S q))) (Int.repr 1)
                  = Int.repr (Z.of_nat q)).
    { rewrite sub_repr. f_equal. lia. }
    assert (Hpos: (length (shorts x) - S q < length (shorts x))%nat) by lia.
    rewrite (skipn_nth _ 0%nat _ Hpos) in Hcheck.
    assert (Hi_in: In (nth (length (shorts x) - S q) (shorts x) 0%nat)
                      (shorts x)).
    { now apply nth_In. }
    assert (Hi_nth: nth q (rev (shorts x)) 0%nat
                    = nth (length (shorts x) - S q) (shorts x) 0%nat).
    { apply rev_nth. lia. }
    (* int i = s->shorts[q - 1]; *)
    run. rewrite (Htsh q), Hi_nth by lia.
    remember (nth (length (shorts x) - S q) (shorts x) 0%nat) as i eqn:Hi.
    pose proof (r_shorts_cls i Hi_in) as Hi_lt.
    pose proof (r_starts i Hi_lt) as Hrange.
    assert (Hadd: Int.add (Int.repr (Z.of_nat i)) (Int.repr 1)
                  = Int.repr (Z.of_nat (S i))).
    { rewrite add_repr. f_equal. lia. }
    cbn [check_shorts] in Hcheck. rewrite (proj2 Hlits i Hi_lt) in Hcheck.
    (* int b = s->cstart[i]; if (b == s->cstart[i + 1]) return i + 1; *)
    run. branch.
    - (* clause i is empty: a conflict, return i + 1; *)
      intros Hempty.
      assert (Heq: starts sh i = starts sh (S i)) by lia.
      rewrite Heq, Nat.sub_diag in Hcheck. cbn [seq map] in Hcheck.
      eapply exec_return.
      + ev.
      + ret. right. exists (enc_conf (Some i)). split.
        * cbn [cast_int_int]. rewrite enc_conf_some. reflexivity.
        * right. rewrite Hcheck. cbn [fst snd]. splits.
          -- reflexivity.
          -- assumption.
          -- intros i' Hsome. injection Hsome as <-. assumption.
    - (* clause i has a first literal a: int a = s->clits[b]; int v = lit_value(s, a); *)
      intros Hne.
      replace (starts sh (S i) - starts sh i)%nat
        with (S (starts sh (S i) - S (starts sh i)))
        in Hcheck by lia.
      cbn [seq map] in Hcheck.
      (* its first literal a, whose key is at b *)
      destruct (proj1 Hlits (starts sh i)) as [a [Hta Ha]].
      { lia. }
      rewrite Hta, lit_of_key in Hcheck.
      pose proof (key_small _ N Ha HN) as Hka.
      run. rewrite Hta.
      call lit_value_fun (lit_value_correct sh N lss xc a).
      + split; assumption.
      + intros m2 v [-> ->]. normal. run.
        (* if (v == -1) return i + 1; *)
        eapply (exec_if_eq _ (-1)).
        * ev.
        * ev.
        * reflexivity.
        * split.
          -- apply enc_small.
          -- lia.
        * (* a is false: a conflict, return i + 1; *)
          intros Hfalse.
          assert (Hl: lookup (vals xc) a = Some false).
          { destruct (lookup (vals xc) a) as [[|]|].
            - discriminate.
            - reflexivity.
            - discriminate. }
          rewrite Hl in Hcheck.
          eapply exec_return.
          -- ev.
          -- ret. right. exists (enc_conf (Some i)). split.
             ++ cbn [cast_int_int]. rewrite enc_conf_some. reflexivity.
             ++ right. rewrite Hcheck. cbn [fst snd]. splits.
                ** reflexivity.
                ** assumption.
                ** intros i' Hsome. injection Hsome as <-. assumption.
        * (* a is true or unassigned *)
          intros Hnotfalse. run.
          (* if (v == 0) { if (!assign(s, a, i + 1)) return -1; } ends with a context
             xc' that the model goes on from, or returns -1. *)
          apply exec_weaken with (Q := ShortsAssignPost q).
          -- apply (shorts_assign_correct xc q i a).
             ++ tmp.
             ++ tmp.
             ++ tmp.
             ++ tmp.
             ++ tmp.
             ++ assumption.
             ++ assumption.
             ++ assumption.
             ++ assumption.
             ++ assumption.
             ++ assert (Hnext: (S (length (shorts x) - S q)
                                = length (shorts x) - q)%nat) by lia.
                rewrite Hnext in Hcheck. assumption.
          -- intros le3 m3 out [(-> & Hs3 & Hq3 & xc' & HRep3 & Hsh3 & Hres3) | ->].
             ++ (* q--; and the loop goes on *)
                normal. run. ints. apply loopk_next with q.
                ** unfold shorts_variant, ltof. lia.
                ** exists xc'. constructor.
                   --- tmp.
                   --- tmp.
                   --- lia.
                   --- assumption.
                   --- assumption.
                   --- assumption.
             ++ (* out of room *)
                ret. right. exists (-1). split.
                ** reflexivity.
                ** now left.
  Qed.

  (* The loop of check_shorts:

       {{ ShortsInv x (length (shorts x)) }}
         while (q > 0) { ... }                                    (shorts_body_correct)
       {{ ShortsInv xc 0 }} ->>
       {{ res = (xc, None): no conflict }}

     The loop ends: q decreases. *)
  Lemma shorts_loop_correct: forall (le: temp_env) (m: mem),
    shorts_inv (length (shorts x)) le m ->
    Exec ge le m shorts_loop (LoopOut sh N lss res).
  Proof.
    intros le m HI0.
    unfold shorts_loop, f_check_shorts. cbn [fn_body drop_stmts first_stmt].
    unfold Swhile.
    apply exec_loop with (R := shorts_variant) (I := shorts_inv)
      (a := length (shorts x)).
    - apply well_founded_ltof.
    - intros q le1 m1 [xc HI]. pose proof HI as HI'.
      destruct HI' as [Hs Hq Hqle [HRepc Hpool] Hsh Hcheck].
      pose proof (r_shorts_le HRepc) as Hshle.
      pose proof (r_lss_small HRepc) as Hlss.
      rewrite Hsh in Hshle. apply exec_seq.
      (* if (q > 0) ... else break; *)
      branch _ 0.
      + (* q > 0: the body *)
        intros Hpos. destruct q as [|q].
        * lia.
        * apply exec_skip. normal.
          apply (shorts_body_correct xc q le1 m1). assumption.
      + (* q = 0: break; every short clause is checked, without conflict *)
        intros Hzero. assert (Hq_zero: q = 0%nat) by lia. subst q.
        apply exec_break. abrupt. apply loopk_break. left. split.
        * reflexivity.
        * rewrite Nat.sub_0_r, skipn_all in Hcheck. rewrite Hcheck.
          cbn [check_shorts fst snd]. split.
          -- reflexivity.
          -- split; assumption.
    - assumption.
  Qed.

End Loop.

(* check_shorts checks the short clauses from the last one, as check_shorts does from
   the first one of its list (they are kept in reverse):

     {{ Rep m sh N lss x }}
       int q = s->nshorts;
     {{ ShortsInv x (length (shorts x)) }}
       while (q > 0) { ... }                                    (shorts_loop_correct)
       return 0;
     {{ ConfOut (check_shorts (shorts x) x) }}                                   *)
Lemma check_shorts_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx),
  {{ m | Rep m sh N lss x }}
    f_check_shorts(sptr sh)
  {{ m', v | ConfOut sh N lss (check_shorts (shorts x) x) m' v }}.
Proof.
  intros sh N lss x m HRep.
  remember (check_shorts (shorts x) x) as res eqn:Hres.
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_check_shorts. cbn [fn_body fn_return].
    pose proof (r_nshorts (proj1 HRep)) as Fns.
    (* int q = s->nshorts; *)
    run. clear Fns.
    apply exec_weaken with (Q := LoopOut sh N lss res).
    + apply (shorts_loop_correct sh N lss x res).
      exists x. constructor.
      * tmp.
      * tmp.
      * lia.
      * assumption.
      * reflexivity.
      * rewrite Nat.sub_diag. assumption.
    + intros le' m' out [(-> & Hnone & HRep') | (z & -> & Hz)].
      * (* no conflict: return 0; *)
        normal. return_int.
        right. splits.
        -- rewrite Hnone. reflexivity.
        -- assumption.
        -- rewrite Hnone. intros i Heq. discriminate.
      * (* a return: i + 1 on a conflict on clause i, or -1 when out of room *)
        abrupt. exists (vint z). split.
        -- apply result_int.
        -- assumption.
Qed.

Lemma check_shorts_fun: FunAt _check_shorts f_check_shorts.
Proof. apply find_fun. reflexivity. Qed.
