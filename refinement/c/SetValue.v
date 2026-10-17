(* set_value sets the value of an atom, for both its literals (the tset of the values in
   assign and jump). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Propagate.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep.
Import ListNotations.

(* set_value stores the value o of atom a at the entries of its two literals, 2a and
   2a + 1. Only the values change:

     {{ RepL m S N lss x lims lt /\ a < N }}
       s->vals[2 * a] = v;
       s->vals[2 * a + 1] = -v;                                         (rep_store_vals)
     {{ RepL (set_vals x (tset (vals x) a o)) lt /\ only the values changed }}       *)
Lemma set_value_correct {lt: list Lit}: forall (S: Shape) (N: nat) (lss: list (list Lit))
  (x: Ctx) (lims: list nat) (a: nat) (o: option bool),
  {{ m | RepL m S N lss x lims lt /\ (a < N)%nat }}
    f_set_value(sptr S, vint (Z.of_nat a), vint (enc_value o))
  {{ m', v | RepL m' S N lss (set_vals x (tset (vals x) a o)) lims lt /\
             Mem.unchanged_on (fun (b: block) (_: Z) => b <> b_vals S) m m' }}.
Proof.
  intros S N lss x lims a o m [HRep Ha].
  pose proof (r_n _ _ _ _ _ _ _ HRep) as HN.
  pose proof (r_vals _ _ _ _ _ _ _ HRep) as Fvals.
  pose proof (a_vals _ _ _ _ _ _ _ HRep) as Avals.
  (* The entries of the two literals of a, as C computes them. *)
  assert (Hpos: Int.mul (Int.repr 2) (Int.repr (Z.of_nat a))
                = Int.repr (Z.of_nat (2 * a))).
  { rewrite mul_repr. f_equal. lia. }
  assert (Hneg: Int.add (Int.repr (Z.of_nat (2 * a))) (Int.repr 1)
                = Int.repr (Z.of_nat (2 * a + 1))).
  { rewrite add_repr. f_equal. lia. }
  assert (Hv: Int.neg (Int.repr (enc_value o)) = Int.repr (- enc_value o)).
  { apply Int.neg_repr. }
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_set_value. cbn [fn_body fn_return].
    (* s->vals[2 * a] = v; *)
    run. eapply exec_store.
    + evl.
    + ev.
    + reflexivity.
    + reflexivity.
    + ofs. bound.
    + ofs. cbn [cast_int_int].
      destruct (arr_storable m (b_vals S) (2 * N) (2 * a) _ (enc_value o) Avals
                  ltac:(lia)) as [m1 Hst1].
      exists m1. split.
      * apply Hst1.
      * normal.
        pose proof (arr_store _ _ _ _ (2 * a) _ _ Avals ltac:(lia) Hst1) as Avals1.
        pose proof (r_nodup _ _ _ _ _ _ _ HRep) as Hnd.
        assert (Fvals1: Fld m1 (b_s S) 24 Mptr (Vptr (b_vals S) Ptrofs.zero)).
        { apply (fld_store_other _ _ _ _ _ _ _ _ _ _ Fvals Hst1). left. neq Hnd. }
        clear Fvals Avals.
        (* s->vals[2 * a + 1] = -v; *)
        run. eapply exec_store.
        -- evl.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- ofs. bound.
        -- ofs. cbn [cast_int_int].
           destruct (arr_storable m1 (b_vals S) (2 * N) (2 * a + 1) _ (- enc_value o)
                       Avals1 ltac:(lia)) as [m2 Hst2].
           exists m2. split.
           ++ apply Hst2.
           ++ exists Vundef. split.
              ** reflexivity.
              ** split.
                 --- apply (rep_store_vals m m1 m2 S N lss x lims a o HRep Ha Hst1 Hst2).
                 --- (* only the values changed *)
                     apply (store_unchanged _ m m1 m2 Mint32 (b_vals S)
                              (4 * Z.of_nat (2 * a + 1)) (vint (- enc_value o))).
                     +++ apply (store_unchanged _ m m m1 Mint32 (b_vals S)
                                  (4 * Z.of_nat (2 * a)) (vint (enc_value o))).
                         *** apply Mem.unchanged_on_refl.
                         *** apply Hst1.
                         *** intros j Hb. now apply Hb.
                     +++ apply Hst2.
                     +++ intros j Hb. now apply Hb.
Qed.

Lemma set_value_fun: exists (b: block),
  Genv.find_symbol ge _set_value = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_set_value).
Proof. apply find_fun. reflexivity. Qed.
