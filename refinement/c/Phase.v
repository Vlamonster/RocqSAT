(* phase gives the literal of an atom with the value it last had (phase). *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers Values Memory AST Globalenvs
  Ctypes Cop Clight ClightBigstep.
From RocqSAT Require Import Lit.
From RocqSAT.refinement Require Import Table Lookup Watches Search Propagate.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Logic Arrays Common Rep.
Import ListNotations.

(* phase reads the last value of the atom a of l and returns the literal of a with that
   value, or l itself if a never had one. It stores nothing. Writing p for the last
   value, tget (phs x) a:

     {{ RepB m S N lss x lims /\ extract l < N }}
       int a = l >> 1;
       int v = s->phs[a];
     {{ a = extract l /\ v = enc_value p }}
       if (v == 1) return 2 * a;
     {{ result = key (Pos a) = key (phase (phs x) l), as p = Some true }}
       if (v == -1) return 2 * a + 1;
     {{ result = key (Neg a) = key (phase (phs x) l), as p = Some false }}
       return l;
     {{ result = key l = key (phase (phs x) l), as p = None }}                      *)
Lemma phase_correct: forall (S: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (lims: list nat) (l: Lit),
  {{ m | RepB m S N lss x lims /\ (extract l < N)%nat }}
    f_phase(sptr S, vint (key l))
  {{ m', v | m' = m /\ v = vint (key (phase (phs x) l)) }}.
Proof.
  intros S N lss x lims l m [HRep Hl].
  pose proof (key_small l N Hl (r_n _ _ _ _ _ _ HRep)) as Hkey.
  (* The shift gives the atom a of l; 2 * a and 2 * a + 1 are the keys of its
     literals. *)
  assert (Hshr: Int.shr (Int.repr (key l)) (Int.repr 1)
                = Int.repr (Z.of_nat (extract l))).
  { apply shr_key. lia. }
  assert (Hmul: Int.mul (Int.repr 2) (Int.repr (Z.of_nat (extract l)))
                = Int.repr (key (Pos (extract l)))).
  { rewrite mul_repr. f_equal. unfold key. cbn [lit_key]. lia. }
  assert (Hadd: Int.add (Int.repr (key (Pos (extract l)))) (Int.repr 1)
                = Int.repr (key (Neg (extract l)))).
  { rewrite add_repr. f_equal. unfold key. cbn [lit_key]. lia. }
  eapply call_simple.
  - reflexivity.
  - reflexivity.
  - unfold f_phase. cbn [fn_body fn_return]. destruct HRep.
    (* int a = l >> 1; int v = s->phs[a]; *)
    run.
    (* if (v == 1) *)
    eapply (exec_if_cmp _ _ _ Ceq).
    + ev.
    + ev.
    + reflexivity.
    + reflexivity.
    + apply enc_small.
    + unfold Small. lia.
    + unfold phase. destruct (tget (phs x) (extract l)) as [[|]|] eqn:Hph.
      * (* The last value was true: return 2 * a; *)
        change (zcmp Ceq (enc_value (Some true)) 1) with true. cbv beta iota.
        eapply exec_return.
        -- ev.
        -- cbn [cast_int_int]. ints. ret. exists (vint (key (Pos (extract l)))). split.
           ++ apply result_int.
           ++ split; reflexivity.
      * (* The last value was false: if (v == -1) return 2 * a + 1; *)
        change (zcmp Ceq (enc_value (Some false)) 1) with false. cbv beta iota. run.
        eapply (exec_if_cmp _ _ _ Ceq _ _ _ (-1)).
        -- ev.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- apply enc_small.
        -- unfold Small. lia.
        -- change (zcmp Ceq (enc_value (Some false)) (-1)) with true. cbv beta iota.
           eapply exec_return.
           ++ ev.
           ++ cbn [cast_int_int]. ints. ret.
              exists (vint (key (Neg (extract l)))). split.
              ** apply result_int.
              ** split; reflexivity.
      * (* No last value: neither test holds, return l; *)
        change (zcmp Ceq (enc_value None) 1) with false. cbv beta iota. run.
        eapply (exec_if_cmp _ _ _ Ceq _ _ _ (-1)).
        -- ev.
        -- ev.
        -- reflexivity.
        -- reflexivity.
        -- apply enc_small.
        -- unfold Small. lia.
        -- change (zcmp Ceq (enc_value None) (-1)) with false. cbv beta iota. run.
           eapply exec_return.
           ++ ev.
           ++ exists (vint (key l)). split.
              ** apply result_int.
              ** split; reflexivity.
Qed.

Lemma phase_fun: exists (b: block),
  Genv.find_symbol ge _phase = Some b /\
  Genv.find_funct_ptr ge b = Some (Internal f_phase).
Proof. apply find_fun. reflexivity. Qed.
