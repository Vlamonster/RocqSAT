(* phase gives the literal of an atom with the value it last had (phase). *)
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
From RocqSAT.refinement Require Import Search.
From RocqSAT.refinement Require Import Watches.
From RocqSAT.refinement Require Import Propagate.
From RocqSAT.refinement.c Require Import Arrays.
From RocqSAT.refinement.c Require Import Logic.
From RocqSAT.refinement.c Require Import Common.
From RocqSAT.refinement.c Require Import solver.
From RocqSAT.refinement.c Require Import Rep.

(* phase reads the last value of the atom a of l and returns the literal of a with that
   value, or l itself if a never had one. It stores nothing. Writing p for the last
   value, tget (phs x) a:

     {{ RepL m sh N lss x /\ extract l < N }}
       int a = l >> 1;
       int v = s->phs[a];
     {{ a = extract l /\ v = enc_value p }}
       if (v == 1) return 2 * a;
     {{ result = key (Pos a) = key (phase (phs x) l), as p = Some true }}
       if (v == -1) return 2 * a + 1;
     {{ result = key (Neg a) = key (phase (phs x) l), as p = Some false }}
       return l;
     {{ result = key l = key (phase (phs x) l), as p = None }}                      *)
Lemma phase_correct: forall (sh: Shape) (N: nat) (lss: list (list Lit)) (x: Ctx)
  (l: Lit),
  {{ m | RepL m sh N lss x /\ (extract l < N)%nat }}
    f_phase(sptr sh, vint (key l))
  {{ m', v | Reads m m' v (vint (key (phase (phs x) l))) }}.
Proof.
  intros sh N lss x l m [HRep Hl].
  pose proof (key_small l N Hl (r_n HRep)) as Hkey.
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
  - unfold f_phase. cbn [fn_body fn_return]. destruct HRep as [[] [] []].
    (* int a = l >> 1; int v = s->phs[a]; *)
    run.
    (* if (v == 1) *)
    eapply exec_if_eq.
    + ev.
    + ev.
    + reflexivity.
    + split.
      * apply enc_small.
      * lia.
    + (* The last value was true: return 2 * a; *)
      intros Hv. unfold phase. destruct (tget (phs x) (extract l)) as [[|]|].
      * eapply exec_return.
        -- ev.
        -- cbn [cast_int_int]. ints. ret. exists (vint (key (Pos (extract l)))). split.
           ++ apply result_int.
           ++ split; reflexivity.
      * simpl in Hv. lia.
      * simpl in Hv. lia.
    + (* if (v == -1) return 2 * a + 1; *)
      intros Hv. run. eapply exec_if_eq with (z2 := -1).
      * ev.
      * ev.
      * reflexivity.
      * split.
        -- apply enc_small.
        -- lia.
      * (* The last value was false: return 2 * a + 1; *)
        intros Hv'. unfold phase. destruct (tget (phs x) (extract l)) as [[|]|].
        -- simpl in Hv'. lia.
        -- eapply exec_return.
           ++ ev.
           ++ cbn [cast_int_int]. ints. ret.
              exists (vint (key (Neg (extract l)))). split.
              ** apply result_int.
              ** split; reflexivity.
        -- simpl in Hv'. lia.
      * (* No last value: return l; *)
        intros Hv'. run. unfold phase. destruct (tget (phs x) (extract l)) as [[|]|].
        -- simpl in Hv. lia.
        -- simpl in Hv'. lia.
        -- return_int.
           split; reflexivity.
Qed.

Lemma phase_fun: FunAt _phase f_phase.
Proof. apply find_fun. reflexivity. Qed.
