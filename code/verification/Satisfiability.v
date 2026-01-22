From Equations Require Import Equations.
From Stdlib Require Import List.
Import ListNotations.
From RocqSAT Require Import Lit Neg Clause CNF Evaluation WellFormed Trans Solve Strategy Normalization.

Definition Total (m: PA) (f: CNF): Prop := forall (l: Lit) (c: Clause), In l c -> In c f -> Def m l.
Definition Model (m: PA) (f: CNF): Prop := f_eval m f = Some true.

Definition Sat (f: CNF): Prop := exists (m: PA), Model m f.
Definition Unsat (f: CNF): Prop := ~ Sat f.

Definition Entails (f f': CNF): Prop := forall (m: PA), Model m f -> Model m f'.
Definition Equivalent (f f': CNF): Prop := Entails f f' /\ Entails f' f.

Theorem final_exists: forall (f: CNF),
  exists (s: State), state [] f (initial_wf f) ==>* s /\ Final s.
Proof.
  intros. destruct (solve f) as [|m' f' Hwf'] eqn:H.
  - exists fail. split.
    + now apply solve_aux_trans in H.
    + now apply solve_aux_final in H.
  - exists (state m' f' Hwf'). split.
    + now apply solve_aux_trans in H.
    + now apply solve_aux_final in H.
Qed.

Lemma final_model: forall (m: PA) (f: CNF) (Hwf: WellFormed m f),
  Final (state m f Hwf) -> Model m f.
Proof.
  unfold Model. unfold Final. unfold not. intros. destruct (f_eval m f) eqn:Heq.
  - destruct b.
    + reflexivity.
    + exfalso. apply H. apply f_eval_false_iff in Heq as [c [Hc_in_f Hconflict]].
      destruct (proj2 (find_conflict_exists_iff m f)) as [c_conflict Hfind_conflict]. now exists c.
      destruct (split_last_decision m) as [[m_split l_split]|] eqn:Hsplit.
      (* t_backtrack *)
      * exists (state (m_split ++p ¬l_split) f (wf_backtrack m m_split f l_split Hsplit Hwf)).
        pose proof (split_decomp m m_split l_split Hsplit) as [n_split [-> Hno_dec]].
        apply (t_backtrack m_split n_split f c_conflict l_split Hwf).
        -- now apply find_conflict_c_in_f in Hfind_conflict.
        -- now apply find_conflict_conflicting in Hfind_conflict.
        -- assumption.
      (* t_fail *)
      * exists fail. apply (t_fail m f c_conflict).
        -- now apply find_conflict_c_in_f in Hfind_conflict.
        -- now apply find_conflict_conflicting in Hfind_conflict.
        -- now apply split_none_iff.
  (* t_decide *)
  - exfalso. apply H. apply undef_decision_exists in Heq as [l_decide Hfind_dec].
    exists (state (m ++d l_decide) f (wf_decide _ _ _ Hfind_dec Hwf)).
    pose proof (find_decision_decomp m f l_decide Hfind_dec) as [c_decide [Hfind_undef_l Hc_in_f]].
    eapply (t_decide m f c_decide l_decide).
    + left. now apply find_undef_l_in_c in Hfind_undef_l.
    + assumption.
    + now apply find_undef_l_undef in Hfind_undef_l.
Qed.

Theorem final_sat_refl: forall (f: CNF),
  (exists (m: PA) (Hwf: WellFormed m f),
    state [] f (initial_wf f) ==>* state m f Hwf /\ Final (state m f Hwf)) <-> Sat f.
Proof.
  intros. split.
  - intros [m [Hwf [Htrans Hfinal]]]. exists m. now apply final_model in Hfinal.
  - intros Hsat. unfold Sat in Hsat. unfold Model in Hsat. destruct Hsat as [m Heq].
    remember (normalize m f) as m' eqn:H.
    pose proof (normalize_wf m f) as Hwf.
    pose proof (normalize_bounded m f) as Hbounded.
    pose proof (normalize_only_dec m f) as Honly_dec.
    pose proof (normalize_all_def m f) as Hall_def.
    apply normalize_f in Heq.
    rewrite <- H in *. clear H. clear m.
    exists m', Hwf. split.
    + admit.
    + unfold Final. unfold not. intros [s Htrans]. inversion Htrans as 
    [
      m f' c_conflict Hwf' Hc_in_f Hconflict Hno_dec |
      m f' c_unit l_unit ? Hwf' Hl_in_c Hc_in_f Hconflict Hundef |
      m f' c_decide l_decide ? Hwf' Hx_in_c Hc_in_f Hundef |
      m_split n_split f' c_conflict l_split ? Hwf' Hc_in_f Hconflict Hno_dec
    ]; subst s; try subst m; try subst f'.
      (* t_fail *)
      * assert (f_eval m' f = Some false).
        -- apply f_eval_false_iff. now exists c_conflict.
        -- congruence.
      (* t_unit *)
      * admit.
      (* t_decide *)
      * admit.
      (* t_backtrack *)
      * admit.
Admitted.

Theorem final_unsat_refl: forall (f: CNF),
  state [] f (initial_wf f) ==>* fail /\ Final fail <-> Unsat f.
Admitted.

Theorem sat_decidable: forall (f: CNF), Sat f \/ Unsat f.
Proof.
  intros. destruct (final_exists f) as [[|m f' Hwf] ].
  - right. now apply final_unsat_refl.
  - left. destruct H. assert (f = f').
    + now apply (trans_clos_same_formula [] m f f' (initial_wf f) Hwf).
    + subst f'. apply final_sat_refl. now exists m, Hwf.
Qed.
