From Stdlib Require Import List.
Import ListNotations.
From RocqSAT Require Import Lit CNF Evaluation WellFormed Trans.

Inductive Entails: CNF -> PA -> Prop :=
| e_intro (f: CNF) (n: PA):
  (forall (m: PA), 
    f_eval m f = Some true -> m_eval m n = Some true) ->
  NoDecisions n ->
  Entails f n
| e_step (f: CNF) (m n: PA) (l: Lit):
  (forall (m': PA), 
    f_eval m' f = Some true /\
    m_eval m' m = Some true /\
    l_eval m' l = Some true -> m_eval m' n = Some true) ->
  NoDecisions n ->
  Entails f m ->
  Entails f (m ++d l ++a n).

Lemma trans_entails: forall (m m': PA) (f: CNF) (Hwf: WellFormed m f) (Hwf': WellFormed m' f),
  state m f Hwf ==> state m' f Hwf' -> Entails f m -> Entails f m'.
Admitted.

Lemma derivation_entails: forall (m m': PA) (f: CNF) (Hwf: WellFormed m f) (Hwf': WellFormed m' f),
  state m f Hwf ==>* state m' f Hwf' -> Entails f m -> Entails f m'.
Admitted.
