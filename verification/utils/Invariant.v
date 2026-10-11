From Stdlib Require Import Relations.

(* A property that every step of R preserves is preserved by any number of steps. *)
Lemma clos_refl_trans_invariant: forall (A: Type) (R: relation A) (P: A -> Prop),
  (forall (x y: A), R x y -> P x -> P y) ->
  forall (x y: A), clos_refl_trans A R x y -> P x -> P y.
Proof.
  intros A R P Hstep x y H. induction H as [x y Hxy | x | x y z _ IHxy _ IHyz].
  - now apply Hstep.
  - easy.
  - intros Hx. now apply IHyz, IHxy.
Qed.
