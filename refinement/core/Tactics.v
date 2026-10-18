(* Tactics shared by the proofs of the refinement. *)

(* Split a conjunction A /\ (B /\ (... /\ Z)) into one goal per conjunct, A to Z. *)
Ltac splits := lazymatch goal with
  | |- _ /\ _ => split; [ | splits]
  | |- _ => idtac
  end.
