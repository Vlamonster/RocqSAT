Definition inspect {A: Type} (a: A): {b | a = b} := exist _ a eq_refl.
Notation "x 'eqn' ':' p" := (exist _ x p) (only parsing, at level 20).
