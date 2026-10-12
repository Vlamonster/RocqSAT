# The C solver

`solver.c` implements the initial context (`init`) and the step (`step`, `solve`) of
`verification/refinement/CStep.v` in C, function by function (each comment names its model function). It
allocates nothing and calls no library: `main.c` (not verified) reads DIMACS, allocates the tables and prints the
answer. Where a table could run out of room, which the invariants of the model rule out but the proofs do not
show, it gives up (`UNKNOWN`), so the intended theorem is: an answer of SAT or UNSAT is correct.

- Run through the runner: `dune exec rocqsat -- --c < problem.cnf` (compiled by dune with gcc).
- Compile with CompCert: `ccomp -O -DSTANDALONE c/main.c c/solver.c -o rocqsat-c`.

## Verification (work in progress)

`verif/build.sh` generates the Clight of `solver.c` with `clightgen` and checks `verif/Spec.v` against the dune
build (needs `coq-vst` 2.17 and `coq-compcert` 3.18, so it is not part of `dune build` or CI; run `dune build`
first).

- Done: `CStep.v` (`cstep_spec`: the table-only step agrees with `step`); `Spec.v` defines the encodings, the
  facts the C code needs (`Shape`), the representation predicate `solver_rep` and the specs of `assign` and
  `solve`; the lemmas for updating a table entry and decoding a literal key are proved.
- To do (`Admitted` in `Spec.v`): a spec and `semax_body` for every function of `solver.c`, each saying that it
  computes its model function on the represented context (`visit` ~ `visit_t`, `resolve` ~ `resolve_t`, ...,
  `step` ~ `cstep`), or gives up; a model for `init` (deduplicated input clauses, `initial_of`, formula of the
  input) and its spec; `body_solve` from the loop invariant `StepInv`, `LimsOf` and reachability, with
  `cstep_spec`, `step_strategy` and `DPLL_BJ.final_*`.
- Trust left: the Rocq kernel, VST's classical axioms, CompCert's parser and assembler, and `main.c`. VST proves
  partial correctness only; termination holds for the model (`step_strategy`).
