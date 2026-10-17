# The C solver

`solver.c` implements the step on the context of `refinement/core/SolverStep.v` (`cstep`) in C,
function by function (each comment names its model function): two watched literals, kept as the first two
literals of each clause, with blocker literals in the watch lists (as in MiniSat), values kept per literal (so
reading one is a single load), decisions by cursor and phase, and on a conflict MiniSat's counting analysis and
a backjump that asserts the literal it gives, with the analysed clause kept as its reason on a stack (no clause
is learnt; a full stack asserts it without a reason, and a failed analysis flips the last decision). It
allocates nothing and calls no library. `main.c` (not
verified) reads DIMACS, removes duplicate literals within a clause, lays out the watch lists, chooses the order of
decisions, allocates the tables (with room for the reason clauses, `rcap`) and prints SAT with a model, UNSAT, or UNKNOWN when the solver ran out of room.
The order of decisions puts first the literals whose atom occurs most often (a static two-sided occurrence count,
as in DLCS or two-sided Jeroslow-Wang); `init` checks that it holds each literal of the clauses once, so the
heuristic is not part of what is verified.

- Run: `dune exec rocqsat < problem.cnf` from the repository root (dune compiles it with CompCert, see `dune`).
- Compile by hand: `ccomp -O main.c solver.c -o rocqsat` in this directory.

It is proved correct in [`refinement/c/`](../refinement/README.md#c-proofs-c): `solver_correct`.
