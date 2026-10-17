# RocqSAT refinement

Concrete solver steps on tables, shaped like the arrays of a C solver, proved to be strategies of the abstract
systems of [`../abstraction/`](../abstraction/README.md), and in `c/` the proof that the C solver of
[`../solver/`](../solver/README.md) computes the solver step.

Two libraries, built from the repository root by `dune build` (after `../abstraction/`):

- `core/`: library `RocqSAT.refinement` (`From RocqSAT.refinement Require Import Step.`), the solver steps.
  Needs no CompCert; `dune build refinement/core` checks it alone.
- `c/`: library `RocqSAT.refinement.c`, the proofs about the C solver, on top of `core/`. Needs CompCert
  (`coq-compcert`).

## Structure

Two solver steps share propagation and the invariant between steps. The solver step (`SolverStep.v`) is the
one the C solver computes; the step with conflict analysis (`analysis_step`) is a separate result on top, which
nothing else uses.

```text
  Table, Lookup, Search, Watches     tables, values, clause lists, literal keys and watch lists
              |
          Propagate                  unit propagation with two watched literals (MiniSat)
              |
       +------+------+
       |             |
      Step         CStep             shared parts of a step, on the trail / on the context alone
       |             |
       +------+------+
              |
     +--------+---------+
     |                  |
 SolverStep        Analysis, AnalysisStep, AnalysisCStep
     |                  conflict analysis and backjumping (not used by the C solver)
     c/
 the C solver
```

## Main results

| Theorem                  | File                   | Statement (informally)                                             |
|--------------------------|------------------------|--------------------------------------------------------------------|
| `step_strategy`          | `core/SolverStep.v`    | The solver step is a valid strategy for `DPLL_BJ`.                 |
| `cstep_spec`             | `core/SolverStep.v`    | The solver step on the context alone agrees with `step`.           |
| `solver_correct`         | `c/Solver.v`           | The C solver terminates with a model, with unsat, or out of room.  |
| `analysis_step_strategy` | `core/AnalysisStep.v`  | The step with conflict analysis is a valid strategy for `DPLL_BJ`. |
| `analysis_cstep_spec`    | `core/AnalysisCStep.v` | Its version on the context alone agrees with `analysis_step`.      |

## Axioms and trusted code

- Everything outside `c/` is closed under the global context: no axioms.
- `c/` uses the axioms of CompCert's semantics (see "Trust left" under [C proofs](#c-proofs-c)).

## File index

Files are listed in dependency order; all are in `core/`.

- `Table.v`: `Table A`, tables as functions (`tget`, `tset`, `tmake`).
- `Lookup.v`: `Values` (the value of each atom), `values m`, `lookup` (agrees with `l_eval`); `ValuesOf`,
  `Fresh`, `Incl`; unassigning a level (`unassign_level`) or a segment of the trail (`unassign_segment`).
- `Search.v`: the clause lists of a formula (`clause_lists`, `ClauseOf`, `formula_lits`); `phase` (decide an
  atom with its last value, `phase_cases`).
- `Watches.v`: literal keys (`lit_key`), marks (`Unmarked`), watch lists of watchers (`Watcher`: a clause
  and its blocker; `watching`, `HasWatcher`), `not_false`.
- `Propagate.v`: unit propagation as in MiniSat, on a context `Ctx` of tables and scalars.
  - The trail is a table (`TrailOf`); the watchers of the negations of the trail literals from `qhead` on are
    still to be visited (`Queued`).
  - The watches of a clause are its first two literals, and a watcher carries a blocker, a literal of its
    clause (as in MiniSat). `visit` keeps a watcher whose blocker is true without looking at its clause;
    otherwise it puts the clause in the form `o :: p :: ls` and keeps it if `o` is true, moves the watch to a
    literal of `ls` that is not false (`swap_watch`), propagates `o`, or stops at a false clause. Clauses are
    reordered on the way (`Reordered`), never changed.
  - Invariants: every clause has a watcher in the lists of both its watches (`Listed`), blockers are literals
    of their clauses (`Blocked`), and a false watch has its negation queued or the clause a true literal
    (`WatchQ`); `SavedQ` keeps that at every decision, so a backjump keeps the watches.
  - `visit_spec`, `propagate_spec`, `check_shorts_spec` (the clauses with fewer than two literals).
- `Step.v`: what both steps share.
  - The cursor of decisions (`skip_from` into a table of literals, `CursorT`).
  - `StepCore`, `StepInv` (adds well-formedness and `Entails`): the context agrees with the state between steps.
  - `front_shorts`, `front_prop` (checking the short clauses and propagating), `decide_spec`, `jump`,
    `jump_core` (jumping back), `final_state`, `step_inv_after`.
  - `initial_of(_inv)`: the initial context for any clause lists with the literals of the clauses of `f`
    (`ClauseOf`).
- `CStep.v`: the shared parts on the context alone, as C computes them: the trail is only read through its
  table, with the decision positions `lims` on a stack (`LimsOf`); `visit_t`, `propagate_t`, `check_shorts_t`
  (no trail), `unset_range` (on trail positions); `Agrees`: an outcome on the context agrees with a step.
- `SolverStep.v`: the solver step, which the C solver computes.
  - `step`: check the short clauses and propagate; on a conflict `resolve` (fail without decisions, flip the
    last decision otherwise), and otherwise decide. `step_spec`, `step_none`, giving `step_strategy`.
  - `cstep`: the same on the context alone (`resolve_t`); `cstep_spec`: it `Agrees` with `step`.
- `Analysis.v`: conflict analysis for backjumping.
  - `Entailed`, `entailed_resolve`, `clause_of` (`entailed_consequence`).
  - `analyze`: resolve the conflict clause with reasons until one literal is at the last level, using marks for
    membership (`resolve_marked`); marked literals are in the clause (`MarkedIn`).
  - `plan`: where to jump, checked against the trail in one pass using the marks (`marked_neg`, `plan_spec`).
  - Reasons and levels are hints: soundness never depends on them.
- `AnalysisStep.v`: `analysis_step`: as `step`, but on a conflict `analysis_resolve` analyses it and
  backjumps; `analysis_resolve_spec`, `analysis_step_spec`, `analysis_step_none`, giving
  `analysis_step_strategy`; `initial_ctx(_inv)` from a formula.
- `AnalysisCStep.v`: `analysis_cstep`, the same on the context alone (`analyze_t`, `plan_t`,
  `analysis_resolve_t`); `analysis_cstep_spec`: `analysis_cstep` `Agrees` with `analysis_step`.

### C proofs (`c/`)

The proofs use our own program logic over CompCert's big-step semantics of Clight, for total correctness:
every rule is a lemma about the semantics itself. `dune build` generates the Clight of
`../solver/solver.c` with `clightgen` (`c/dune`, as `RocqSAT.refinement.c.solver`) and checks the proofs, in
about a minute and a half.

`solver_correct` (`c/Solver.v`): from memory holding the clauses of a formula `f` for `N` atoms,
`init` terminates and either rejects the input (0), or sets up the solver so that `solve` then terminates and
returns 1 with an assignment `pm` on the trail such that `Model pm f` (`TrailIn` in `c/Rep.v`), 0 if
`f` is unsatisfiable, or 2 if it ran out of room. It is stated as one triple for the two calls the driver
makes, `{{ m | IRep ... }} init(s); solve(s) {{ m', r | ... }}` (`Triple2` in `c/Logic.v`), where the answer `r`
is `Rejected` or the int `solve` returned (`Returned z`). The hypotheses describe the input: the clause layout in
`cstart`/`clits`, the watch-list layout in `woff`/`wcap` and the order of decisions in `alls`/`nlits` (both
only checked by `init`, so a bad layout or order makes it reject the input or give up), the sizes (`N < 2^28`,
fewer than `2^30` literals, clauses and pool entries), separate blocks for the tables, and that the clauses are
exactly those of `f`.

- `c/Logic.v`: `Exec le m s Q` (a terminating execution of `s` ends in a state satisfying `Q`), `Call`, and
  rules for sequences, assignments, stores, branches, calls, and loops with a variant in any well-founded
  relation (which gives termination). The continuations of sequences and loops are definitions (`SeqK`,
  `LoopK`), so that goals stay small. Calls are Hoare triples (`Triple`, written
  `{{ m | P }} f(args) {{ m', v | Q }}` in `c/Rep.v`), and `drop_stmts`, `first_stmt`, `loop_body`,
  `then_stmt` and `else_stmt` name the parts of a generated body, so that a loop or a branch is proved in a
  lemma of its own. The comment above each lemma shows its part of the C code as a decorated program.
- `c/Arrays.v`: tables in memory (`Arr`, `Fld`): every table has a block of its own, so a store to one keeps
  the others without separation logic; `Mem.unchanged_on` frames for calls.
- `c/Common.v`: literals as keys, and the tactics that run straight-line code (`run`, `ev`, `ld`, `store`).
- `c/Rep.v`: `RepB`/`Rep`, how the memory of `solver.c` holds a context of `Propagate.v` and the
  positions of its decisions (the values per literal, `key_value`, so that `lit_value` is one load), and the
  store lemmas (`rep_store_*`): what a store of the C code does to the
  represented context.
- One file per function of `../solver/solver.c`, each proving that it computes its model function, or gives up:
  - propagation: `LitValue.v`, `SetValue.v`, `Assign.v`, `Wpush.v`, `FindWatch.v`, `KeepRest.v` (also the
    memory during a visit, `VisitMem`), `Visit.v`, `Propagate.v`, `CheckShorts.v`;
  - the step: `SkipFrom.v`, `Phase.v`, `Cut.v`, `Resolve.v`, `Step.v` (`step` computes `cstep`), `Solve.v`
    (`solve` terminates by `strict_derivation_well_founded` and answers by `step_strategy`);
  - the initial context: `Zero.v`, `CheckClauses.v`, `CheckLits.v`, `CheckRoom.v`, `Index.v`, `Init.v`
    (`init` sets up `initial_of`), and `Solver.v`.
- Trust left: the Rocq kernel, the axioms of CompCert's semantics (excluded middle, functional extensionality,
  two of the classical reals, and the semantics of external calls, which the solver does not make), CompCert's
  parser and assembler, and the driver `../solver/main.c`.
