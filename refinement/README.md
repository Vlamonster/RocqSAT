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

The solver step (`SolverStep.v`), which the C solver computes, propagates, decides, and on a conflict analyses
it (MiniSat's counting analysis) and backjumps, asserting the literal the analysis gives with the analysed clause
as its reason; reason clauses are kept on a stack, not learnt. Soundness never depends on the analysis: when it
gives nothing, the step flips the last decision. Decisions take the most active atom (VSIDS as in MiniSat, in
fixed point, `Heur.v`): the analysis bumps the atoms it marks. The heuristic is only a hint: a decision checks
that its literal is unassigned and falls back to the cursor, so only bounds on the heuristic are proved.

```text
  Table, Lookup, Search, Watches     tables, values, clause lists, literal keys and watch lists
              |
            Heur                     the decision heuristic: activities and a heap of atoms (VSIDS)
              |
          Propagate                  unit propagation with two watched literals (MiniSat); reasons, levels
              |
          Analysis                   conflict analysis, the stack of reason clauses, jump levels
              |
       +------+------+
       |             |
      Step         CStep             shared parts of a step, on the trail / on the context alone
       |             |
       +------+------+
              |
          SolverStep                 the solver step, with backjumping
              |
             c/                      the C solver
```

## Main results

| Theorem          | File                | Statement (informally)                                                  |
|------------------|---------------------|-------------------------------------------------------------------------|
| `step_strategy`  | `core/SolverStep.v` | The solver step is a valid strategy for `DPLL_BJ`.                      |
| `cstep_spec`     | `core/SolverStep.v` | The solver step on the context alone agrees with `step`.                |
| `analyze_spec`   | `core/Analysis.v`   | The analysis gives an entailed clause asserting a literal, or nothing.  |
| `solver_correct` | `c/Solver.v`        | The C solver terminates with a model, with unsat, or out of room.       |

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
- `Heur.v`: the decision heuristic `Heur` (activities, the bump, a binary heap of atoms with their positions,
  and the literal to decide on of each atom), with integer activities below `act_lim = 2^30`: `bump`,
  `decay` (the bump grows by 1/19), `rescale` (divide all by 2^20), `heap_up`/`heap_down`/`heap_insert`/
  `heap_pop` (with fuel), `pick` (pop until an unassigned literal), `reinsert` (atoms unassigned by a jump),
  `init_heur`. `HeurOk`: the bounds the C code needs; nothing else about the heap is proved.
- `Propagate.v`: unit propagation as in MiniSat, on a context `Ctx` of tables and scalars (with the
  heuristic `hr`).
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
  - Each trail literal has a `Reason` (none, input clause `i`, or reason clause `j`) and a level; `TraceOk`:
    the levels count the decisions up to each literal, and a reason clause justifies its literal
    (`Justifies`, `ReasonOk`). Propagation assigns with the clause as reason.
  - `visit_spec`, `propagate_spec`, `check_shorts_spec` (the clauses with fewer than two literals).
- `Analysis.v`: conflict analysis.
  - `Entailed`: a clause that follows from the formula.
  - `analyze`: MiniSat's counting analysis. From the conflict clause, the literals of the last level are marked
    and counted (`add_lits`, which bumps their atoms), those of lower levels collected in `lt`; walking the trail down (`prev_marked`),
    the newest marked literal is resolved with its reason until one literal of the last level is left, the
    one to assert (`analyze_loop`). Without a reason, or out of room, it gives nothing and unmarks
    (`unmark_range`). `analyze_spec` (with the invariant `AInv`): the clause is entailed and asserts a literal.
  - `unmark_lower` (the highest level among `lt`), `split_levels` (where to jump); the stack of reason clauses
    (`reasons_size`, `add_reason`, `push_reason`, which gives no reason when it is full, `pop_reasons`).
- `Step.v`: the parts of a step.
  - The cursor of decisions (`skip_from` into a table of literals, `CursorT`).
  - `StepCore`, `StepInv` (adds well-formedness and `Entails`): the context agrees with the state between steps;
    the reason clauses are entailed and below the end of the trail (`SlotsOk`).
    The literals to decide on of the heuristic are literals of `f` (`DlitIn`); `with_heur` changes only the
    heuristic (`step_core_heur`).
  - `front_shorts`, `front_prop` (checking the short clauses and propagating), `decide_lit_spec` (deciding
    any unassigned literal of `f`) and `decide_spec`, `jump` (jumping back, dropping the reason clauses from
    there on), `jump_core` (with the asserted literal and its reason, `JumpReason`, for any heuristic),
    `final_state`, `step_inv_after`.
  - `initial_of(_inv)`: the initial context for any clause lists with the literals of the clauses of `f`
    (`ClauseOf`).
- `CStep.v`: the shared parts on the context alone, as C computes them: the trail is only read through its
  table, with the decision positions `lims` on a stack (`LimsOf`); `visit_t`, `propagate_t`, `check_shorts_t`
  (no trail), `unset_range` (on trail positions); `Agrees`: an outcome on the context agrees with a step.
- `SolverStep.v`: the solver step, which the C solver computes.
  - `step`: check the short clauses and propagate; on a conflict `resolve`: fail without decisions, and
    otherwise analyse it, clear the marks (`clear_marks`) and, if the literal to assert is below the current
    level, backjump there and assert it with the analysed clause as its reason; else flip the last decision
    (`flip`); the bump decays before the analysis, and a jump puts the unassigned atoms back in the heap
    (`jump_heur`). Otherwise decide on the literal `pick` gives, or else at the cursor. `step_spec`, `step_none`, giving `step_strategy` (backjumps are `Backjump`
    steps of `DPLL_BJ`).
  - `cstep`: the same on the context alone (`resolve_t`, `flip_t`); `cstep_spec`: it `Agrees` with `step`.

The former step with a separate conflict analysis (`AnalysisStep.v`, `AnalysisCStep.v`, the old `Analysis.v`)
is archived in `context/removed/`.

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
fewer than `2^30` literals, clauses and pool entries, room `rc < 2^30` for the literals of the reason clauses),
separate blocks for the tables, and that the clauses are exactly those of `f`.

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
- `c/Rep.v`: `RepL`/`RepB`/`Rep`, how the memory of `solver.c` holds a context of `Propagate.v`, the
  positions of its decisions and, during an analysis, its lower literals `lt` (`RepB`: none, between steps):
  the values per literal (`key_value`, so that `lit_value` is one load), the marks, reasons (`enc_reason`) and
  levels, the stack of reason clauses (`ReasonsIn`) and the heuristic (`HeurOk`); and the store lemmas
  (`rep_store_*`): what a store of the C code does to the represented context, those of the analysis in
  `c/RepReasons.v` and those of the heuristic in `c/RepHeur.v` (split to keep each file below 1 GB).
- One file per function of `../solver/solver.c`, each proving that it computes its model function, or gives up:
  - propagation: `LitValue.v`, `SetValue.v`, `Assign.v`, `Wpush.v`, `FindWatch.v`, `KeepRest.v` (also the
    memory during a visit, `VisitMem`), `Visit.v`, `Propagate.v`, `CheckShorts.v`;
  - the heuristic: `Rescale.v`, `HeapUp.v`, `HeapDown.v`, `HeapInsert.v`, `HeapPop.v`, `Bump.v`,
    `Decay.v`, `Pick.v`, `Reinsert.v`, `FillNone.v`, `AddAtoms.v`;
  - the analysis: `Mark.v` (mark a literal and bump its atom), `AddLits.v`, `AddReasonLits.v` (the literals of a reason, `reason_add`), `PrevMarked.v`,
    `UnmarkRange.v`, `Analyze.v` (the loop follows `analyze_loop`: `LoopRes`, `AnalyzeState`),
    `UnmarkLower.v`, `PushReason.v`, `PopReasons.v`;
  - the step: `SkipFrom.v`, `Phase.v`, `Cut.v` (puts the atoms back in the heap and pops the reason
    clauses), `Resolve.v` (backjump or
    flip), `Step.v` (`step` computes `cstep`), `Solve.v` (`solve` terminates by
    `strict_derivation_well_founded` and answers by `step_strategy`);
  - the initial context: `Zero.v`, `CheckClauses.v`, `CheckLits.v`, `CheckRoom.v`, `Index.v`, `Init.v`
    (`init` sets up `initial_of`), and `Solver.v`.
- Trust left: the Rocq kernel, the axioms of CompCert's semantics (excluded middle, functional extensionality,
  two of the classical reals, and the semantics of external calls, which the solver does not make), CompCert's
  parser and assembler, and the driver `../solver/main.c`.
