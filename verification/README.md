# RocqSAT verification

A Rocq formalization of an abstract DPLL-style transition system for SAT solving, proving:

- **soundness**: a final non-`fail` state is a model, and reaching `fail` means unsatisfiable;
- **completeness**: every formula reaches one of the two;
- **termination**: there are no infinite derivations.

It also gives a concrete, verified strategy and derives decidability of satisfiability.

- Build from the repository root with `dune build`.
- The library is `RocqSAT`; subdirectories are qualified, e.g. `From RocqSAT.rules Require Import Unit.`

## Main results

- The first five theorems hold for each system `<S>` in `Basic`, `DPLL` and `DPLL_BJ`
  (e.g. `DPLL.final_sat_refl`).
- `DPLL_BJ.final_model` assumes a well-formed entailed state; every reachable state is one.

| Theorem                          | File                      | Statement (informally)                                              |
|----------------------------------|---------------------------|---------------------------------------------------------------------|
| `final_exists`                   | `systems/<S>.v`           | From the initial state, some final state is reachable.              |
| `final_model`                    | `systems/<S>.v`           | A final state other than `fail` is a model of the formula.          |
| `final_sat_refl`                 | `systems/<S>.v`           | A formula is satisfiable iff a final non-`fail` state is reachable. |
| `final_unsat_refl`               | `systems/<S>.v`           | A formula is unsatisfiable iff `fail` is reachable.                 |
| `sat_decidable`                  | `systems/<S>.v`           | Every formula is satisfiable or unsatisfiable.                      |
| `strict_derivation_well_founded` | `Termination.v`           | There are no infinite derivations from well-formed states.          |
| `scheduled_terminates`           | `Schedule.v`              | Restarting on an unbounded schedule terminates.                     |
| `derivation_entails`             | `Trans.v`                 | Every derivation preserves entailment.                              |
| `next_state_strategy`            | `refinement/NextState.v`  | The concrete solver step is a valid strategy for `DPLL_BJ`.         |
| `next_impl_strategy`             | `refinement/Imperative.v` | The same step on a store updated in place is a valid strategy.      |

## Axioms and trusted code

- Everything, including the refinement, is closed under the global context: no axioms.
- The extracted solver (`runner/`) runs `next_impl_strategy` with Luby restarts (`solve_restart`)
  on a store (`refinement/Store.v`) realized by mutable arrays (`runner/store_rt.ml`).
- Trusted: the table operations (`tmake`, `vget` … `pset`) agree with their model in `Table.v`
  and `Store.v`. This holds because stores are used linearly (only through the state monad
  of `Store.v`, and by `next_impl`).
- Extraction also realizes `nat` as OCaml `int` (with `int`-typed `Nat.eqb`, `Nat.leb`, `Nat.max`,
  `Nat.sub`, `le_dec`) and atom equality as `Int.equal`.

## Module dependencies

- Each module is drawn above the modules that import it; implied edges are left out.
- The rule files form one node, as do the system files (each imports the one before it).
- `Schedule.v` (restarts) imports `Termination` and `rules/Restart.v`; nothing imports it.
- `utils/` is left out, and so is `Solve` (on `Strategy` and `Termination`), used only by `runner/`.

```text
                         Atom
                          |
                         Lit
                 +--------+--------+
                 |                 |
                 |               Clause
                 |                 |
            Assignment            CNF
                 +--------+--------+
                 |                 |
             Evaluation          State
                 |                 |
                 +--------+        |
                 |        |        |
                 |        +--------+
                 |                 |
               Model           WellFormed
                 |                 |
              Entails          Measure
                 |                 |
                 +--------+--------+
                          |
                        Rule
                          |
   rules/{Fail,Unit,Decide,Backtrack,Backjump,Pure}
                          |
                        Trans
              +-----------+-----------+
              |           |           |
          Strategy   Termination  Normalization
              |           |           |
              |           +-----+-----+
              |                 |
       refinement         Satisfiability
                                |
                  systems/{Basic,DPLL,DPLL_BJ}
```


## Adding a rule

A `Rule` bundles a relation `step` on states with these properties:

- `rule_equivalence`: the formula only changes to an equivalent one (used for soundness);
- `rule_well_formed`: well-formed states stay well-formed;
- `rule_entails`: the entailment invariant is preserved;
- `rule_decreasing`: from a well-formed state, the termination measure decreases;
- `rule_model_final`: the rule cannot fire from a total model.

Notes:

- `Trans rs` never steps from `fail`, so `fail` is always final.
- Well-formedness is an invariant (`derivation_well_formed`), not part of states.
- Since the properties come with the rules, the general results (`derivation_equivalent`,
  `derivation_entails`, `strict_derivation_well_founded`, …) hold for any rule set.
- Rules may change the formula: a decreasing step never increases its largest atom
  (`state_lt_max_atom`).
- A rule that keeps the formula gets `rule_equivalence` from
  `preserves_formula_equivalence`; all current rules do.

Steps:

1. Create `rules/<Rule>.v`: the inductive `<Rule>Step`, its properties, and `<Rule>: Rule`.
2. Use it in a rule set in `Trans.v`.
3. Add `systems/<S>.v`. The main theorems follow from `sat_iff_final`, `unsat_iff_fail`
   and `sat_or_unsat` (`Satisfiability.v`), given that:
   - the rules include `Decide`;
   - only `Fail` reaches `fail`;
   - a final state is reachable (`final_exists`);
   - final well-formed entailed states are models (`final_model`).

   `systems/DPLL_BJ.v` shows how to get the last two from another system.
4. When changing an existing rule set, update the proofs that case on its rules
   (`trans_dpll_basic`, `<s>_fail_only`).

## File index

Files are listed in dependency order.

### Utilities (`utils/`)

- `EqB.v`: typeclass `EqB` for Boolean equality, notation `x =? y`.
- `Member.v`: typeclass `Member`, notations `x ∈ y` and `x ∉ y`.
- `Inspect.v`: `inspect`, to keep an equation when matching in Equations definitions.
- `Dedupe.v`: `dedupe_by`, removing duplicates with respect to a Boolean relation.
- `Invariant.v`: `clos_refl_trans_invariant`, lifting a step invariant to the closure.

### Literals, clauses and formulas

- `Atom.v`: atoms as natural numbers, with `EqB`.
- `Lit.v`: literals `Pos`/`Neg` with `extract` and `EqB`; `LitOrderType`; module `Neg`
  with negation `¬l` (`involutive`, `self_neqb_neg`, …).
- `Clause.v`: clauses as sets (MSet) of literals; `l ∈ c`.
- `CNF.v`: formulas as sets of clauses; `c ∈ f`, `l ∈ f` and its Boolean `mem_lit`.

### Assignments, states and semantics

- `Assignment.v`: trails `PA` of propagated and decided literals.
  - Notation: `⟨m, l⟩` propagates, `⟨m; l⟩` decides, `⟨m ++ n⟩` appends, `⟨⟩` is empty.
  - `PA.app`, `PA.In` (`l ∈ m`), `PA.length`, `atoms`, `NoDecisions`, `NoPropagations`,
    `split_last_decision`.
- `Evaluation.v`: three-valued `l_eval`, `c_eval`, `f_eval` and Boolean versions; `Def`,
  `Undef`; `*_true_iff`/`*_false_iff`; lemmas on removing and adding literals;
  `l_eval_app_some`/`l_eval_app_undef`.
- `Model.v`: `Model m f`; `unit_cnf`, `units`, `neg_clause`; `model_singleton_iff`;
  transferring falsity to models; `f ⊨ g` and `Equivalent`.
- `State.v`: `fail` or `state m f`.
- `WellFormed.v`: `WellFormed` = `NoDuplicates` + `Bounded`; extending and restricting;
  `nodup_in_true`; `initial_well_formed`.

### Entailment

- `Entails.v`: `Entails f m`, every propagated literal follows from the formula and the
  literals before it (pure literals only preserve models).
  - Constructors `e_nil`, `e_decide`, `e_propagate`, `e_pure`.
  - `entails_prefix`, `entails_extend`, `entails_equivalent`.

### Termination measure

- `Measure.v`:
  - `score`: per decision level, the bound minus its propagations, padded;
  - `StateLt` (`s >>[f] s'`): `fail` lowest, then by `score`, then `score_total`;
  - `state_lt_well_founded`, `state_lt_incl`, `state_lt_max_atom`;
  - `rank`: the measure as a number (digits in a fixed base), lower after every step
    (`state_lt_rank`), so it bounds the number of steps;
  - how each kind of step changes the score.

### Rules

- `Rule.v`: the properties `PreservesFormula`, `PreservesEquivalence`,
  `PreservesWellFormed`, `PreservesEntails`, `Decreasing`, `ModelFinal`; the record `Rule`.
- Each `rules/<Rule>.v` has `<Rule>Step` (constructor `r_<rule>`), the lemmas
  `<rule>_same_formula`, `_well_formed`, `_entails`, `_state_lt`, `_model_final`, and `<Rule>`.
  - `Fail.v`: conflict without decisions; go to `fail`.
  - `Unit.v`: a clause is false except for one unassigned literal; propagate it.
  - `Decide.v`: decide an unassigned literal of the formula.
  - `Backtrack.v`: on a conflict, flip the last decision; `backtrack_neg` (the flipped
    literal follows).
  - `Backjump.v`: on a conflict, jump back before some decision and propagate a literal of
    an entailed clause whose other literals are false there.
    - `backtrack_backjump`: from a well-formed entailed state, Backtrack steps are Backjump
      steps.
    - `backjump_backtrack`: Backtrack applies whenever Backjump does.
  - `Pure.v`: assign a literal whose negation does not occur in the formula.
  - `Restart.v`: start over from `⟨⟩`. Not a `Rule`, since it raises the measure; only
    `RestartStep` and its `_same_formula`, `_well_formed`, `_entails` lemmas.

### Transition system

- `Trans.v`:
  - `Trans rs` (`s ==>[rs] s'`, `==>*[rs]`, `==>+[rs]`; `==>` etc. for `DPLL`);
  - rule sets `DPLL`, `Basic`, `DPLL_BJ`;
  - `Final rs`, `trans_dpll_basic`, `trans_basic_dpll`, `final_dpll_basic`;
  - `final_or_step`: every state is final for `Basic` or has a `Basic` step;
  - `derivation_invariant` and the `trans_*`/`derivation_*` lemmas for well-formedness,
    equivalence and entailment;
  - `fail_predecessor`.
- `Termination.v`: every transition from a well-formed state decreases the measure;
  `trans_well_founded`, `strict_derivation_well_founded`, for any rule set.
- `Schedule.v`: restarts on a schedule `g`, where restart `k` needs `g k` rounds of
  `==>+[rs]` since the previous one (`Scheduled rs g`).
  - `scheduled_terminates`: no infinite derivations if `g` is unbounded and the rules keep
    the formula (`KeepsFormula`, e.g. `dpll_bj_keeps_formula`). Between restarts the rank
    bounds the steps, so once `g` exceeds that bound no further restart can happen.
  - `scheduled_derivation`: a restart returns to the initial state, so every reachable state
    is reachable without restarts, and the results for `rs` carry over.
  - `luby`: the Luby sequence 1 1 2 1 1 2 4 …; `luby_unbounded`.

### Normalization

- `Normalization.v`: turns a model into a reachable final state (`totalize`,
  `convert_prop`, `bound`, `dedupe`, `normalize`); `normalize_derivation` needs `Decide`.

### Strategy and solver

- `Strategy.v`: `Strategy rs Inv next`, a step function on a state and a context of its own
  choosing, kept consistent by `Inv`; it never steps from `fail`, only stops at final states
  of `Basic`, and only takes `==>+[rs]` steps preserving `Inv`; `strategy_trans`.
- `Solve.v`: `solve` iterates a strategy by well-founded recursion;
  `solve_final_derivation`.
  - `solve_restart`: the same with restarts on an unbounded schedule, given a `restart` of the
    context that keeps `Inv`; it recurses on the accessibility proof of `scheduled_terminates`.
    `solve_restart_final`: the result is reachable without restarts and final.

### Refinement (`refinement/`)

A concrete strategy, implemented efficiently and proved to agree with the specification.

- `Table.v`: `Table A`, tables as functions (`tget`, `tset`, `tmake`); extracted as arrays.
- `Lookup.v`: `Values` (the value of each atom), `values m`, `lookup` (agrees with `l_eval`);
  `ValuesOf`, `Fresh`, `Incl`; `unassign_level`, `unassign_all`.
- `Search.v`: `clause_lists`, `formula_lits`; `skip_assigned` and the `Cursor` invariant;
  `phase` (decide an atom with its last value, `phase_cases`).
- `Watches.v`: two watched literals.
  - `WatchStruct` (every clause is in its watches' lists or pending), `WatchOK`, `Settled`.
  - `repair`, `visit` (with the other-watch fast path), `process`, `unpend`, `index_clauses`;
    `pend_all` (make every watched clause pending, for a restart).
- `Analysis.v`: backjumping.
  - `Entailed`, `entailed_resolve`, `clause_of` (`entailed_consequence`).
  - `analyze`: resolve the conflict clause with reasons until one literal is at the last level,
    using marks for membership (`resolve_marked`); marked literals are in the clause (`MarkedIn`).
  - `plan`: where to jump, checked against the trail in one pass using the marks (`marked_neg`,
    `plan_spec`); `unassign_segment`.
  - Reasons and levels are hints: soundness never depends on them.
- `NextState.v`: `next_state` on a `SolverContext` (values, clauses, cursor, watches, queue,
  saved cursors, and the reason, level, decision level and phase hints).
  - On a conflict it backjumps as planned, or else flips the last decision
    (`backtrack_backjump`); both unassign whole levels and keep the watches.
  - `CoreInv`, `SavedWatches`, no marks between steps (`Unmarked`); `ContextInv` adds
    well-formedness and `Entails`.
  - `next_state_sound`, `next_state_none`, `next_state_exists`, `next_state_inv`, giving
    `next_state_strategy`; `initial_context(_inv)`.
  - `restart_context(_inv)`: no values, all literals to decide on, every watched clause pending
    (so unit clauses are found again); clauses, watches, hints, marks and phases are kept.
- `Store.v`: the store of tables and its state monad (`M`, `ret`, `bind`, `runM`, `vget` … `pset`).
- `Imperative.v`: `next_stateM` and its parts (`visitM`, `processM`, …), each with a `_spec`
  equal to its pure counterpart; `next_impl_strategy`, `initial_impl(_inv)`,
  `restart_impl(_inv)`.

### Satisfiability

- `Satisfiability.v`: `Sat`, `Unsat`, `Total`; for any rule set:
  - `final_exists_progress`: if reachable states step or are final, a final state is reachable;
  - `sat_final`: with `Decide`, a model gives a reachable final state;
  - `fail_unsat`: if only `Fail` reaches `fail`, reaching it means unsatisfiable;
  - `final_reachable_model`;
  - `sat_iff_final`, `unsat_iff_fail`, `sat_or_unsat`: the main theorems, with the facts
    they need as hypotheses.

### Transition systems (`systems/`)

Each file instantiates the theorems of `Satisfiability.v`.

- `Basic.v` (`Fail`, `Decide`, `Backtrack`): `final_exists` via `final_or_step`; `final_model`
  by finding a step from any non-model.
- `DPLL.v` (`Fail`, `Unit`, `Decide`, `Backtrack`, `Pure`): `final_exists` via
  `final_or_step`; `final_model` via `Basic.final_model`.
- `DPLL_BJ.v` (`DPLL` with `Backjump` for `Backtrack`): `trans_dpll_bj_dpll`,
  `trans_dpll_dpll_bj`, `final_basic_dpll_bj`; `final_exists` via `final_or_step`;
  `final_model` via `DPLL.final_model`.
