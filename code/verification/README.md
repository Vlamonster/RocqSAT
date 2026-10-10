# RocqSAT verification

A Rocq formalization of an abstract, DPLL-style transition system for SAT solving.
It proves that the system is **sound** (a final state that is not `fail` gives a
model, and reaching `fail` means the formula is unsatisfiable), **complete**
(every formula ends up in one of the two), and **terminating** (no infinite
derivations). It also implements a concrete strategy, proves that it follows the
system, and derives decidability of satisfiability.

Build everything from the `code/` directory with:

```sh
dune build
```

The files are compiled as the library `RocqSAT`. Files in a subdirectory are
qualified by that directory, e.g. `From RocqSAT.rules Require Import Unit.`

## Main results

| Theorem                          | File                        | Statement (informally)                                              |
|----------------------------------|-----------------------------|---------------------------------------------------------------------|
| `final_exists`                   | `Satisfiability.v`          | From the initial state, some final state is reachable.              |
| `final_model`                    | `Satisfiability.v`          | A final state other than `fail` is a model of the formula.          |
| `final_sat_refl`                 | `Satisfiability.v`          | A formula is satisfiable iff a final non-`fail` state is reachable. |
| `final_unsat_refl`               | `Satisfiability.v`          | A formula is unsatisfiable iff `fail` is reachable.                 |
| `sat_decidable`                  | `Satisfiability.v`          | Every formula is satisfiable or unsatisfiable.                      |
| `strict_derivation_well_founded` | `Termination.v`             | There are no infinite derivations.                                  |
| `derivation_entails`             | `entailment/Preservation.v` | Every derivation preserves the entailment invariant.                |
| `next_state_strategy`            | `Strategy.v`                | The concrete solver step is a valid strategy.                       |

## Module dependencies

Each module is drawn above the modules that import it. Only direct dependencies
are shown (an edge implied by a longer path is left out), and the five rule files
are grouped into one node.

```text
                      utils/EqB
                          |
                         Atom
                          |
                         Lit
                 +--------+--------+
                 |                 |
                 |               Clause
                 |                 |
            Assignment            CNF
                 +--------+--------+
                          |
                      Evaluation
                 +--------+-----------------+
                 |                          |
               Model                   WellFormed
                 |                          |
       entailment/Entails                 Trans
                 |                          |
     entailment/Properties     +------------+------------+-----------------+
                 |             |                         |                 |
                 |          Measure                 Strategy (1)     Normalization (2)
                 +------+------+                         |                 |
                        |                                |                 |
    rules/{Fail,Unit,Decide,Backtrack,Pure}              |                 |
                        |                                |                 |
           +------------+------------+                   |                 |
           |                         |                   |                 |
 entailment/Preservation        Termination              |                 |
           |                         |                   |                 |
           |                         +---------+---------+                 |
           |                                   |                           |
           |                                 Solve                         |
           |                                   |                           |
           +-----------------------------------+-------------+-------------+
                                                             |
                                                      Satisfiability
```

(1) `Strategy` also imports the helper `utils/Inspect`. (2) `Normalization` also imports
the helper `utils/Dedupe`. `rules/Fail`, `rules/Decide` and `rules/Pure` only need
`entailment/Entails`; `rules/Unit` and `rules/Backtrack` also use
`entailment/Properties`.

## File index

Files are listed in dependency order: each file only depends on files above it.

### Utilities

General-purpose helpers in `utils/`, independent of the rest of the development.

| File              | Contents                                                                                       |
|-------------------|------------------------------------------------------------------------------------------------|
| `utils/EqB.v`     | The `EqB` typeclass for computational (Boolean) equality, with the notation `x =? y`.          |
| `utils/Inspect.v` | `inspect`, a helper for keeping an equation when matching on a value in Equations definitions. |
| `utils/Dedupe.v`  | `dedupe_by`, which removes duplicates from a list with respect to a Boolean relation.          |

### Literals, clauses and formulas

| File       | Contents                                                                                                                                                                                                                            |
|------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Atom.v`   | `Atom` (propositional variables, as natural numbers), its `EqB` instance and `eqb` lemmas.                                                                                                                                          |
| `Lit.v`    | Literals `Lit` (`Pos`/`Neg` of an atom) with `extract`, their `EqB` instance and lemmas; `LitOrderType`, the ordering used for sets of literals; module `Neg` with negation `¬l` and its lemmas (`involutive`, `self_neqb_neg`, …). |
| `Clause.v` | `Clause`, a finite set (MSet) of literals, read as their disjunction, plus lemmas relating set equality to `exists_`/`for_all`.                                                                                                     |
| `CNF.v`    | `CNF`, a finite set of clauses, read as their conjunction; `l_in_f` (a literal or its negation occurs in a formula) with its characterisations.                                                                                     |

### Assignments and semantics

| File           | Contents                                                                                                                                                                                                                                                                                                                                                        |
|----------------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Assignment.v` | Partial assignments `PA`: lists of literals annotated as decision (`dec`) or propagation (`prop`), with the notations `m ++d l`, `m ++p l` and `m ++a n` (written so that the newest entries appear on the right); `NoDecisions`; `split_last_decision`, which splits off the most recent decision.                                                             |
| `Evaluation.v` | Three-valued evaluation of literals, clauses and formulas under a partial assignment (`l_eval`, `c_eval`, `f_eval`) and their Boolean versions (`l_true`, `c_false`, …); `Def`/`Undef`; characterisations such as `c_eval_true_iff` and `f_eval_true_iff`; lemmas about removing a literal from a clause and extending an assignment with an undefined literal. |
| `Model.v`      | `Model m f` (`m` makes `f` true); `unit_cnf l` (a literal as a formula) and `units m` (an assignment as one unit clause per literal); lemmas for models of unions, units and unit clauses; transferring falsity from an assignment to any model of it.                                                                                                          |
| `WellFormed.v` | Well-formed assignments for a formula: no atom assigned twice (`NoDuplicates`), and only atoms occurring in the formula (`Bounded`); lemmas about extending and restricting them; `initial_well_formed`.                                                                                                                                                        |

### The transition system

| File      | Contents                                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
|-----------|----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Trans.v` | States `State` (`fail`, or a well-formed assignment for a formula); the rules `Rule` (`Fail`, `Unit`, `Decide`, `Backtrack`, `Pure`); `Trans rs`, the transition relation of a list of rules, with notations `s ==>[rs] s'`, `==>*[rs]`, `==>+[rs]`, and `==>`/`==>*`/`==>+` for the full system `DPLL`; the smaller rule set `Basic`; `trans_union`, which views `Trans rs` as the union of its rules; final states `Final rs`; lemmas that transitions keep the formula fixed. |

### Entailment

The entailment invariant says that every propagated literal on the trail follows
from the formula together with the literals before it, except pure literals, which
only preserve models.

| File                        | Contents                                                                                                                                                                                                               |
|-----------------------------|------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `entailment/Entails.v`      | Semantic consequence `f ⊨ g` between formulas, and the invariant `Entails f m`, built one trail entry at a time (`e_nil`, `e_decide`, `e_propagate`, `e_pure`).                                                        |
| `entailment/Properties.v`   | `entails_prefix` (the older part of an entailed trail is entailed) and `entails_extend` (a model of the formula and an entailed trail extends past propagated literals); used for soundness of `Fail` and `Backtrack`. |
| `entailment/Preservation.v` | `trans_entails` and `derivation_entails`: every transition and derivation, for any rule set, preserves entailment. Combines the per-rule lemmas from `rules/`.                                                         |

### Normalization

| File              | Contents                                                                                                                                                                                                                                                                                                                                                                                            |
|-------------------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Normalization.v` | Turns any model of a formula into a final state reachable from the initial state: `totalize` (assign every undefined literal), `convert_prop` (make every literal a decision), `bound` (drop literals outside the formula), `dedupe` (remove duplicate atoms), and `normalize`, which combines them; each step's properties, and `normalize_derivation`. Used for completeness of `final_sat_refl`. |

### Termination

| File            | Contents                                                                                                                                                                                                                                                                                                                                                                                                   |
|-----------------|------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Measure.v`     | The termination measure: `score`, which records for each decision level how far the number of propagated literals is below a bound (one more than the largest atom of the formula), padded to a fixed length; the order `StateLt` (`s >>[f] s'`) on states, ordered lexicographically by score, with its well-foundedness (`state_lt_well_founded`); lemmas about how each kind of step changes the score. |
| `Termination.v` | `trans__state_lt`: every transition decreases the measure (any rule set); from that, `trans_well_founded` and `strict_derivation_well_founded`.                                                                                                                                                                                                                                                            |

### The rules

Each file proves, for its rule on its own (`s ==>[[R]] s'`), the three facts that
the main theorems combine:

- `<rule>_entails`: the rule preserves entailment (used in `entailment/Preservation.v`),
- `<rule>_state_lt`: the rule decreases the termination measure (used in `Termination.v`),
- `<rule>_model_final`: the rule cannot fire from a total model of the formula (used in `Satisfiability.v`).

| File                | Rule                                                                                                                                                                                           |
|---------------------|------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `rules/Fail.v`      | `Fail`: all literals assigned with a conflict and no decisions; go to `fail`.                                                                                                                  |
| `rules/Unit.v`      | `Unit`: a clause is false except for one unassigned literal; propagate it.                                                                                                                     |
| `rules/Decide.v`    | `Decide`: assign an unassigned literal of the formula as a decision.                                                                                                                           |
| `rules/Backtrack.v` | `Backtrack`: on a conflict, flip the most recent decision. Also contains `backtrack_no_model` and `backtrack_neg`, which show that the flipped literal follows from the formula and the trail. |
| `rules/Pure.v`      | `Pure`: assign a literal whose negation does not occur in the formula.                                                                                                                         |

### Strategy and solver

| File         | Contents                                                                                                                                                                                                                                                                                                                                              |
|--------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Strategy.v` | `Strategy next`: a step function that only takes `==>+` steps, never steps from `fail`, and only stops at final states of `Basic`; the search functions `find_conflict`, `find_unit`, `find_decision` (and helpers) with their specifications; `next_state`, one solver step, with `next_state_sound`, `next_state_exists` and `next_state_strategy`. |
| `Solve.v`    | `solve`: iterates a strategy until a final state, by well-founded recursion on `strict_derivation_well_founded`; `solve_final_derivation` states that the result is reachable and final.                                                                                                                                                              |

### Main results

| File               | Contents                                                        |
|--------------------|-----------------------------------------------------------------|
| `Satisfiability.v` | `Sat`, `Unsat` and `Total`, and the main theorems listed above. |
