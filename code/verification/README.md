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

| Theorem                          | File                        | Statement (informally)                                                                        |
|----------------------------------|-----------------------------|-----------------------------------------------------------------------------------------------|
| `final_exists`                   | `Satisfiability.v`          | From the initial state, some final state is reachable.                                        |
| `final_model`                    | `Satisfiability.v`          | A final state other than `fail` is a model of the formula.                                    |
| `final_sat_refl`                 | `Satisfiability.v`          | A formula is satisfiable iff a final non-`fail` state is reachable.                           |
| `final_unsat_refl`               | `Satisfiability.v`          | A formula is unsatisfiable iff `fail` is reachable.                                           |
| `sat_decidable`                  | `Satisfiability.v`          | Every formula is satisfiable or unsatisfiable.                                                |
| `strict_derivation_well_founded` | `Termination.v`             | If every rule keeps the formula and decreases the measure, there are no infinite derivations. |
| `derivation_entails`             | `entailment/Preservation.v` | If every rule preserves entailment, so does every derivation.                                 |
| `next_state_strategy`            | `Strategy.v`                | The concrete solver step is a valid strategy.                                                 |

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
                 +--------+--------+
                 |                 |
               Model           WellFormed
                 |                 |
                 |               State
                 |                 |
                 +--------+--------+
                          |
                        Rule
                 +--------+--------+
                 |                 |
       entailment/Entails       Measure
                 |                 |
     entailment/Properties         |
                 |                 |
                 +--------+--------+
                          |
          rules/{Fail,Unit,Decide,Backtrack,Pure}
                          |
                        Trans
       +------------------+-----------------+------------------+
       |                  |                 |                  |
entailment/Preservation  Termination     Strategy (1)     Normalization (2)
       |                  |                 |                  |
       |                  +--------+--------+                  |
       |                           |                           |
       |                         Solve                         |
       |                           |                           |
       +---------------------------+---------------------------+
                                   |
                            Satisfiability
```

(1) `Strategy` also imports the helper `utils/Inspect`. (2) `Normalization` also imports
the helper `utils/Dedupe`. `rules/Fail`, `rules/Decide` and `rules/Pure` only need
`entailment/Entails`; `rules/Unit` and `rules/Backtrack` also use
`entailment/Properties`.

## Adding a rule

A rule is a relation on states, `Rule := relation State`. `Trans rs` only takes steps
from a non-`fail` state, so `fail` is final whatever the rules say about it. The
general results take the properties of the rules as hypotheses on the rule set:

- `trans_equivalent`/`derivation_equivalent` need `Forall PreservesEquivalence rs`:
  the formula only changes to an equivalent one. This is the invariant on the formula
  that soundness uses.
- `trans_entails`/`derivation_entails` need `Forall PreservesEntails rs`.
- `trans__state_lt` needs `Forall Decreasing rs`, and `trans_well_founded`/
  `strict_derivation_well_founded` also need `Forall KeepsFormula rs`, because the
  measure is relative to a fixed formula.

A rule that keeps the formula (`KeepsFormula`) preserves equivalence for free
(`keeps_formula_equivalence`); all current rules are of this kind.

To add a rule:

1. Create `rules/<Rule>.v` with the rule as an inductive of type `Rule`, and prove
   the properties you need (`KeepsFormula` or `PreservesEquivalence`,
   `PreservesEntails`, `Decreasing`, `ModelFinal`). Nothing imports the file yet,
   so this does not affect the rest of the development.
2. Import it in `Trans.v` and use it in a rule set, e.g. a new list next to `DPLL`.
3. For that rule set, prove the `Forall`s from the per-rule lemmas, as
   `dpll_keeps_formula`, `dpll_equivalence`, `dpll_entails`, `dpll_decreasing` and
   `dpll_model_final` do for `DPLL`.

Adding the rule to `DPLL` itself also requires updating the DPLL-specific proofs that
case on its rules: `final_dpll_basic`, `final_unsat_refl` (only `Fail` reaches `fail`)
and the `dpll_*` lemmas.

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

| File           | Contents                                                                                                                                                                                                                                                                                                                                                                                                    |
|----------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Assignment.v` | Partial assignments `PA`: lists of literals annotated as decision (`dec`) or propagation (`prop`), with the notations `m ++d l`, `m ++p l` and `m ++a n` (written so that the newest entries appear on the right); `NoDecisions`; `split_last_decision`, which splits off the most recent decision.                                                                                                         |
| `Evaluation.v` | Three-valued evaluation of literals, clauses and formulas under a partial assignment (`l_eval`, `c_eval`, `f_eval`) and their Boolean versions (`l_true`, `c_false`, …); `Def`/`Undef`; characterisations such as `c_eval_true_iff` and `f_eval_true_iff`; lemmas about removing a literal from a clause and extending an assignment with an undefined literal.                                             |
| `Model.v`      | `Model m f` (`m` makes `f` true); `unit_cnf l` (a literal as a formula) and `units m` (an assignment as one unit clause per literal); lemmas for models of unions, units and unit clauses; transferring falsity from an assignment to any model of it; semantic consequence `f ⊨ g` and equivalence `Equivalent f g` between formulas, with `equivalent_refl`/`_sym`/`_trans` and `model_union_equivalent`. |
| `WellFormed.v` | Well-formed assignments for a formula: no atom assigned twice (`NoDuplicates`), and only atoms occurring in the formula (`Bounded`); lemmas about extending and restricting them; `initial_well_formed`.                                                                                                                                                                                                    |

### States and rules

| File      | Contents                                                                                                                                                                                                                                                                                                               |
|-----------|------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `State.v` | States `State`: `fail`, or a well-formed assignment for a formula.                                                                                                                                                                                                                                                     |
| `Rule.v`  | The type `Rule` of rules (relations on states); `KeepsFormula` (the rule never changes the formula), `PreservesEquivalence` (the rule only changes the formula to an equivalent one) with `keeps_formula_equivalence`, and `ModelFinal` (the rule cannot fire from a model that defines every literal of the formula). |

### Entailment

The entailment invariant says that every propagated literal on the trail follows
from the formula together with the literals before it, except pure literals, which
only preserve models.

| File                      | Contents                                                                                                                                                                                                                                                                                            |
|---------------------------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `entailment/Entails.v`    | The invariant `Entails f m`, built one trail entry at a time (`e_nil`, `e_decide`, `e_propagate`, `e_pure`); `PreservesEntails`, the property that a rule preserves it (relative to the formula of each state).                                                                                     |
| `entailment/Properties.v` | `entails_prefix` (the older part of an entailed trail is entailed) and `entails_extend` (a model of the formula and an entailed trail extends past propagated literals); used for soundness of `Fail` and `Backtrack`; `entails_equivalent` (entailment only depends on the models of the formula). |

### Termination measure

| File        | Contents                                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
|-------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Measure.v` | The termination measure: `score`, which records for each decision level how far the number of propagated literals is below a bound (one more than the largest atom of the formula), padded to a fixed length; the order `StateLt` (`s >>[f] s'`) on states, ordered lexicographically by score, with its well-foundedness (`state_lt_well_founded`); `Decreasing`, the property that a rule decreases the measure; lemmas about how each kind of step changes the score. |

### The rules

Each file defines its rule (`r_<rule>` is its only constructor) and proves the four
properties that the main theorems combine:

- `<rule>_keeps_formula: KeepsFormula <Rule>` (used in `Trans.v` for `dpll_equivalence`, and in `Termination.v`),
- `<rule>_entails: PreservesEntails <Rule>` (used in `entailment/Preservation.v`),
- `<rule>_state_lt: Decreasing <Rule>` (used in `Termination.v`),
- `<rule>_model_final: ModelFinal <Rule>` (used in `Satisfiability.v`).

| File                | Rule                                                                                                                                                                                           |
|---------------------|------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `rules/Fail.v`      | `Fail`: all literals assigned with a conflict and no decisions; go to `fail`.                                                                                                                  |
| `rules/Unit.v`      | `Unit`: a clause is false except for one unassigned literal; propagate it.                                                                                                                     |
| `rules/Decide.v`    | `Decide`: assign an unassigned literal of the formula as a decision.                                                                                                                           |
| `rules/Backtrack.v` | `Backtrack`: on a conflict, flip the most recent decision. Also contains `backtrack_no_model` and `backtrack_neg`, which show that the flipped literal follows from the formula and the trail. |
| `rules/Pure.v`      | `Pure`: assign a literal whose negation does not occur in the formula.                                                                                                                         |

### The transition system

| File                        | Contents                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
|-----------------------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Trans.v`                   | `Trans rs`, the transition relation of a list of rules (`t_step`: a step of one of the rules from a non-`fail` state), with notations `s ==>[rs] s'`, `==>*[rs]`, `==>+[rs]`, and `==>`/`==>*`/`==>+` for the full system `DPLL`; the smaller rule set `Basic`; `trans_rule`, `trans_union` and `trans_incl`; final states `Final rs` and `final_dpll_basic`; `trans_same_formula`/`derivation_same_formula` and `dpll_keeps_formula`; `trans_equivalent`/`derivation_equivalent` and `dpll_equivalence`; `fail_predecessor`. |
| `entailment/Preservation.v` | `trans_entails` and `derivation_entails`: if every rule preserves entailment, so does every transition and derivation; `dpll_entails` for `DPLL`.                                                                                                                                                                                                                                                                                                                                                                             |
| `Termination.v`             | `trans__state_lt`: if every rule decreases the measure, so does every transition; from that, if every rule also keeps the formula, `trans_well_founded` and `strict_derivation_well_founded`; `dpll_decreasing` for `DPLL`.                                                                                                                                                                                                                                                                                                   |

### Normalization

| File              | Contents                                                                                                                                                                                                                                                                                                                                                                                            |
|-------------------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Normalization.v` | Turns any model of a formula into a final state reachable from the initial state: `totalize` (assign every undefined literal), `convert_prop` (make every literal a decision), `bound` (drop literals outside the formula), `dedupe` (remove duplicate atoms), and `normalize`, which combines them; each step's properties, and `normalize_derivation`. Used for completeness of `final_sat_refl`. |

### Strategy and solver

| File         | Contents                                                                                                                                                                                                                                                                                                                                              |
|--------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Strategy.v` | `Strategy next`: a step function that only takes `==>+` steps, never steps from `fail`, and only stops at final states of `Basic`; the search functions `find_conflict`, `find_unit`, `find_decision` (and helpers) with their specifications; `next_state`, one solver step, with `next_state_sound`, `next_state_exists` and `next_state_strategy`. |
| `Solve.v`    | `solve`: iterates a strategy until a final state, by well-founded recursion on `strict_derivation_well_founded`; `solve_final_derivation` states that the result is reachable and final.                                                                                                                                                              |

### Main results

| File               | Contents                                                                        |
|--------------------|---------------------------------------------------------------------------------|
| `Satisfiability.v` | `Sat`, `Unsat` and `Total`; `dpll_model_final`; the main theorems listed above. |
