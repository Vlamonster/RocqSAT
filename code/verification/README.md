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

| Theorem                          | File               | Statement (informally)                                                                      |
|----------------------------------|--------------------|---------------------------------------------------------------------------------------------|
| `final_exists`                   | `Satisfiability.v` | From the initial state, some final state is reachable.                                      |
| `final_model`                    | `Satisfiability.v` | A final state other than `fail` is a model of the formula.                                  |
| `final_sat_refl`                 | `Satisfiability.v` | A formula is satisfiable iff a final non-`fail` state is reachable.                         |
| `final_unsat_refl`               | `Satisfiability.v` | A formula is unsatisfiable iff `fail` is reachable.                                         |
| `sat_decidable`                  | `Satisfiability.v` | Every formula is satisfiable or unsatisfiable.                                              |
| `strict_derivation_well_founded` | `Termination.v`    | If every rule keeps the formula, there are no infinite derivations from well-formed states. |
| `derivation_entails`             | `Trans.v`          | Every derivation preserves entailment.                                                      |
| `next_state_strategy`            | `Strategy.v`       | The concrete solver step is a valid strategy.                                               |

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
          rules/{Fail,Unit,Decide,Backtrack,Pure}
                          |
                        Trans
              +-----------+-----------+
              |           |           |
         Termination   Strategy   Normalization (2)
              |           |           |
              +-----+-----+           |
                    |                 |
                Solve (1)             |
                    |                 |
                    +--------+--------+
                             |
                      Satisfiability
```

(1) `Solve` also imports the helper `utils/Inspect`, and `Trans` the helper
`utils/Invariant`. (2) `Normalization` also imports the helper `utils/Dedupe`.

## Adding a rule

A rule is a record `Rule` bundling a relation on states, `step`, with the properties
every rule must have:

- `rule_equivalence: PreservesEquivalence step`: the formula only changes to an
  equivalent one. This is the invariant on the formula that soundness uses.
- `rule_well_formed: PreservesWellFormed step`: well-formed states stay well-formed.
- `rule_entails: PreservesEntails step`: the entailment invariant is preserved.
- `rule_decreasing: Decreasing step`: from a well-formed state, the termination
  measure decreases.
- `rule_model_final: ModelFinal step`: the rule cannot fire from a total model.

`Trans rs` only takes steps from a non-`fail` state, so `fail` is final whatever the
rules say about it. States do not carry well-formedness proofs and `Trans` does not
require them: well-formedness is an invariant (`derivation_well_formed`), and
termination is stated for derivations from well-formed states. Because the properties come with the rules, the general results
(`derivation_equivalent`, `derivation_entails`, `trans__state_lt`, …) hold for any
rule set. The exception is `trans_well_founded`/`strict_derivation_well_founded`,
which also need every rule to keep the formula (`KeepsFormula`), because the measure
is relative to a fixed formula.

A rule that keeps the formula preserves equivalence for free
(`keeps_formula_equivalence`); all current rules are of this kind.

To add a rule:

1. Create `rules/<Rule>.v` with the relation `<Rule>Step` as an inductive, prove its
   properties, and bundle them as `<Rule>: Rule`. Nothing imports the file yet, so this
   does not affect the rest of the development.
2. Import it in `Trans.v` and use it in a rule set, e.g. a new list next to `DPLL`.
3. For termination, prove that every rule of that set keeps the formula, as
   `dpll_keeps_formula` does for `DPLL`.

Adding the rule to `DPLL` itself also requires updating the DPLL-specific proofs that
case on its rules: `final_dpll_basic`, `final_unsat_refl` (only `Fail` reaches `fail`)
and `dpll_keeps_formula`.

## File index

Files are listed in dependency order: each file only depends on files above it.

### Utilities

General-purpose helpers in `utils/`, independent of the rest of the development.

| File                | Contents                                                                                                                        |
|---------------------|---------------------------------------------------------------------------------------------------------------------------------|
| `utils/EqB.v`       | The `EqB` typeclass for computational (Boolean) equality, with the notation `x =? y`.                                           |
| `utils/Inspect.v`   | `inspect`, a helper for keeping an equation when matching on a value in Equations definitions.                                  |
| `utils/Dedupe.v`    | `dedupe_by`, which removes duplicates from a list with respect to a Boolean relation.                                           |
| `utils/Invariant.v` | `clos_refl_trans_invariant`: a property preserved by every step of a relation is preserved by its reflexive-transitive closure. |

### Literals, clauses and formulas

| File       | Contents                                                                                                                                                                                                                            |
|------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Atom.v`   | `Atom` (propositional variables, as natural numbers), its `EqB` instance and `eqb` lemmas.                                                                                                                                          |
| `Lit.v`    | Literals `Lit` (`Pos`/`Neg` of an atom) with `extract`, their `EqB` instance and lemmas; `LitOrderType`, the ordering used for sets of literals; module `Neg` with negation `¬l` and its lemmas (`involutive`, `self_neqb_neg`, …). |
| `Clause.v` | `Clause`, a finite set (MSet) of literals, read as their disjunction, plus lemmas relating set equality to `exists_`/`for_all`.                                                                                                     |
| `CNF.v`    | `CNF`, a finite set of clauses, read as their conjunction; `l_in_f` (a literal or its negation occurs in a formula) with its characterisations.                                                                                     |

### Assignments, states and semantics

| File           | Contents                                                                                                                                                                                                                                                                                                                                                                                                    |
|----------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Assignment.v` | Partial assignments `PA`: lists of literals annotated as decision (`dec`) or propagation (`prop`), with the notations `m ++d l`, `m ++p l` and `m ++a n` (written so that the newest entries appear on the right); `NoDecisions`; `split_last_decision`, which splits off the most recent decision.                                                                                                         |
| `Evaluation.v` | Three-valued evaluation of literals, clauses and formulas under a partial assignment (`l_eval`, `c_eval`, `f_eval`) and their Boolean versions (`l_true`, `c_false`, …); `Def`/`Undef`; characterisations such as `c_eval_true_iff` and `f_eval_true_iff`; lemmas about removing a literal from a clause and extending an assignment with an undefined literal.                                             |
| `Model.v`      | `Model m f` (`m` makes `f` true); `unit_cnf l` (a literal as a formula) and `units m` (an assignment as one unit clause per literal); lemmas for models of unions, units and unit clauses; transferring falsity from an assignment to any model of it; semantic consequence `f ⊨ g` and equivalence `Equivalent f g` between formulas, with `equivalent_refl`/`_sym`/`_trans` and `model_union_equivalent`. |
| `State.v`      | States `State`: `fail`, or an assignment for a formula.                                                                                                                                                                                                                                                                                                                                                     |
| `WellFormed.v` | Well-formed states `WellFormed s`: `fail`, or an assignment for a formula with no atom assigned twice (`NoDuplicates`) and only atoms occurring in the formula (`Bounded`); lemmas about extending and restricting assignments; `initial_well_formed`.                                                                                                                                                      |

### Entailment

The entailment invariant says that every propagated literal on the trail follows
from the formula together with the literals before it, except pure literals, which
only preserve models.

| File        | Contents                                                                                                                                                                                                                                                                                                                                                                                                         |
|-------------|------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Entails.v` | The invariant `Entails f m`, built one trail entry at a time (`e_nil`, `e_decide`, `e_propagate`, `e_pure`); `entails_prefix` (the older part of an entailed trail is entailed) and `entails_extend` (a model of the formula and an entailed trail extends past propagated literals), used for soundness of `Fail` and `Backtrack`; `entails_equivalent` (entailment only depends on the models of the formula). |

### Termination measure

| File        | Contents                                                                                                                                                                                                                                                                                                                                                                                                   |
|-------------|------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Measure.v` | The termination measure: `score`, which records for each decision level how far the number of propagated literals is below a bound (one more than the largest atom of the formula), padded to a fixed length; the order `StateLt` (`s >>[f] s'`) on states, ordered lexicographically by score, with its well-foundedness (`state_lt_well_founded`); lemmas about how each kind of step changes the score. |

### The rules

| File     | Contents                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  |
|----------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Rule.v` | The properties of a relation on states: `KeepsFormula` (the rule never changes the formula), `PreservesEquivalence` (the rule only changes the formula to an equivalent one) with `keeps_formula_equivalence`, `PreservesWellFormed` (the rule keeps states well-formed), `PreservesEntails` (the rule preserves the entailment invariant, relative to the formula of each state), `Decreasing` (from a well-formed state, the rule decreases the termination measure), and `ModelFinal` (the rule cannot fire from a model that defines every literal of the formula); the record `Rule`, a relation (`step`) with all properties except `KeepsFormula`. |

Each file in `rules/` defines its relation `<Rule>Step` (`r_<rule>` is its only constructor),
proves its properties, and bundles them as `<Rule>: Rule`:

- `<rule>_keeps_formula: KeepsFormula <Rule>Step`, which gives `rule_equivalence` via
  `keeps_formula_equivalence` (and is used by `dpll_keeps_formula` for termination),
- `<rule>_well_formed: PreservesWellFormed <Rule>Step`,
- `<rule>_entails: PreservesEntails <Rule>Step`,
- `<rule>_state_lt: Decreasing <Rule>Step`,
- `<rule>_model_final: ModelFinal <Rule>Step`.

| File                | Rule                                                                                                                                                                                           |
|---------------------|------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `rules/Fail.v`      | `Fail`: all literals assigned with a conflict and no decisions; go to `fail`.                                                                                                                  |
| `rules/Unit.v`      | `Unit`: a clause is false except for one unassigned literal; propagate it.                                                                                                                     |
| `rules/Decide.v`    | `Decide`: assign an unassigned literal of the formula as a decision.                                                                                                                           |
| `rules/Backtrack.v` | `Backtrack`: on a conflict, flip the most recent decision. Also contains `backtrack_no_model` and `backtrack_neg`, which show that the flipped literal follows from the formula and the trail. |
| `rules/Pure.v`      | `Pure`: assign a literal whose negation does not occur in the formula.                                                                                                                         |

### The transition system

| File            | Contents                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    |
|-----------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Trans.v`       | `Trans rs`, the transition relation of a list of rules (`t_step`: a step of one of the rules from a non-`fail` state), with notations `s ==>[rs] s'`, `==>*[rs]`, `==>+[rs]`, and `==>`/`==>*`/`==>+` for the full system `DPLL` (of the bundled rules `Fail`, `Unit`, …); the smaller rule set `Basic`; `trans_rule`, `trans_union` and `trans_incl`; `derivation_invariant` (a property of assignments preserved by every transition between states is preserved by derivations, used for the `derivation_*` lemmas); final states `Final rs` and `final_dpll_basic`; `trans_well_formed`/`derivation_well_formed`; `trans_same_formula`/`derivation_same_formula` and `dpll_keeps_formula`; `trans_equivalent`/`derivation_equivalent`; `trans_entails`/`derivation_entails` (every transition and derivation preserves entailment); `fail_predecessor`. |
| `Termination.v` | `trans__state_lt`: every transition from a well-formed state decreases the measure; `WellFormedTrans rs`, the transitions from well-formed states, and `strict_derivation_well_formed_trans`, which turns a strict derivation from a well-formed state into one of these; from that, if every rule keeps the formula, `trans_well_founded` and `strict_derivation_well_founded`.                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |

### Normalization

| File              | Contents                                                                                                                                                                                                                                                                                                                                                                                            |
|-------------------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Normalization.v` | Turns any model of a formula into a final state reachable from the initial state: `totalize` (assign every undefined literal), `convert_prop` (make every literal a decision), `bound` (drop literals outside the formula), `dedupe` (remove duplicate atoms), and `normalize`, which combines them; each step's properties, and `normalize_derivation`. Used for completeness of `final_sat_refl`. |

### Strategy and solver

| File         | Contents                                                                                                                                                                                                                                                                                                                                                                 |
|--------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Strategy.v` | `Strategy next`: a step function that only takes `==>+` steps, never steps from `fail`, and only stops at final states of `Basic`; the search functions `find_conflict`, `find_unit`, `find_decision` (and helpers) with their specifications; `next_state`, one solver step, with `next_state_sound`, `next_state_none`, `next_state_exists` and `next_state_strategy`. |
| `Solve.v`    | `solve`: iterates a strategy until a final state, by well-founded recursion on `strict_derivation_well_founded` (every reachable state is well-formed, by `derivation_well_formed`); `solve_final_derivation` states that the result is reachable and final.                                                                                                             |

### Main results

| File               | Contents                                                        |
|--------------------|-----------------------------------------------------------------|
| `Satisfiability.v` | `Sat`, `Unsat` and `Total`, and the main theorems listed above. |
