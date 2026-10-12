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

The first five theorems are proved for each transition system, in `systems/<S>.v` for
`<S>` one of `Basic`, `DPLL` and `DPLL_BJ` (e.g. `DPLL.final_sat_refl`). For `DPLL_BJ`,
`final_model` assumes a well-formed entailed state, which every reachable state is.

| Theorem                          | File            | Statement (informally)                                              |
|----------------------------------|-----------------|---------------------------------------------------------------------|
| `final_exists`                   | `systems/<S>.v` | From the initial state, some final state is reachable.              |
| `final_model`                    | `systems/<S>.v` | A final state other than `fail` is a model of the formula.          |
| `final_sat_refl`                 | `systems/<S>.v` | A formula is satisfiable iff a final non-`fail` state is reachable. |
| `final_unsat_refl`               | `systems/<S>.v` | A formula is unsatisfiable iff `fail` is reachable.                 |
| `sat_decidable`                  | `systems/<S>.v` | Every formula is satisfiable or unsatisfiable.                      |
| `strict_derivation_well_founded` | `Termination.v` | There are no infinite derivations from well-formed states.          |
| `derivation_entails`             | `Trans.v`       | Every derivation preserves entailment.                              |
| `next_state_strategy`            | `Strategy.v`    | The concrete solver step is a valid strategy.                       |

## Module dependencies

Each module is drawn above the modules that import it. Only direct dependencies
are shown (an edge implied by a longer path is left out), and the six rule files
are grouped into one node, as are the three system files (each imports the one before
it). The helpers in `utils/` are left out.

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
              |     +-----+-----+     |
              |     |           |     |
              +--+--+           +--+--+
                 |                 |
               Solve        Satisfiability
                 |                 |
                 +--------+--------+
                          |
            systems/{Basic,DPLL,DPLL_BJ}
```

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
termination is stated for derivations from well-formed states. Because the
properties come with the rules, the general results (`derivation_equivalent`,
`derivation_entails`, `strict_derivation_well_founded`, …) hold for any rule set.
Rules may change the formula: a step that decreases the measure cannot increase the
largest atom of the formula (`state_lt_max_atom`), so every derivation is measured
against the formula it starts from.

A rule that keeps the formula preserves equivalence for free
(`preserves_formula_equivalence`); all current rules are of this kind.

To add a rule:

1. Create `rules/<Rule>.v` with the relation `<Rule>Step` as an inductive, prove its
   properties, and bundle them as `<Rule>: Rule`. Nothing imports the file yet, so this
   does not affect the rest of the development.
2. Import it in `Trans.v` and use it in a rule set, e.g. a new list next to `DPLL`.
3. To prove the main theorems for the new rule set, add `systems/<S>.v`. The generic
   theorems `sat_iff_final`, `unsat_iff_fail` and `sat_or_unsat` (`Satisfiability.v`)
   give them from four facts, taken as hypotheses: the rules include `Decide`, only
   `Fail` reaches `fail`, a final state is reachable (`final_exists`), and final
   well-formed entailed states are models (`final_model`). `systems/DPLL_BJ.v` shows
   how to get the last two from another system by relating their steps.

Adding the rule to an existing rule set also requires updating the proofs that case on
its rules, such as `trans_dpll_basic` and the `<s>_fail_only` lemma of its system.

## File index

Files are listed in dependency order: each file only depends on files above it.

### Utilities

General-purpose helpers in `utils/`, independent of the rest of the development.

| File                | Contents                                                                                                                        |
|---------------------|---------------------------------------------------------------------------------------------------------------------------------|
| `utils/EqB.v`       | The `EqB` typeclass for computational (Boolean) equality, with the notation `x =? y`.                                           |
| `utils/Member.v`    | The `Member` typeclass for membership, with the notations `x ∈ y` and `x ∉ y`.                                                  |
| `utils/Inspect.v`   | `inspect`, a helper for keeping an equation when matching on a value in Equations definitions.                                  |
| `utils/Dedupe.v`    | `dedupe_by`, which removes duplicates from a list with respect to a Boolean relation.                                           |
| `utils/Invariant.v` | `clos_refl_trans_invariant`: a property preserved by every step of a relation is preserved by its reflexive-transitive closure. |

### Literals, clauses and formulas

| File       | Contents                                                                                                                                                                                                                            |
|------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Atom.v`   | `Atom` (propositional variables, as natural numbers), its `EqB` instance and `eqb` lemmas.                                                                                                                                          |
| `Lit.v`    | Literals `Lit` (`Pos`/`Neg` of an atom) with `extract`, their `EqB` instance and lemmas; `LitOrderType`, the ordering used for sets of literals; module `Neg` with negation `¬l` and its lemmas (`involutive`, `self_neqb_neg`, …). |
| `Clause.v` | `Clause`, a finite set (MSet) of literals, read as their disjunction, with membership `l ∈ c`, plus lemmas relating set equality to `exists_`/`for_all`.                                                                            |
| `CNF.v`    | `CNF`, a finite set of clauses, read as their conjunction, with membership `c ∈ f` and `l ∈ f` (`l` occurs in some clause of `f`), and `mem_lit`, its Boolean version (`mem_lit_spec`).                                             |

### Assignments, states and semantics

| File           | Contents                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
|----------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Assignment.v` | Partial assignments `PA`: trails of propagated and decided literals (`empty`, `propagate`, `decide`), extended on the right. Trails are written left to right between `⟨ ⟩`: `⟨m, l⟩` propagates `l` and `⟨m; l⟩` decides `l` after `m`, `⟨m ++ n⟩` is `m` followed by `n`, `⟨⟩` is the empty trail, and a trail starting from it is written `⟨, l1, l2; l3⟩`. The list-like `PA.app`, `PA.In` and `PA.length`, used qualified, with `PA.In` as the `Member` instance (`l ∈ m`); `atoms`; `NoDecisions` and `NoPropagations`; `split_last_decision`, which splits off the most recent decision. |
| `Evaluation.v` | Three-valued evaluation of literals, clauses and formulas under a partial assignment (`l_eval`, `c_eval`, `f_eval`) and their Boolean versions (`l_true`, `c_false`, …); `Def`/`Undef`; characterisations such as `c_eval_true_iff` and `f_eval_true_iff`; lemmas about removing a literal from a clause and extending an assignment with an undefined literal; `l_eval_app_some` and `l_eval_app_undef` (in `⟨m ++ n⟩`, a literal has its value under `n`, or under `m` if `n` leaves it unassigned).                                                                                          |
| `Model.v`      | `Model m f` (`m` makes `f` true); `unit_cnf l` (a literal as a formula) and `units m` (an assignment as one unit clause per literal); `neg_clause m` (the clause of the negations of the literals of `m`); `model_singleton_iff`; lemmas for models of unions, units and unit clauses; transferring falsity from an assignment to any model of it; semantic consequence `f ⊨ g` and equivalence `Equivalent f g` between formulas, with `equivalent_refl`/`_sym`/`_trans` and `model_union_equivalent`.                                                                                         |
| `State.v`      | States `State`: `fail`, or an assignment for a formula.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
| `WellFormed.v` | Well-formed states `WellFormed s`: `fail`, or an assignment for a formula with no atom assigned twice (`NoDuplicates`) and only atoms occurring in the formula (`Bounded`); lemmas about extending and restricting assignments; `nodup_in_true` (without duplicates, every assigned literal is true); `initial_well_formed`.                                                                                                                                                                                                                                                                    |

### Entailment

The entailment invariant says that every propagated literal on the trail follows
from the formula together with the literals before it, except pure literals, which
only preserve models.

| File        | Contents                                                                                                                                                                                                                                                                                                                                                                                                         |
|-------------|------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Entails.v` | The invariant `Entails f m`, built one trail entry at a time (`e_nil`, `e_decide`, `e_propagate`, `e_pure`); `entails_prefix` (the older part of an entailed trail is entailed) and `entails_extend` (a model of the formula and an entailed trail extends past propagated literals), used for soundness of `Fail` and `Backtrack`; `entails_equivalent` (entailment only depends on the models of the formula). |

### Termination measure

| File        | Contents                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
|-------------|----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Measure.v` | The termination measure: `score`, which records for each decision level how far the number of propagated literals is below a bound (one more than the largest atom of the formula), padded to a fixed length; the order `StateLt` (`s >>[f] s'`) on states, which puts `fail` below every other state and otherwise compares lexicographically by score, then `score_total`, with its well-foundedness (`state_lt_well_founded`); `state_lt_incl` (the order grows with the largest atom of the formula) and `state_lt_max_atom` (a decreasing step never increases the largest atom); lemmas about how each kind of step changes the score. |

### The rules

| File     | Contents                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
|----------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Rule.v` | The properties of a relation on states: `PreservesFormula` (the rule never changes the formula), `PreservesEquivalence` (the rule only changes the formula to an equivalent one) with `preserves_formula_equivalence`, `PreservesWellFormed` (the rule keeps states well-formed), `PreservesEntails` (the rule preserves the entailment invariant, relative to the formula of each state), `Decreasing` (from a well-formed state, the rule decreases the termination measure), and `ModelFinal` (the rule cannot fire from a model that defines every literal of the formula); the record `Rule`, a relation (`step`) with all properties except `PreservesFormula`. |

Each file in `rules/` defines its relation `<Rule>Step` (`r_<rule>` is its only constructor),
proves its properties, and bundles them as `<Rule>: Rule`:

- `<rule>_same_formula: PreservesFormula <Rule>Step`, which gives `rule_equivalence` via
  `preserves_formula_equivalence`,
- `<rule>_well_formed: PreservesWellFormed <Rule>Step`,
- `<rule>_entails: PreservesEntails <Rule>Step`,
- `<rule>_state_lt: Decreasing <Rule>Step`,
- `<rule>_model_final: ModelFinal <Rule>Step`.

| File                | Rule                                                                                                                                                                                                                                                                                                                                                                                                                          |
|---------------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `rules/Fail.v`      | `Fail`: all literals assigned with a conflict and no decisions; go to `fail`.                                                                                                                                                                                                                                                                                                                                                 |
| `rules/Unit.v`      | `Unit`: a clause is false except for one unassigned literal; propagate it.                                                                                                                                                                                                                                                                                                                                                    |
| `rules/Decide.v`    | `Decide`: assign an unassigned literal of the formula as a decision.                                                                                                                                                                                                                                                                                                                                                          |
| `rules/Backtrack.v` | `Backtrack`: on a conflict, flip the most recent decision. Also contains `backtrack_no_model` and `backtrack_neg`, which show that the flipped literal follows from the formula and the trail.                                                                                                                                                                                                                                |
| `rules/Backjump.v`  | `Backjump`: on a conflict, go back to before some decision and propagate a literal of a clause that follows from the formula and whose other literals are false there. Also contains `backtrack_backjump` (from a well-formed entailed state, a Backtrack step is a Backjump step, with the clause of `¬l` and the negations of the literals before `l`) and `backjump_backtrack` (Backtrack applies whenever Backjump does). |
| `rules/Pure.v`      | `Pure`: assign a literal whose negation does not occur in the formula.                                                                                                                                                                                                                                                                                                                                                        |

### The transition system

| File            | Contents                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
|-----------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Trans.v`       | `Trans rs`, the transition relation of a list of rules (`t_step`: a step of one of the rules from a non-`fail` state), with notations `s ==>[rs] s'`, `==>*[rs]`, `==>+[rs]`, and `==>`/`==>*`/`==>+` for the full system `DPLL` (of the bundled rules `Fail`, `Unit`, …); the smaller rule set `Basic`; `DPLL_BJ`, which has `Backjump` in place of `Backtrack`; `trans_rule` and `trans_incl`; `derivation_invariant` (a property of assignments preserved by every transition between states is preserved by derivations, used for the `derivation_*` lemmas); final states `Final rs`, `trans_dpll_basic` (whenever DPLL steps, Basic steps) and `final_dpll_basic`; `trans_well_formed`/`derivation_well_formed`; `trans_equivalent`/`derivation_equivalent`; `trans_entails`/`derivation_entails` (every transition and derivation preserves entailment); `fail_predecessor`, for any rule set. |
| `Termination.v` | `trans__state_lt`: every transition from a well-formed state decreases the measure; `WellFormedTrans rs`, the transitions from well-formed states, and `strict_derivation_well_formed_trans`, which turns a strict derivation from a well-formed state into one of these; `trans_max_atom` and `max_atom_invariant`: the largest atom of the formula never increases along these transitions; from that, `trans_well_founded` and `strict_derivation_well_founded`, for any rule set.                                                                                                                                                                                                                                                                                                                                                                                                                 |

### Normalization

| File              | Contents                                                                                                                                                                                                                                                                                                                                                                                                                                             |
|-------------------|------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Normalization.v` | Turns any model of a formula into a final state reachable from the initial state: `totalize` (assign every undefined literal), `convert_prop` (make every literal a decision), `bound` (drop literals outside the formula), `dedupe` (remove duplicate atoms), and `normalize`, which combines them; each step's properties, and `normalize_derivation` (reachable with any rules that include `Decide`). Used for completeness of `final_sat_refl`. |

### Strategy and solver

| File         | Contents                                                                                                                                                                                                                                                                                                                                                                 |
|--------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Strategy.v` | `Strategy next`: a step function that only takes `==>+` steps, never steps from `fail`, and only stops at final states of `Basic`; the search functions `find_conflict`, `find_unit`, `find_decision` (and helpers) with their specifications; `next_state`, one solver step, with `next_state_sound`, `next_state_none`, `next_state_exists` and `next_state_strategy`. |
| `Solve.v`    | `solve`: iterates a strategy until a final state, by well-founded recursion on `strict_derivation_well_founded` (every reachable state is well-formed, by `derivation_well_formed`); `solve_final_derivation` states that the result is reachable and final.                                                                                                             |

### Main results

| File               | Contents                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
|--------------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Satisfiability.v` | `Sat`, `Unsat` and `Total`; for any rule set: `final_exists_progress` (if every reachable state steps or is final, a final state is reachable), `sat_final` (with `Decide`, a model gives a reachable final state) and `fail_unsat` (if only `Fail` steps to `fail`, reaching `fail` means unsatisfiable), `final_reachable_model`, and `sat_iff_final`, `unsat_iff_fail` and `sat_or_unsat`: the main theorems for any rule set, with the facts they need as hypotheses (see "Adding a rule"). |

### Transition systems

Each file in `systems/` proves the main theorems for one rule set, by instantiating
the generic theorems of `Satisfiability.v`.

| File                | Contents                                                                                                                                                                                                                                                                                                                                                                  |
|---------------------|---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `systems/Basic.v`   | `Basic` (`Fail`, `Decide`, `Backtrack`): `basic_fail_only`; `final_exists`, using `next_state` to tell whether a state is final; `final_model`, by finding a step from any state that is not a model; the main theorems.                                                                                                                                                  |
| `systems/DPLL.v`    | `DPLL` (`Fail`, `Unit`, `Decide`, `Backtrack`, `Pure`): `dpll_fail_only`; `final_exists`, by running the solver (`solve`); `final_model`, via `final_dpll_basic` and `Basic.final_model`; the main theorems.                                                                                                                                                              |
| `systems/DPLL_BJ.v` | `DPLL_BJ` (`DPLL` with `Backjump` in place of `Backtrack`): `dpll_bj_fail_only`; `trans_dpll_bj_dpll` and `trans_dpll_dpll_bj`, relating its steps to those of `DPLL` (the latter from well-formed entailed states); `final_basic_dpll_bj`; `final_exists`, from `next_state`; `final_model`, for well-formed entailed states, via `DPLL.final_model`; the main theorems. |
