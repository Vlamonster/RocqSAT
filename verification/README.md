# RocqSAT verification

A Rocq formalization of an abstract, DPLL-style transition system for SAT solving.
It proves that the system is **sound** (a final state that is not `fail` gives a
model, and reaching `fail` means the formula is unsatisfiable), **complete**
(every formula ends up in one of the two), and **terminating** (no infinite
derivations). It also implements a concrete strategy, proves that it follows the
system, and derives decidability of satisfiability.

Build everything from the repository root with:

```sh
dune build
```

The files are compiled as the library `RocqSAT`. Files in a subdirectory are
qualified by that directory, e.g. `From RocqSAT.rules Require Import Unit.`

## Main results

| Theorem                          | File                     | Statement (informally)                                                     |
|----------------------------------|--------------------------|----------------------------------------------------------------------------|
| `final_exists`                   | `Satisfiability.v`       | From the initial state, some final state is reachable.                     |
| `final_model`                    | `Satisfiability.v`       | A final state other than `fail` is a model of the formula.                 |
| `final_sat_refl`                 | `Satisfiability.v`       | A formula is satisfiable iff a final non-`fail` state is reachable.        |
| `final_unsat_refl`               | `Satisfiability.v`       | A formula is unsatisfiable iff `fail` is reachable.                        |
| `sat_decidable`                  | `Satisfiability.v`       | Every formula is satisfiable or unsatisfiable.                             |
| `strict_derivation_well_founded` | `Termination.v`          | There are no infinite derivations from well-formed states.                 |
| `derivation_entails`             | `Trans.v`                | Every derivation preserves entailment.                                     |
| `next_state_strategy`            | `refinement/NextState.v` | The concrete solver step is a valid strategy. **Uses axioms** (see below). |

**Axioms.** All results are closed under the global context, except `next_state_strategy` and the solver
built from it. The refinement stores the values and occurrences in primitive arrays (`PArray`) for
constant-time access, so it depends on the axioms that specify primitive arrays and 63-bit integers
(Corelib's `ArrayAxioms` and `Uint63Axioms`, together with the primitives `PrimArray.*` and `PrimInt63.*`).
`Print Assumptions next_state_strategy` lists them. The extracted solver also relies on the OCaml
implementations of these primitives (`Parray`, `Uint63`) and on extracting `nat_index` to `Uint63.of_int`.
The main results in `Satisfiability.v` and `Termination.v` do not depend on the refinement and use no axioms.

## Module dependencies

Each module is drawn above the modules that import it. Only direct dependencies
are shown (an edge implied by a longer path is left out), and the five rule files
are grouped into one node. The helpers in `utils/` are left out.

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
          rules/{Fail,Unit,Decide,Backtrack,Pure}
                          |
                        Trans
              +-----------+-----------+
              |           |           |
          Strategy   Termination  Normalization
              |           |           |
              |           +-----+-----+
              |                 |
       refinement         Satisfiability
```

`Solve` (on `Strategy` and `Termination`) runs a strategy until it stops; only the solver
in `runner/` uses it.

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

Adding the rule to `DPLL` itself also requires updating the DPLL-specific proofs that
case on its rules: `final_dpll_basic`, `final_unsat_refl` (only `Fail` reaches `fail`)
and `dpll_same_formula`.

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
| `Evaluation.v` | Three-valued evaluation of literals, clauses and formulas under a partial assignment (`l_eval`, `c_eval`, `f_eval`) and their Boolean versions (`l_true`, `c_false`, …); `Def`/`Undef`; characterisations such as `c_eval_true_iff` and `f_eval_true_iff`; lemmas about removing a literal from a clause and extending an assignment with an undefined literal.                                                                                                                                                                                                                                 |
| `Model.v`      | `Model m f` (`m` makes `f` true); `unit_cnf l` (a literal as a formula) and `units m` (an assignment as one unit clause per literal); lemmas for models of unions, units and unit clauses; transferring falsity from an assignment to any model of it; semantic consequence `f ⊨ g` and equivalence `Equivalent f g` between formulas, with `equivalent_refl`/`_sym`/`_trans` and `model_union_equivalent`.                                                                                                                                                                                     |
| `State.v`      | States `State`: `fail`, or an assignment for a formula.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
| `WellFormed.v` | Well-formed states `WellFormed s`: `fail`, or an assignment for a formula with no atom assigned twice (`NoDuplicates`) and only atoms occurring in the formula (`Bounded`); lemmas about extending and restricting assignments; `initial_well_formed`.                                                                                                                                                                                                                                                                                                                                          |

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
  `preserves_formula_equivalence` (and is used by `dpll_same_formula`),
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

| File            | Contents                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
|-----------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Trans.v`       | `Trans rs`, the transition relation of a list of rules (`t_step`: a step of one of the rules from a non-`fail` state), with notations `s ==>[rs] s'`, `==>*[rs]`, `==>+[rs]`, and `==>`/`==>*`/`==>+` for the full system `DPLL` (of the bundled rules `Fail`, `Unit`, …); the smaller rule set `Basic`; `trans_rule`, `trans_union` and `trans_incl`; `derivation_invariant` (a property of assignments preserved by every transition between states is preserved by derivations, used for the `derivation_*` lemmas); final states `Final rs`, `final_dpll_basic` and `final_or_step` (every state is final for `Basic` or has a `Basic` step); `trans_well_formed`/`derivation_well_formed`; `trans_same_formula`/`derivation_same_formula` and `dpll_same_formula`; `trans_equivalent`/`derivation_equivalent`; `trans_entails`/`derivation_entails` (every transition and derivation preserves entailment); `fail_predecessor`. |
| `Termination.v` | `trans__state_lt`: every transition from a well-formed state decreases the measure; `WellFormedTrans rs`, the transitions from well-formed states, and `strict_derivation_well_formed_trans`, which turns a strict derivation from a well-formed state into one of these; `trans_max_atom` and `max_atom_invariant`: the largest atom of the formula never increases along these transitions; from that, `trans_well_founded` and `strict_derivation_well_founded`, for any rule set.                                                                                                                                                                                                                                                                                                                                                                                                                                                |

### Normalization

| File              | Contents                                                                                                                                                                                                                                                                                                                                                                                            |
|-------------------|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Normalization.v` | Turns any model of a formula into a final state reachable from the initial state: `totalize` (assign every undefined literal), `convert_prop` (make every literal a decision), `bound` (drop literals outside the formula), `dedupe` (remove duplicate atoms), and `normalize`, which combines them; each step's properties, and `normalize_derivation`. Used for completeness of `final_sat_refl`. |

### Strategy and solver

| File         | Contents                                                                                                                                                                                                                                                                                                                  |
|--------------|---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `Strategy.v` | `Strategy Inv next`: a step function `next: State * Ctx -> option (State * Ctx)` that carries a context of its own choosing, kept consistent with the state by the invariant `Inv`; it never steps from `fail`, only stops at final states of `Basic`, and only takes `==>+` steps that preserve `Inv`; `strategy_trans`. |
| `Solve.v`    | `solve`: iterates a strategy from an initial context until a final state, by well-founded recursion on `strict_derivation_well_founded` (every reachable state is well-formed, by `derivation_well_formed`); `solve_final_derivation` states that the result is reachable and final.                                      |

### Refinement

A concrete strategy in `refinement/`, implemented efficiently and proved to agree with the specification.
Its tables are primitive arrays, so it **depends on the `PArray` and `Uint63` axioms** (see Axioms above).

| File                     | Contents                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    |
|--------------------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `refinement/Table.v`     | `Table A`, a table from natural numbers backed by a primitive array (`PArray`) for constant-time access, with an AVL map (`AtomMap`) for keys that do not fit; `tget`, `tset` and `tmake` with `tget_tset_same`, `tget_tset_other` and `tget_tmake`; `nat_index`, extracted to `Uint63.of_int`. **Depends on the `ArrayAxioms` and `Uint63Axioms`.**                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| `refinement/Lookup.v`    | `Values`, a table from atoms to the value they were assigned most recently, `set_value`, and `values sz m`, the values of a trail; `lookup` and `c_lookup`, which evaluate literals and clauses through such a table, with `lookup_values` and `c_lookup_values` (they agree with `l_eval` and `c_eval`), and how setting a value changes a lookup (`lookup_add_self`, `lookup_add_other`).                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| `refinement/Search.v`    | `formula_lits`, the literals of a formula; `skip_assigned`, which drops the assigned literals from the front of a list, and `Cursor v f ls` (`ls` are literals of `f` and include all unassigned ones), which it preserves (`skip_assigned_cursor`) as does assigning a literal (`cursor_set_value`); `Settled v c` (a true literal or two unassigned ones: neither false nor unit).                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| `refinement/Watches.v`   | Two watched literals: the clause table (each clause with its literals), the watch table and the watch lists, all `Table`s; `WatchStruct` (every clause watches two of its literals and is in their watch lists or pending under them) and `WatchOK` (a watch is true, or both are distinct and unassigned), which implies `Settled`; `repair`, which moves false watches (`repair_spec`, `repair_settled`); `visit`, which repairs the watchers of a false literal and rebuilds its watch list in one pass (`visit_spec`), and `process`, which visits the pending false literals until a clause is stuck (`process_spec`), so it is false or unit (`stuck_unsettled`, `unsettled_unit`, `unsettled_conflict`); and the initial watches (`index_clauses`).                                                                                                                                                                                                                                                                                                                                                  |
| `refinement/NextState.v` | `next_state`, one solver step with two watched literals per clause. Its context (`SolverContext`) holds the values of the trail, the clauses with their literals, the literals still to decide on (a cursor into the literals of the formula, so a decision does not rescan the assigned ones), the watches and watch lists, a queue of false literals with the watchers still to visit, and snapshots of the values, watches and cursor before each decision; the tables are sized by the formula (`value_size`, `key_size`). A stuck clause gives its unit literal as the first literal that is not false, or else a conflict. `CoreInv` says every clause that is not pending has fine watches, so assigning `l` only queues the watchers of `¬l` (`assign_inv`); `SavedOK` says the snapshots are those before each decision, when all watches were fine, so a backtrack restores them and only queues the watchers of the flipped literal; `next_state_sound`, `next_state_none`, `next_state_exists` and `next_state_inv`, giving `next_state_strategy`; `initial_context` and `initial_context_inv`. |

### Main results

| File               | Contents                                                                                                                                          |
|--------------------|---------------------------------------------------------------------------------------------------------------------------------------------------|
| `Satisfiability.v` | `Sat`, `Unsat` and `Total` and the main theorems listed above, with `final_exists` by well-founded induction on `strict_derivation_well_founded`. |
