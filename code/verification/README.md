# RocqSAT verification

A Rocq formalization of an abstract DPLL-style transition system for SAT solving, proving:

- **soundness**: a final non-`fail` state is a model, and reaching `fail` means unsatisfiable;
- **completeness**: every formula reaches one of the two;
- **termination**: there are no infinite derivations.

It also gives a concrete, verified strategy and derives decidability of satisfiability.

- Build from `code/` with `dune build`.
- The library is `RocqSAT`; subdirectories are qualified, e.g. `From RocqSAT.rules Require Import Unit.`

## Main results

- The first five theorems hold for each system `<S>` in `Basic`, `DPLL` and `DPLL_BJ`
  (e.g. `DPLL.final_sat_refl`).
- `DPLL_BJ.final_model` assumes a well-formed entailed state; every reachable state is one.

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

- Each module is drawn above the modules that import it; implied edges are left out.
- The rule files form one node, as do the system files (each imports the one before it).
- `utils/` is left out.

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

### Transition system

- `Trans.v`:
  - `Trans rs` (`s ==>[rs] s'`, `==>*[rs]`, `==>+[rs]`; `==>` etc. for `DPLL`);
  - rule sets `DPLL`, `Basic`, `DPLL_BJ`;
  - `Final rs`, `trans_dpll_basic`, `final_dpll_basic`;
  - `derivation_invariant` and the `trans_*`/`derivation_*` lemmas for well-formedness,
    equivalence and entailment;
  - `fail_predecessor`.
- `Termination.v`: every transition from a well-formed state decreases the measure;
  `trans_well_founded`, `strict_derivation_well_founded`, for any rule set.

### Normalization

- `Normalization.v`: turns a model into a reachable final state (`totalize`,
  `convert_prop`, `bound`, `dedupe`, `normalize`); `normalize_derivation` needs `Decide`.

### Strategy and solver

- `Strategy.v`: `Strategy next`; `find_conflict`, `find_unit`, `find_decision`; `next_state`
  with `next_state_sound`, `next_state_none`, `next_state_exists`, `next_state_strategy`.
- `Solve.v`: `solve` iterates a strategy by well-founded recursion;
  `solve_final_derivation`.

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

- `Basic.v` (`Fail`, `Decide`, `Backtrack`): `final_exists` via `next_state`; `final_model`
  by finding a step from any non-model.
- `DPLL.v` (`Fail`, `Unit`, `Decide`, `Backtrack`, `Pure`): `final_exists` by running
  `solve`; `final_model` via `Basic.final_model`.
- `DPLL_BJ.v` (`DPLL` with `Backjump` for `Backtrack`): `trans_dpll_bj_dpll`,
  `trans_dpll_dpll_bj`, `final_basic_dpll_bj`; `final_exists` via `next_state`;
  `final_model` via `DPLL.final_model`.
