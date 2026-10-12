# RocqSAT

A Rocq formalization of an abstract DPLL-style SAT transition system, proving soundness, completeness and
termination, together with a verified solver extracted to OCaml. See
[`verification/README.md`](verification/README.md) for an overview of the formalization.

# Installation

1. Install **Opam** (tested with version 2.5.0).
2. Install the dependencies from the repository root:
    - `opam install . --deps-only`
3. Build **RocqSAT** with:
    - `dune build`
    - If `dune` is not on your `PATH`, run `eval $(opam env)` first.

# Running

You can run a problem from the repository root using:
```bash
dune exec rocqsat < problems/sat/satlib/hanoi/hanoi4.cnf
```
This rebuilds the solver from the proofs first if anything changed. It prints `UNSAT`, or `SAT` followed by a
model. The problems are grouped by status in `problems/sat` and `problems/unsat`; see
[`problems/README.md`](problems/README.md) for their sources.

# Editor support

To work with **VSRocq** (tested with version 2.5.0), install its language server with
`opam install vsrocq-language-server` and open the repository root in VS Code. The snippets in
`.vscode/rocq.code-snippets` then insert the Unicode symbols of the notations:

| Prefix           | Symbol | Meaning                      |
|------------------|--------|------------------------------|
| `\<`             | `⟨`    | start of a trail             |
| `\>`             | `⟩`    | end of a trail               |
| `\tr`            | `⟨…⟩`  | a trail                      |
| `\in`            | `∈`    | membership                   |
| `\notin`         | `∉`    | non-membership               |
| `\neg` or `\not` | `¬`    | negation of a literal        |
| `\models`        | `⊨`    | model of a formula           |
| `\empty`         | `∅`    | the empty trail inside `⟨ ⟩` |
