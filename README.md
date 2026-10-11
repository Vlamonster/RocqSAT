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
dune exec rocqsat < problems/<problem>.cnf
```
This rebuilds the solver from the proofs first if anything changed. It prints `UNSAT`, or `SAT` followed by a
model.

The problems in `problems/`, with a time limit of 3 minutes (all problems run in parallel on a 12-core
machine):

| Problem             | Variables | Clauses | Result  | Time    |
|---------------------|----------:|--------:|---------|--------:|
| `trivial.cnf`       |         1 |       1 | SAT     | < 0.01s |
| `trivial2.cnf`      |         1 |       2 | UNSAT   | < 0.01s |
| `simple.cnf`        |         3 |       2 | SAT     | < 0.01s |
| `tutorial.cnf`      |         5 |       5 | SAT     | < 0.01s |
| `test.cnf`          |         6 |      15 | SAT     | < 0.01s |
| `hole6.cnf`         |        42 |     133 | UNSAT   |   0.06s |
| `zebra.cnf`         |       155 |    1135 | SAT     |   0.04s |
| `queens16.cnf`      |       256 |    6336 | SAT     |   0.28s |
| `hanoi4.cnf`        |       718 |    4934 | SAT     |     51s |
| `factor1234321.cnf` |      1433 |    7585 | SAT     |    153s |
| `bf.cnf`            |      1040 |    3668 | timeout |       - |
| `factor1235321.cnf` |      1433 |    7585 | timeout |       - |
| `subsets100.cnf`    |      3357 |   15212 | timeout |       - |

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
