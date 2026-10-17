# RocqSAT

A Rocq formalization of an abstract DPLL-style SAT transition system, proving soundness, completeness and
termination, together with a verified solver in C, compiled with CompCert. See
[`abstraction/README.md`](abstraction/README.md) for an overview of the formalization,
[`refinement/README.md`](refinement/README.md) for the concrete solver and its proofs, and
[`solver/`](solver/README.md) for the C program.

# Installation

1. Install **Opam** (tested with version 2.5.0).
2. Install the dependencies from the repository root:
    - `opam install . --deps-only`
3. Build **RocqSAT** with:
    - `dune build`
    - If `dune` is not on your `PATH`, run `eval $(opam env)` first.

# Running

The benchmark problems are not part of the repository; fetch them into `problems/` first (see
[Problems](#problems)):
```bash
./fetch_problems.sh
```
You can then run a problem from the repository root using:
```bash
dune exec rocqsat < problems/sat/satlib/hanoi/hanoi4.cnf
```
This runs the C solver of [`solver/`](solver/README.md), verified against `refinement/core/SolverStep.v` with
CompCert's semantics of C and compiled with CompCert (`ccomp`). It prints `UNSAT`, `SAT` followed by a model,
or `UNKNOWN` if it ran out of room.

# Problems

`./fetch_problems.sh` downloads the three assets of the `bench-v1` release, checks them against their SHA-256 and
unpacks them into `problems/` (ignored by git). The problems are in DIMACS CNF format, grouped by their status:
`problems/sat/` holds satisfiable problems and `problems/unsat/` unsatisfiable ones, each with a directory per
source and a directory per family below it. The status of every CNFgen and SATLIB problem was checked with an
independent solver (Kissat); the GBD problems are filed by the status GBD records.

| Location                                         | Problems | Release asset       | Source |
|--------------------------------------------------|---------:|---------------------|--------|
| `problems/sat/cnfgen/`, `problems/unsat/cnfgen/` |       55 | `cnfgen.tar.xz`     | CNFgen |
| `problems/sat/satlib/`, `problems/unsat/satlib/` |     9306 | `satlib-all.tar.xz` | SATLIB |
| `problems/sat/gbd/`, `problems/unsat/gbd/`       |      846 | `gbd.tar.xz`        | GBD    |

**CNFgen.** Crafted families generated with CNFgen 0.9.6 (https://massimolauria.net/cnfgen): pigeonhole
principle (`php`), ordering principle (`op`), parity principle (`parity`), mutilated chessboard (`mchess`), Tseitin
formulas on random 4-regular graphs (`tseitin`), and 3-colourability of random regular graphs (`kcolor`). The
comments at the start of each file give the command line and random seed that produced it. Cite CNFgen as:

> Massimo Lauria, Jan Elffers, Jakob Nordström and Marc Vinyals. CNFgen: A Generator of Crafted Benchmarks.
> SAT 2017, LNCS 10491, pages 464–473.

**SATLIB.** The benchmark problems of SATLIB (https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html): uniform random
3-SAT (`uf*`, `uuf*`), graph colouring (`flat*`, `sw100-*`, `gcp`), planning (`blocksworld`, `logistics`),
all-interval series (`ais`), quasigroups (`qg`), bounded model checking (`bmc`), the DIMACS families (`aim`,
`lran`, `jnh`, `dubois`, `parity`, `ii`, `hanoi`, `bf`, `ssa`, `pigeon-hole`, `pret`) and the Beijing SAT
competition problems (`beijing`). The comments in each file name its original contributor. Cite SATLIB as:

> Holger H. Hoos and Thomas Stützle. SATLIB: An Online Resource for Research on SAT. In I. P. Gent, H. van Maaren
> and T. Walsh (editors), SAT 2000, pages 283–292, IOS Press, 2000.

The release has them normalized, repairing a few formatting errors of the original files: the `%` trailer at the
end of the random 3-SAT and graph colouring files is removed, as is the lone `0` line at the end of the `pret`
files (an unintended empty clause), and the 202 clauses of `dubois100` that lack their terminating `0` (one clause
per line) get one. The status of 12 problems could not be checked within 10 minutes (`par32-*`, `g125.17` and
`g250.29`); those are filed as SATLIB documents them. The script that built the asset from the original archives
is `problems/fetch_satlib.py` in commit `5e45497`.

**GBD.** SAT competition problems from the Global Benchmark Database (https://benchmark-database.de), chosen
for benchmarking the solver: problems with a known status, at most 8000 variables and 150000 clauses, a few per
family spread over their sizes, and more of the families whose problems take the solver seconds rather than
milliseconds or minutes. Each file is named by its GBD hash; GBD gives its original name, author and competition
track. The files are as GBD serves them. Cite GBD as:

> Ashlin Iser and Christoph Jabs. Global Benchmark Database. SAT 2024, LIPIcs, article 18.
> https://doi.org/10.4230/LIPIcs.SAT.2024.18

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
