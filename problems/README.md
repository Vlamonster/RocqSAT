# Problems

SAT problems in DIMACS CNF format, grouped by their status: `sat/` holds satisfiable problems and `unsat/`
unsatisfiable ones, each with a directory per source and a directory per family below it. The status of every
problem was checked with an independent solver (Kissat).

| Location                               | Problems | In the repository | Source                                    |
|----------------------------------------|---------:|-------------------|-------------------------------------------|
| `sat/cnfgen/`, `unsat/cnfgen/`         |       55 | yes               | CNFgen                                    |
| `sat/satlib/`, `unsat/satlib/`         |      118 | yes               | SATLIB, the problems used by `bench/`     |
| `sat/satlib-all/`, `unsat/satlib-all/` |     9306 | no                | SATLIB, fetched by `fetch_satlib.py`      |

## CNFgen

Crafted families generated with CNFgen 0.9.6 (https://massimolauria.net/cnfgen): pigeonhole principle (`php`),
ordering principle (`op`), parity principle (`parity`), mutilated chessboard (`mchess`), Tseitin formulas on random
4-regular graphs (`tseitin`), and 3-colourability of random regular graphs (`kcolor`). The comments at the start of
each file give the command line and random seed that produced it. Cite CNFgen as:

> Massimo Lauria, Jan Elffers, Jakob Nordström and Marc Vinyals. CNFgen: A Generator of Crafted Benchmarks.
> SAT 2017, LNCS 10491, pages 464–473.

## SATLIB

The benchmark problems of SATLIB (https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html): uniform random 3-SAT
(`uf*`, `uuf*`), graph colouring (`flat*`, `sw100-*`, `gcp`), planning (`blocksworld`, `logistics`), all-interval
series (`ais`), quasigroups (`qg`), bounded model checking (`bmc`), the DIMACS families (`aim`, `lran`, `jnh`,
`dubois`, `parity`, `ii`, `hanoi`, `bf`, `ssa`, `pigeon-hole`, `pret`) and the Beijing SAT competition problems
(`beijing`). The comments in each file name its original contributor. Cite SATLIB as:

> Holger H. Hoos and Thomas Stützle. SATLIB: An Online Resource for Research on SAT. In I. P. Gent, H. van Maaren
> and T. Walsh (editors), SAT 2000, pages 283–292, IOS Press, 2000.

The full collection is not part of this repository. It is attached, normalized, to the `bench-v1` release
(`satlib-all.tar.xz`, 19 MB, 184 MB unpacked); fetch it with

```bash
python3 problems/fetch_satlib.py                         # the release, checked against its SHA-256
python3 problems/fetch_satlib.py --from-satlib uf50-218  # or rebuild from the original SATLIB archives
```

The script repairs a few formatting errors in the original files, which the copies in `satlib/` share: the `%`
trailer at the end of the random 3-SAT and graph colouring files is removed, as is the lone `0` line at the end of
the `pret` files (an unintended empty clause), and the 202 clauses of `dubois100` that lack their terminating `0`
(one clause per line) get one. The status of 12 problems of the full collection could not be checked within 10
minutes (`par32-*`, `g125.17` and `g250.29`); those are filed as SATLIB documents them.
