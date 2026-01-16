# Requirements
| Package                     | Version      |
|-----------------------------|--------------|
| rocq-stdlib                 | 9.0.0        |
| rocq-prover                 | 9.0.0        |
| rocq-core                   | 9.0.1        |
| rocq-runtime                | 9.0.1        |
| rocq-equations              | 1.3.1+9.0    |
| vsrocq-language-server      | 2.3.3        |
| dune                        | 3.20.2       |

There are no guarantees that deviating from these versions will allow the project to build.

# Usage
You can build **RocqSAT** from the `/code` directory using:
```bash
dune build
```
You can run a problem from the `/code` directory using:
```bash
cat ./problems/<problem>.cnf | dune exec ./runner/runner.exe
```
The following problems can be solved within a reasonable time:
- test.cnf (SAT)
- tutorial.cnf (SAT)
- trivial.cnf (SAT)
- trivial2.cnf (UNSAT)
- simple.cnf (SAT)
- hole6.cnf (UNSAT)
- zebra.cnf (SAT)
