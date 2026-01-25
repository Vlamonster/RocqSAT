# Installation

1. Install **Opam** (tested with version 2.5.0).  
2. Enter the `/code` directory and install dependencies: 
    - `opam install . --deps-only`
3. If you want to work with **VSRocq** (tested with version 2.3.3): 
    - `opam install vsrocq-language-server`
4. Finally, build **RocqSAT** with:
    - `opam exec -- dune build`

# Running
You can run a problem from the `/code` directory using:
```bash
cat ./problems/<problem>.cnf | opam exec -- dune exec ./runner/runner.exe
```
The following problems can be solved within a reasonable time:
- test.cnf (SAT)
- tutorial.cnf (SAT)
- trivial.cnf (SAT)
- trivial2.cnf (UNSAT)
- simple.cnf (SAT)
- hole6.cnf (UNSAT)
- zebra.cnf (SAT)
