# Installation

1. Install **Opam** (tested with version 2.5.0).  
2. Enter the `/code` directory and install dependencies: 
    - `opam install . --deps-only`
3. If you want to work with **VSRocq** (tested with version 2.3.3): 
    - `opam install vsrocq-language-server`
    - Open the repository root in VS Code to get the snippets in `.vscode/rocq.code-snippets` for the notation symbols: `\<` `⟨`, `\>` `⟩`, `\tr` `⟨…⟩`, `\in` `∈`, `\notin` `∉`, `\neg` `¬`, `\models` `⊨`, `\empty` `∅`.
4. Finally, build **RocqSAT** with:
    - `dune build`
    - If `dune` is not on your `PATH`, run `eval $(opam env)` first.

# Running
You can run a problem from the `/code` directory using:
```bash
dune exec rocqsat < problems/<problem>.cnf
```
This rebuilds the solver from the proofs first if anything changed.

The following problems can be solved within a reasonable time:
- test.cnf (SAT)
- tutorial.cnf (SAT)
- trivial.cnf (SAT)
- trivial2.cnf (UNSAT)
- simple.cnf (SAT)
- hole6.cnf (UNSAT)
- zebra.cnf (SAT)
