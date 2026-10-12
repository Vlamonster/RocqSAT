#!/bin/bash
# Check the VST proofs of the C solver (needs coq-vst and coq-compcert, so it is not part of dune build): generate
# the Clight of ../solver.c, then compile the proofs against the RocqSAT build (run dune build first).
set -e
cd "$(dirname "$(readlink -f "$0")")"
mkdir -p ../_clight
cp ../solver.c ../solver.h ../_clight/
(cd ../_clight && clightgen -normalize solver.c)
for f in ../_clight/solver.v Spec.v; do
  echo "== $f"
  rocq c -Q ../_clight RocqSATClight -Q . RocqSATC -R ../../_build/default/verification RocqSAT "$f"
done
