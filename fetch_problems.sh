#!/bin/sh
# Download the benchmark problems from the bench-v1 release into problems/ (ignored by git), checking each
# asset against its SHA-256: SATLIB into problems/<status>/satlib/<family> and CNFgen into
# problems/<status>/cnfgen/<family>, where <status> is sat or unsat. Existing families are replaced. See the
# README for the sources.
set -eu
cd "$(dirname "$0")"
release=https://github.com/Vlamonster/RocqSAT/releases/download/bench-v1
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# fetch <asset> <sha256> <directory name in the asset> <directory name in problems/>
fetch() {
  curl -fsSL -o "$tmp/$1" "$release/$1"
  echo "$2  $tmp/$1" | sha256sum -c --quiet -
  mkdir -p "$tmp/unpacked"
  tar -xJf "$tmp/$1" -C "$tmp/unpacked"
  for status in sat unsat; do
    if [ -d "$tmp/unpacked/$status/$3" ]; then
      mkdir -p "problems/$status"
      rm -rf -- "problems/$status/$4"
      mv "$tmp/unpacked/$status/$3" "problems/$status/$4"
    fi
  done
  rm -rf -- "$tmp/unpacked"
  echo "$1: $(find problems/sat/"$4" problems/unsat/"$4" -name '*.cnf' 2>/dev/null | wc -l) problems"
}

fetch satlib-all.tar.xz 76bd75409b9ca814f81fec92b54d26f795228479f7cc929f8320fb50d6ddfac1 satlib-all satlib
fetch cnfgen.tar.xz b2326e7180939beea6d7d0676c0daf458d383fd4bb150adbdaf57191a31c7482 cnfgen cnfgen
