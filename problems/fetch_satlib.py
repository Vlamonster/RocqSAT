#!/usr/bin/env python3
"""Fetch all SATLIB benchmark problems (https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html) into
sat/satlib-all/<family> and unsat/satlib-all/<family>, which git ignores. The problems used by the benchmarks are
already in sat/satlib and unsat/satlib; see README.md for the sources and how to cite them.

By default the normalized collection is downloaded from the bench-v1 release of this repository and checked
against its SHA-256. With --from-satlib it is rebuilt from the original SATLIB archives instead; that is how the
release asset was made:

    python3 fetch_satlib.py --from-satlib
    tar --sort=name --mtime=@0 --owner=0 --group=0 --numeric-owner -cf - sat/satlib-all unsat/satlib-all \
        | xz -9e -T1 > satlib-all.tar.xz

Every file is normalized: the '%' trailer of some files is dropped, as are lone '0' lines past the declared number
of clauses (an unintended empty clause), and in files where some clauses lack their terminating 0 but each line is
one clause (dubois100) the 0 is added. The status of every problem was checked with an independent solver; it
agrees with the descriptions on the SATLIB pages.

Usage: python3 fetch_satlib.py                         (the release, all families)
       python3 fetch_satlib.py --from-satlib [family ...]  (all families when none is given)
"""
import hashlib
import io
import os
import sys
import tarfile
import urllib.request

BASE = "https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/"
RELEASE = "https://github.com/Vlamonster/RocqSAT/releases/download/bench-v1/satlib-all.tar.xz"
SHA256 = "76bd75409b9ca814f81fec92b54d26f795228479f7cc929f8320fb50d6ddfac1"
HERE = os.path.dirname(os.path.abspath(__file__))

# Family name, archive path below BASE, and status: "sat", "unsat", or a function from file name to status.
RANDOM = [(f"{p}{n}-{m}", f"RND3SAT/{p}{n}-{m}.tar.gz", "sat" if p == "uf" else "unsat")
          for n, m in [(20, 91), (50, 218), (75, 325), (100, 430), (125, 538), (150, 645), (175, 753), (200, 860),
                       (225, 960), (250, 1065)]
          for p in ["uf", "uuf"] if (p, n) != ("uuf", 20)]
FLAT = [(f"flat{n}-{m}", f"GCP/flat{n}-{m}.tar.gz", "sat")
        for n, m in [(30, 60), (50, 115), (75, 180), (100, 239), (125, 301), (150, 360), (175, 417), (200, 479)]]
MORPHED = [(f"sw100-8-{p}-c5", f"SW-GCP/sw100-8-{p}-c5.tar.gz", "sat")
           for p in [f"lp{i}" for i in range(9)] + ["p0"]]

JNH_UNSAT = {2, 3, 4, 5, 6, 8, 9, 10, 11, 13, 14, 15, 16, 18, 19, 20, 202, 203, 206, 208, 211, 214, 215, 216, 219,
             302, 303, 304, 305, 306, 307, 308, 309, 310}
QG_UNSAT = {"qg3-09", "qg4-08", "qg5-09", "qg5-10", "qg5-12", "qg5-13", "qg6-10", "qg6-11", "qg6-12", "qg7-10",
            "qg7-11", "qg7-12"}

FAMILIES = RANDOM + FLAT + MORPHED + [
    ("blocksworld", "PLANNING/BlocksWorld/blocksworld.tar.gz", "sat"),
    ("logistics", "PLANNING/Logistics/logistics.tar.gz", "sat"),
    ("ais", "AIS/ais.tar.gz", "sat"),
    ("qg", "QG/QG.tar.gz", lambda name: "unsat" if name in QG_UNSAT else "sat"),
    ("bmc", "BMC/bmc.tar.gz", "sat"),
    ("aim", "DIMACS/AIM/aim.tar.gz", lambda name: "unsat" if "-no-" in name else "sat"),
    ("lran", "DIMACS/LRAN/f.tar.gz", "sat"),
    ("jnh", "DIMACS/JNH/jnh.tar.gz", lambda name: "unsat" if int(name[3:]) in JNH_UNSAT else "sat"),
    ("dubois", "DIMACS/DUBOIS/dubois.tar.gz", "unsat"),
    ("gcp", "DIMACS/GCP/gcp-large.tar.gz", "sat"),
    ("parity", "DIMACS/PARITY/parity.tar.gz", "sat"),
    ("ii", "DIMACS/II/inductive-inference.tar.gz", "sat"),
    ("hanoi", "DIMACS/HANOI/hanoi.tar.gz", "sat"),
    ("bf", "DIMACS/BF/bf.tar.gz", "unsat"),
    ("ssa", "DIMACS/SSA/ssa.tar.gz", lambda name: "sat" if name.startswith("ssa7552") else "unsat"),
    ("pigeon-hole", "DIMACS/PHOLE/pigeon-hole.tar.gz", "unsat"),
    ("pret", "DIMACS/PRET/pret.tar.gz", "unsat"),
    ("beijing", "Bejing/Bejing.tar.gz", lambda name: "unsat" if name == "2bitadd_10" else "sat"),
]


def normalize(text):
    """The DIMACS text of a SATLIB file, repaired as described above."""
    lines = []
    for line in text.splitlines():
        if line.startswith("%"):
            break
        lines.append(line.rstrip())
    header = next(i for i, line in enumerate(lines) if line.startswith("p"))
    clauses = int(lines[header].split()[3])
    body = [line for line in lines[header + 1:] if line.strip() and not line.startswith("c")]
    ends = sum(line.split().count("0") for line in body)
    while ends > clauses and body and body[-1].strip() == "0":
        body.pop()
        ends -= 1
    if ends < clauses and len(body) == clauses:
        body = [line if line.split()[-1] == "0" else line + " 0" for line in body]
        ends = clauses
    if ends != clauses:
        raise ValueError(f"{ends} clauses, {clauses} declared")
    return "\n".join(lines[:header + 1] + body) + "\n"


def fetch(family, path, status):
    """Download and unpack one family."""
    with urllib.request.urlopen(BASE + path) as response:
        archive = tarfile.open(fileobj=io.BytesIO(response.read()), mode="r:gz")
    count = 0
    for member in archive.getmembers():
        if not member.isfile() or not member.name.endswith(".cnf"):
            continue
        name = os.path.basename(member.name)[:-len(".cnf")]
        label = status if isinstance(status, str) else status(name)
        directory = os.path.join(HERE, label, "satlib-all", family)
        os.makedirs(directory, exist_ok=True)
        text = archive.extractfile(member).read().decode("latin-1")
        with open(os.path.join(directory, name + ".cnf"), "w") as out:
            out.write(normalize(text))
        count += 1
    print(f"{family}: {count} problems")


def fetch_release():
    """Download the release asset, check its checksum and unpack it."""
    with urllib.request.urlopen(RELEASE) as response:
        data = response.read()
    digest = hashlib.sha256(data).hexdigest()
    if digest != SHA256:
        sys.exit(f"checksum mismatch: got {digest}, expected {SHA256}")
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:xz") as archive:
        archive.extractall(HERE, filter="data")
    print("unpacked satlib-all.tar.xz")


def main():
    args = sys.argv[1:]
    if not args:
        fetch_release()
        return
    if args[0] != "--from-satlib":
        sys.exit(__doc__)
    wanted = set(args[1:])
    unknown = wanted - {family for family, _, _ in FAMILIES}
    if unknown:
        sys.exit("unknown families: " + " ".join(sorted(unknown)))
    for family, path, status in FAMILIES:
        if not wanted or family in wanted:
            fetch(family, path, status)


if __name__ == "__main__":
    main()
