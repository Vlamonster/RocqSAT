/* The driver of the C solver, not verified: read a DIMACS CNF problem from standard input, without duplicate
   literals in a clause, lay out the watch lists, choose the order of decisions, allocate the tables, run the solver,
   and print UNSAT, SAT followed by a model, or UNKNOWN when it ran out of room. dune compiles it with CompCert
   into `rocqsat` (see dune); by hand: `ccomp -O main.c solver.c` (in this directory). */

#include <stdio.h>
#include <stdlib.h>
#include "solver.h"

/* Memory for n ints, at least one; exits when there is none. */
static int *ints(long n) {
  int *p = malloc(sizeof(int) * (size_t) (n > 0 ? n : 1));
  if (p == NULL) {
    fprintf(stderr, "out of memory\n");
    exit(1);
  }
  return p;
}

/* The occurrences of each atom and the first position of each literal, for the order of decisions. */
static long *occ, *first;

/* Most occurrences of its atom first, and among those the literal that occurs first. */
static int by_occurrences(const void *x, const void *y) {
  int a = *(const int *) x, b = *(const int *) y;
  if (a == b) return 0;
  if (occ[a >> 1] != occ[b >> 1]) return occ[a >> 1] > occ[b >> 1] ? -1 : 1;
  return first[a] < first[b] ? -1 : 1;
}

/* The literals to decide on, which init checks: each literal of the clauses once, those whose atom occurs most often
   first (a static two-sided occurrence count, as DLCS or two-sided Jeroslow-Wang without weights). Returns their
   number. */
static int decision_order(int *lits, long n, int nv, int *alls) {
  occ = calloc((size_t) nv, sizeof(long));
  first = malloc(sizeof(long) * 2 * (size_t) nv);
  if (occ == NULL || first == NULL) {
    fprintf(stderr, "out of memory\n");
    exit(1);
  }
  for (long k = 0; k < 2L * nv; k++) first[k] = -1;
  int nl = 0;
  for (long q = 0; q < n; q++) {
    occ[lits[q] >> 1]++;
    if (first[lits[q]] < 0) {
      first[lits[q]] = q;
      alls[nl++] = lits[q];
    }
  }
  qsort(alls, (size_t) nl, sizeof(int), by_occurrences);
  free(occ);
  free(first);
  return nl;
}

int main(void) {
  int c;
  /* Skip comments and the problem line. */
  while ((c = getchar()) == 'c' || c == 'p' || c == '\n') {
    if (c != '\n') {
      while ((c = getchar()) != '\n' && c != EOF) {}
    }
  }
  if (c != EOF) ungetc(c, stdin);
  long cap = 1024, n = 0, ccap = 1024, ncl = 0;
  int *lits = ints(cap), *start = ints(ccap + 1);
  long maxatom = 0, x;
  start[0] = 0;
  while (scanf("%ld", &x) == 1) {
    /* Drop a literal that the clause already has. */
    int dup = 0;
    for (long q = start[ncl]; q < n && x != 0; q++) {
      if (lits[q] == (int) (x > 0 ? 2 * x : -2 * x + 1)) dup = 1;
    }
    if (dup) continue;
    if (x == 0) {
      if (ncl + 1 >= ccap) {
        ccap *= 2;
        start = realloc(start, sizeof(int) * (size_t) (ccap + 1));
        if (start == NULL) exit(1);
      }
      start[++ncl] = (int) n;
      continue;
    }
    long a = x > 0 ? x : -x;
    if (a > maxatom) maxatom = a;
    if (n >= cap) {
      cap *= 2;
      lits = realloc(lits, sizeof(int) * (size_t) cap);
      if (lits == NULL) exit(1);
    }
    lits[n++] = (int) (x > 0 ? 2 * a : 2 * a + 1);
  }
  if (n != start[ncl]) {
    fprintf(stderr, "clause not terminated by 0\n");
    return 1;
  }
  if (maxatom >= (1L << 28) || n >= (1L << 28) || ncl >= (1L << 28)) {
    fprintf(stderr, "problem too large\n");
    return 1;
  }
  struct solver s;
  int nv = (int) maxatom + 1;
  s.nv = nv;
  s.ncl = (int) ncl;
  s.cstart = start;
  s.clits = lits;
  s.vals = ints(2L * nv);
  /* The room of the watch lists: twice the occurrences of each literal. */
  s.woff = ints(2L * nv);
  s.wlen = ints(2L * nv);
  s.wcap = ints(2L * nv);
  for (long k = 0; k < 2L * nv; k++) s.wcap[k] = 0;
  for (long q = 0; q < n; q++) s.wcap[lits[q]] += 2;
  long off = 0;
  for (long k = 0; k < 2L * nv; k++) {
    s.woff[k] = (int) off;
    off += s.wcap[k];
  }
  s.npool = (int) off;
  s.wpool = ints(2 * off);
  s.tr = ints(nv);
  s.shorts = ints(ncl);
  s.alls = ints(2L * nv);
  s.nlits = decision_order(lits, n, nv, s.alls);
  s.saved = ints(nv);
  s.lims = ints(nv);
  s.phs = ints(nv);
  s.mrk = ints(2L * nv);
  if (!init(&s)) {
    fprintf(stderr, "bad input\n");
    return 1;
  }
  int r = solve(&s);
  if (r == 2) {
    printf("UNKNOWN\n");
  } else if (r == 0) {
    printf("UNSAT\n");
  } else {
    /* The model: the trail literals, sorted by atom. */
    printf("SAT");
    for (int a = 1; a < nv; a++) {
      if (s.vals[2 * a] != 0) printf(" %d", s.vals[2 * a] * a);
    }
    printf("\n");
  }
  fflush(stdout);
  return 0;
}
