/* The driver of the C solver, not verified: read a DIMACS CNF problem from standard input, allocate the tables of
   the solver, run it, and print UNSAT, SAT followed by a model, or UNKNOWN if it ran out of room. It is called by
   the runner as `rocqsat --c` (runner/c_stub.c), and can be compiled on its own with CompCert:
   `ccomp -O -DSTANDALONE c/main.c c/solver.c`. */

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

int rocqsat_c_main(void) {
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
  s.cstart = ints(ncl + 1);
  s.clits = ints(n);
  s.vals = ints(nv);
  s.w1 = ints(ncl);
  s.w2 = ints(ncl);
  long room = 2 * n + 2 * ncl;
  s.wpool = ints(room);
  s.woff = ints(2L * nv);
  s.wlen = ints(2L * nv);
  s.wcap = ints(2L * nv);
  s.tr = ints(nv);
  s.shorts = ints(ncl);
  s.alls = ints(2L * nv);
  s.saved = ints(nv);
  s.lims = ints(nv);
  s.rsn = ints(nv);
  s.lvl = ints(nv);
  s.mrk = ints(2L * nv);
  s.phs = ints(nv);
  s.lt = ints(2L * nv);
  if (!init(&s, (int) ncl, start, lits, (int) room)) {
    printf("UNKNOWN\n");
    fflush(stdout);
    return 0;
  }
  int r = solve(&s);
  if (r == 0) {
    printf("UNSAT\n");
  } else if (r == 1) {
    /* The model: the trail literals, sorted by atom. */
    int *val = ints(nv);
    for (int a = 0; a < nv; a++) val[a] = 0;
    for (int j = 0; j < s.tlen; j++) val[s.tr[j] >> 1] = (s.tr[j] & 1) ? -1 : 1;
    printf("SAT");
    for (int a = 1; a < nv; a++) {
      if (val[a] != 0) printf(" %d", val[a] * a);
    }
    printf("\n");
  } else {
    printf("UNKNOWN\n");
  }
  fflush(stdout);
  return 0;
}

#ifdef STANDALONE
int main(void) { return rocqsat_c_main(); }
#endif
