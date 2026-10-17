/* The RocqSAT solver in C: the step on the context of refinement/core/SolverStep.v (cstep), function by
   function, verified in refinement/c/ (solver_correct). It allocates nothing and calls no library: the caller
   provides every table. Where a table could run out of room, it gives up. The functions marked inline are
   inlined by CompCert (a speedup of the propagation loop); clightgen ignores inline, so the proofs see the same
   program. */

#include "solver.h"

/* The value of literal l: 1 if true, -1 if false, 0 if unassigned (lookup). */
static inline int lit_value(struct solver *s, int l) {
  return s->vals[l];
}

/* Set the value of atom a to v: v for its positive literal, -v for its negative one (the tset of the values in
   assign and jump). */
static inline void set_value(struct solver *s, int a, int v) {
  s->vals[2 * a] = v;
  s->vals[2 * a + 1] = -v;
}

/* Append the watcher of clause i with blocker b to the watch list of literal l: 0 if it has no room. */
static inline int wpush(struct solver *s, int l, int i, int b) {
  int n = s->wlen[l];
  if (n >= s->wcap[l]) return 0;
  int q = 2 * (s->woff[l] + n);
  s->wpool[q] = i;
  s->wpool[q + 1] = b;
  s->wlen[l] = n + 1;
  return 1;
}

/* Assign l at the end of the trail (assign): 0 if the trail is full. */
static inline int assign(struct solver *s, int l) {
  int a = l >> 1;
  int v = 1 - 2 * (l & 1);
  int t = s->tlen;
  if (t >= s->nv) return 0;
  set_value(s, a, v);
  s->tr[t] = l;
  s->tlen = t + 1;
  s->phs[a] = v;
  return 1;
}

/* The first position from q to e whose literal is not false, or -1 (the search of swap_watch). */
static inline int find_watch(struct solver *s, int q, int e) {
  while (q < e) {
    if (lit_value(s, s->clits[q]) != -1) return q;
    q++;
  }
  return -1;
}

/* End the visit of the watchers of p at a conflict: write its watchers k .. n back from position j on (the
   rev_append of visit_t), and return 1. */
static inline int keep_rest(struct solver *s, int p, int j, int k, int n) {
  int base = 2 * s->woff[p];
  while (k < n) {
    s->wpool[base + 2 * j] = s->wpool[base + 2 * k];
    s->wpool[base + 2 * j + 1] = s->wpool[base + 2 * k + 1];
    j++;
    k++;
  }
  s->wlen[p] = j;
  return 1;
}

/* Visit the watchers of the false literal p (visit_t): 1 on a conflict, 0, or -1 to give up. A watcher is a clause
   and its blocker, two entries of the pool; the watchers kept, with blocker kb, are written back to the front of
   the watch list of p. The watches of a clause are its first two literals: a clause watching p is put in the form
   o, p, ... first. */
static int visit(struct solver *s, int p) {
  int base = 2 * s->woff[p];
  int n = s->wlen[p];
  int j = 0;
  int k = 0;
  while (k < n) {
    int i = s->wpool[base + 2 * k];
    int kb = s->wpool[base + 2 * k + 1];
    if (lit_value(s, kb) == 1) {
      s->wpool[base + 2 * j] = i;
      s->wpool[base + 2 * j + 1] = kb;
      j++;
      k++;
      continue;
    }
    kb = -1;
    int b = s->cstart[i];
    int e = s->cstart[i + 1];
    if (e - b == 1) {
      if (s->clits[b] == p) return keep_rest(s, p, j, k, n);
    } else if (e - b >= 2) {
      int o = s->clits[b];
      if (o == p) {
        o = s->clits[b + 1];
        s->clits[b] = o;
        s->clits[b + 1] = p;
      }
      if (s->clits[b + 1] == p) {
        if (lit_value(s, o) == 1) {
          kb = o;
        } else {
          int q = find_watch(s, b + 2, e);
          if (q >= 0) {
            int r = s->clits[q];
            s->clits[b + 1] = r;
            s->clits[q] = p;
            if (!wpush(s, r, i, o)) return -1;
          } else if (lit_value(s, o) == 0) {
            if (!assign(s, o)) return -1;
            kb = o;
          } else {
            return keep_rest(s, p, j, k, n);
          }
        }
      }
    }
    if (kb >= 0) {
      s->wpool[base + 2 * j] = i;
      s->wpool[base + 2 * j + 1] = kb;
      j++;
    }
    k++;
  }
  s->wlen[p] = j;
  return 0;
}

/* Visit the watchers of the queued literals, at most nv + 1 of them, until a conflict (propagate_t): 1 on a
   conflict, 0, or -1 to give up. */
static int propagate(struct solver *s) {
  int fuel = s->nv + 1;
  while (fuel > 0) {
    if (s->qhead >= s->tlen) return 0;
    int c = visit(s, s->tr[s->qhead] ^ 1);
    if (c != 0) return c;
    s->qhead = s->qhead + 1;
    fuel--;
  }
  return 0;
}

/* Check the clauses with fewer than two literals, newest first (check_shorts_t): 1 on a conflict, 0, or -1 to give
   up. */
static int check_shorts(struct solver *s) {
  int q = s->nshorts;
  while (q > 0) {
    int i = s->shorts[q - 1];
    int b = s->cstart[i];
    if (b == s->cstart[i + 1]) return 1;
    int a = s->clits[b];
    int v = lit_value(s, a);
    if (v == -1) return 1;
    if (v == 0) {
      if (!assign(s, a)) return -1;
    }
    q--;
  }
  return 0;
}

/* The first position from the cursor on whose literal is unassigned, or nlits (skip_from). */
static int skip_from(struct solver *s) {
  int c = s->cur;
  int n = s->nlits;
  while (c < n) {
    if (lit_value(s, s->alls[c]) == 0) return c;
    c++;
  }
  return c;
}

/* The literal of the atom of l with the value it last had, or l (phase). */
static int phase(struct solver *s, int l) {
  int a = l >> 1;
  int v = s->phs[a];
  if (v == 1) return 2 * a;
  if (v == -1) return 2 * a + 1;
  return l;
}

/* Cut the trail back to position j, unassigning the literals from there on, with an empty queue (the values,
   length and queue of jump). */
static void cut(struct solver *s, int j) {
  int q = s->tlen;
  while (q > j) {
    set_value(s, s->tr[q - 1] >> 1, 0);
    q--;
  }
  s->tlen = j;
  s->qhead = j;
}

/* Resolve a conflict (resolve_t): fail without decisions, and flip the last decision otherwise. 1 to fail, 2 to go
   on, or -1 to give up. */
static int resolve(struct solver *s) {
  if (s->dl == 0) return 1;
  int j0 = s->lims[s->dl - 1];
  int l = s->tr[j0];
  cut(s, j0);
  s->cur = s->saved[s->dl - 1];
  s->dl = s->dl - 1;
  if (!assign(s, l ^ 1)) return -1;
  return 2;
}

/* One step (cstep): 0 to stop, 1 to fail, 2 to go on, or -1 to give up. */
static int step(struct solver *s) {
  int t0 = s->tlen;
  int c = check_shorts(s);
  if (c < 0) return -1;
  if (c > 0) return resolve(s);
  s->nshorts = 0;
  c = propagate(s);
  if (c < 0) return -1;
  if (c > 0) return resolve(s);
  int k = skip_from(s);
  if (k < s->nlits) {
    int l = phase(s, s->alls[k]);
    s->cur = k;
    s->saved[s->dl] = k;
    s->lims[s->dl] = s->tlen;
    s->dl = s->dl + 1;
    if (!assign(s, l)) return -1;
    return 2;
  }
  if (s->tlen == t0) return 0;
  s->cur = k;
  return 2;
}

int solve(struct solver *s) {
  while (1) {
    int r = step(s);
    if (r == 0) return 1;
    if (r == 1) return 0;
    if (r < 0) return 2;
  }
}

/* Set n ints from p on to zero. */
static void zero(int *p, int n) {
  int q = 0;
  while (q < n) {
    p[q] = 0;
    q++;
  }
}

/* Whether all literals of the clauses have an atom below nv, and no clause has a literal twice; the marks are
   cleared before and after. */
static int check_clauses(struct solver *s) {
  int n = 2 * s->nv;
  int i = 0;
  while (i < s->ncl) {
    int b = s->cstart[i];
    int e = s->cstart[i + 1];
    int q = b;
    while (q < e) {
      int y = s->clits[q];
      if (y < 0) return 0;
      if (y >= n) return 0;
      if (s->mrk[y] != 0) return 0;
      s->mrk[y] = 1;
      q++;
    }
    q = b;
    while (q < e) {
      s->mrk[s->clits[q]] = 0;
      q++;
    }
    i++;
  }
  return 1;
}

/* Whether the literals to decide on that the caller put in alls[0 .. nlits) are the literals of the clauses, each
   once. The literals of the clauses are marked first; then each entry of alls must be a marked literal, and is
   unmarked, so none is there twice; then no literal of a clause may be marked still. The marks are cleared
   before. */
static int check_lits(struct solver *s) {
  int n = 2 * s->nv;
  int nl = s->nlits;
  int e = s->cstart[s->ncl];
  if (nl < 0) return 0;
  if (nl > n) return 0;
  int q = 0;
  while (q < e) {
    s->mrk[s->clits[q]] = 1;
    q++;
  }
  int k = 0;
  while (k < nl) {
    int y = s->alls[k];
    if (y < 0) return 0;
    if (y >= n) return 0;
    if (s->mrk[y] == 0) return 0;
    s->mrk[y] = 0;
    k++;
  }
  q = 0;
  while (q < e) {
    if (s->mrk[s->clits[q]] != 0) return 0;
    q++;
  }
  return 1;
}

/* Whether the watch lists the caller laid out fit in the pool, one after the other: that of literal l has room for
   wcap[l] clauses from woff[l] on. */
static int check_room(struct solver *s) {
  int n = 2 * s->nv;
  int off = 0;
  int q = 0;
  while (q < n) {
    int o = s->woff[q];
    int c = s->wcap[q];
    if (o < off) return 0;
    if (c < 0) return 0;
    if (c > s->npool - o) return 0;
    off = o + c;
    q++;
  }
  return 1;
}

/* Index the clauses: watch their first two literals, each with the other as blocker, and a unit clause by its
   literal, and collect the short ones (index); returns their number, or -1 if a watch list has no room. */
static int index_clauses(struct solver *s) {
  int k = 0;
  int ns = 0;
  while (k < s->ncl) {
    int b = s->cstart[k];
    int len = s->cstart[k + 1] - b;
    if (len >= 2) {
      int a = s->clits[b];
      int c = s->clits[b + 1];
      if (!wpush(s, a, k, c)) return -1;
      if (!wpush(s, c, k, a)) return -1;
    } else if (len == 1) {
      int a = s->clits[b];
      if (!wpush(s, a, k, a)) return -1;
    }
    if (len <= 1) {
      s->shorts[ns] = k;
      ns++;
    }
    k++;
  }
  return ns;
}

int init(struct solver *s) {
  if (s->nv < 1) return 0;
  int n = 2 * s->nv;
  zero(s->vals, n);
  zero(s->tr, s->nv);
  zero(s->phs, s->nv);
  zero(s->mrk, n);
  zero(s->wlen, n);
  s->tlen = 0;
  s->qhead = 0;
  s->nshorts = 0;
  s->cur = 0;
  s->dl = 0;
  if (!check_clauses(s)) return 0;
  if (!check_lits(s)) return 0;
  if (!check_room(s)) return 0;
  int ns = index_clauses(s);
  if (ns < 0) return 0;
  s->nshorts = ns;
  return 1;
}
