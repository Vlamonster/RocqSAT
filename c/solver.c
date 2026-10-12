/* The RocqSAT solver in C: the initial context and the step of verification/refinement/CStep.v, verified against
   them with VST (verification/c/). It allocates no memory: the caller provides every table. Where a table could
   run out of room, which the invariants of the model rule out but the proofs do not show, it gives up. */

#include "solver.h"

/* Codes for giving up and for the results of solve. */
#define GIVE_UP (-1)

/* Append clause i to the watch list of literal l: 0 if it has no room. */
static int wpush(struct solver *s, int l, int i) {
  int n = s->wlen[l];
  if (n >= s->wcap[l]) return 0;
  s->wpool[s->woff[l] + n] = i;
  s->wlen[l] = n + 1;
  return 1;
}

/* The value of literal l: 1 if true, -1 if false, 0 if unassigned (lookup). */
static int lit_value(struct solver *s, int l) {
  int v = s->vals[l >> 1];
  if (l & 1) return -v;
  return v;
}

/* Assign l with reason r at the current level, appending it to the trail (assign): 0 if the trail is full. */
static int assign(struct solver *s, int l, int r) {
  int a = l >> 1;
  int v = 1 - 2 * (l & 1);
  int t = s->tlen;
  if (t >= s->nv) return 0;
  s->vals[a] = v;
  s->tr[t] = l;
  s->tlen = t + 1;
  s->rsn[a] = r;
  s->lvl[a] = s->dl;
  s->phs[a] = v;
  return 1;
}

/* The first literal of clause i that is not false and not o, or -1 (the find of visit_t). */
static int find_other(struct solver *s, int i, int o) {
  int q = s->cstart[i];
  int e = s->cstart[i + 1];
  while (q < e) {
    int y = s->clits[q];
    if (y != o) {
      if (lit_value(s, y) != -1) return y;
    }
    q++;
  }
  return -1;
}

/* Visit the clauses watching the false literal p (visit_t): 1 + the conflict clause, 0, or GIVE_UP. The clauses kept
   in the watch list of p are written back to its front. */
static int visit(struct solver *s, int p) {
  int base = s->woff[p];
  int n = s->wlen[p];
  int j = 0;
  int k = 0;
  while (k < n) {
    int i = s->wpool[base + k];
    int a = s->w1[i];
    int b = s->w2[i];
    int o;
    if (a == p) o = b;
    else if (b == p) o = a;
    else o = -1;
    if (o >= 0) {
      if (lit_value(s, o) == 1) {
        s->wpool[base + j] = i;
        j++;
      } else {
        int r = find_other(s, i, o);
        if (r >= 0) {
          if (a == p) s->w1[i] = r; else s->w2[i] = r;
          if (!wpush(s, r, i)) return GIVE_UP;
        } else if (lit_value(s, o) == 0) {
          if (!assign(s, o, i + 1)) return GIVE_UP;
          s->wpool[base + j] = i;
          j++;
        } else {
          while (k < n) {
            s->wpool[base + j] = s->wpool[base + k];
            j++;
            k++;
          }
          s->wlen[p] = j;
          return i + 1;
        }
      }
    }
    k++;
  }
  s->wlen[p] = j;
  return 0;
}

/* Visit the watchers of the queued literals, at most nv + 1 of them, until a conflict (propagate_t): 1 + the
   conflict clause, 0, or GIVE_UP. */
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

/* Check the clauses with fewer than two literals, newest first (check_shorts_t): 1 + the conflict clause, 0, or
   GIVE_UP. */
static int check_shorts(struct solver *s) {
  int q = s->nshorts;
  while (q > 0) {
    int i = s->shorts[q - 1];
    int b = s->cstart[i];
    if (b == s->cstart[i + 1]) return i + 1;
    int a = s->clits[b];
    int v = lit_value(s, a);
    if (v == -1) return i + 1;
    if (v == 0) {
      if (!assign(s, a, i + 1)) return GIVE_UP;
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

/* n - m cut off at 0. */
static int sub(int n, int m) {
  if (n >= m) return n - m;
  return 0;
}

/* Set the marks of the literals of clause i to b. */
static void mark_clause(struct solver *s, int i, int b) {
  int q = s->cstart[i];
  int e = s->cstart[i + 1];
  while (q < e) {
    s->mrk[s->clits[q]] = b;
    q++;
  }
}

/* Set the marks of the literals of the learnt clause to b. */
static void mark_learnt(struct solver *s, int b) {
  int q = 0;
  while (q < s->ltlen) {
    s->mrk[s->lt[q]] = b;
    q++;
  }
}

/* The number of literals of clause i at decision level d (count_level). */
static int count_level(struct solver *s, int i, int d) {
  int q = s->cstart[i];
  int e = s->cstart[i + 1];
  int k = 0;
  while (q < e) {
    if (s->lvl[s->clits[q] >> 1] == d) k++;
    q++;
  }
  return k;
}

/* The learnt clause becomes clause i: its literals are the data of lt, newest first. 0 if it has no room. */
static int learn_clause(struct solver *s, int i) {
  int q = s->cstart[i + 1];
  int b = s->cstart[i];
  int n = 0;
  while (q > b) {
    if (n >= 2 * s->nv) return 0;
    s->lt[n] = s->clits[q - 1];
    n++;
    q--;
  }
  s->ltlen = n;
  return 1;
}

/* Resolve the learnt clause with clause i on t, using the marks (resolve_marked): drop ¬t, then add the unmarked
   literals of clause i other than t. Given the count k of literals at level d, returns the new count, or GIVE_UP. */
static int resolve_marked(struct solver *s, int i, int t, int d, int k) {
  int nt = t ^ 1;
  int q = 0;
  int j = 0;
  s->mrk[nt] = 0;
  while (q < s->ltlen) {
    int y = s->lt[q];
    if (y != nt) {
      s->lt[j] = y;
      j++;
    }
    q++;
  }
  s->ltlen = j;
  k = sub(k, 1);
  q = s->cstart[i];
  int e = s->cstart[i + 1];
  while (q < e) {
    int y = s->clits[q];
    if (y != t) {
      if (s->mrk[y] == 0) {
        if (s->ltlen >= 2 * s->nv) return GIVE_UP;
        if (k >= 0x3fffffff) return GIVE_UP;
        s->mrk[y] = 1;
        s->lt[s->ltlen] = y;
        s->ltlen = s->ltlen + 1;
        if (s->lvl[y >> 1] == d) k++;
      }
    }
    q++;
  }
  return k;
}

/* Resolve the learnt clause with the reasons of the n trail literals from lo on, newest first, until at most one
   of its literals is at level d (analyze_t); k is that number of literals. 0 if it gave up. */
static int analyze(struct solver *s, int lo, int n, int d, int k) {
  while (n > 0) {
    int t = s->tr[lo + n - 1];
    if (k <= 1) return 1;
    if (s->mrk[t ^ 1]) {
      int r = s->rsn[t >> 1];
      if (r == 0) return 1;
      k = resolve_marked(s, r - 1, t, d, k);
      if (k < 0) return 0;
    }
    n--;
  }
  return 1;
}

/* Whether l is on the trail at one of the n positions from j on (in_range). */
static int in_range(struct solver *s, int l, int j, int n) {
  while (n > 0) {
    if (s->tr[j + n - 1] == l) return 1;
    n--;
  }
  return 0;
}

/* Whether a literal at one of the n positions from j on, other than nu, has its negation marked (marked_range). */
static int marked_range(struct solver *s, int nu, int j, int n) {
  while (n > 0) {
    int y = s->tr[j + n - 1];
    if (s->mrk[y ^ 1]) {
      if (y != nu) return 1;
    }
    n--;
  }
  return 0;
}

/* The literal of the learnt clause to assert by a backjump (the find of plan_t), or -1. */
static int find_level(struct solver *s, int d) {
  int q = s->ltlen;
  while (q > 0) {
    int y = s->lt[q - 1];
    if (s->lvl[y >> 1] == d) return y;
    q--;
  }
  return -1;
}

/* The highest level of the literals of the learnt clause other than u (the list_max of plan_t). */
static int max_level(struct solver *s, int u) {
  int mx = 0;
  int q = 0;
  while (q < s->ltlen) {
    int y = s->lt[q];
    if (y != u) {
      int v = s->lvl[y >> 1];
      if (v > mx) mx = v;
    }
    q++;
  }
  return mx;
}

/* Whether every literal of the learnt clause is false (the forallb of plan_t). */
static int all_false(struct solver *s) {
  int q = 0;
  while (q < s->ltlen) {
    if (lit_value(s, s->lt[q]) != -1) return 0;
    q++;
  }
  return 1;
}

/* Whether the backjump for u to trail position j is sound (the checks of plan_t). */
static int jump_ok(struct solver *s, int u, int j) {
  int nu = u ^ 1;
  int n = s->tlen - (j + 1);
  if (!all_false(s)) return 0;
  if (s->tr[j] != nu) {
    if (!in_range(s, nu, j + 1, n)) return 0;
  }
  if (s->mrk[s->tr[j] ^ 1]) {
    if (s->tr[j] != nu) return 0;
  }
  if (marked_range(s, nu, j + 1, n)) return 0;
  return 1;
}

/* Unassign the trail literals from position j on and jump back to it, with the cursor and decision level of the
   decision there, popping k + 1 decisions (jump). */
static void jump(struct solver *s, int j, int k) {
  int q = s->tlen;
  while (q > j) {
    s->vals[s->tr[q - 1] >> 1] = 0;
    q--;
  }
  s->tlen = j;
  s->qhead = j;
  s->cur = s->saved[s->dl - 1 - k];
  s->dl = s->dl - (k + 1);
}

/* Resolve the conflict on clause i (resolve_t): 1 to fail, 2 after a backjump or a backtrack, or GIVE_UP. */
static int resolve(struct solver *s, int i) {
  int d = s->dl;
  if (d == 0) return 1;
  int j0 = s->lims[d - 1];
  mark_clause(s, i, 1);
  if (!learn_clause(s, i)) return GIVE_UP;
  if (!analyze(s, j0 + 1, s->tlen - (j0 + 1), d, count_level(s, i, d))) return GIVE_UP;
  mark_learnt(s, 1);
  int u = find_level(s, d);
  if (u >= 0) {
    int k = sub(d, max_level(s, u) + 1);
    if (k < d) {
      int j = s->lims[d - 1 - k];
      if (jump_ok(s, u, j)) {
        mark_learnt(s, 0);
        jump(s, j, k);
        if (!assign(s, u, 0)) return GIVE_UP;
        return 2;
      }
    }
  }
  int l = s->tr[j0];
  mark_learnt(s, 0);
  jump(s, j0, 0);
  if (!assign(s, l ^ 1, 0)) return GIVE_UP;
  return 2;
}

/* One solver step (cstep): 0 to stop, 1 to fail, 2 to go on, or GIVE_UP. */
static int step(struct solver *s) {
  int t0 = s->tlen;
  int c = check_shorts(s);
  if (c < 0) return GIVE_UP;
  if (c > 0) return resolve(s, c - 1);
  s->nshorts = 0;
  c = propagate(s);
  if (c < 0) return GIVE_UP;
  if (c > 0) return resolve(s, c - 1);
  int cu = skip_from(s);
  if (cu < s->nlits) {
    int l = phase(s, s->alls[cu]);
    int d = s->dl;
    if (d >= s->nv) return GIVE_UP;
    s->cur = cu;
    s->saved[d] = cu;
    s->lims[d] = s->tlen;
    s->dl = d + 1;
    if (!assign(s, l, 0)) return GIVE_UP;
    return 2;
  }
  if (s->tlen == t0) return 0;
  s->cur = cu;
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

/* Store clause i of the input, the literals lits[b .. e), from position pos of the clauses on without duplicates;
   returns the position after it, or GIVE_UP if a literal has no atom below nv. */
static int store_clause(struct solver *s, const int *lits, int b, int e, int pos) {
  int q = b;
  int p = pos;
  while (q < e) {
    int y = lits[q];
    if (y < 0) return GIVE_UP;
    if (y >= 2 * s->nv) return GIVE_UP;
    if (s->mrk[y] == 0) {
      s->mrk[y] = 1;
      s->clits[p] = y;
      p++;
    }
    q++;
  }
  q = pos;
  while (q < p) {
    s->mrk[s->clits[q]] = 0;
    q++;
  }
  return p;
}

/* The literals of the clauses without duplicates, in order of first occurrence, as the literals to decide on. */
static void collect_lits(struct solver *s) {
  int e = s->cstart[s->ncl];
  int n = 0;
  int q = 0;
  while (q < e) {
    int y = s->clits[q];
    if (s->mrk[y] == 0) {
      s->mrk[y] = 1;
      s->alls[n] = y;
      n++;
    }
    q++;
  }
  q = 0;
  while (q < n) {
    s->mrk[s->alls[q]] = 0;
    q++;
  }
  s->nlits = n;
}

/* Room for the watch lists: twice the number of occurrences of each literal, and twice the number of empty clauses
   for literal 0, which they watch; 0 if it exceeds the pool of size room. */
static int make_room(struct solver *s, int room) {
  int n = 2 * s->nv;
  int e = s->cstart[s->ncl];
  int q = 0;
  zero(s->wcap, n);
  while (q < e) {
    s->wcap[s->clits[q]] = s->wcap[s->clits[q]] + 2;
    q++;
  }
  q = 0;
  while (q < s->ncl) {
    if (s->cstart[q] == s->cstart[q + 1]) s->wcap[0] = s->wcap[0] + 2;
    q++;
  }
  int off = 0;
  q = 0;
  while (q < n) {
    s->woff[q] = off;
    off = off + s->wcap[q];
    if (off > room) return 0;
    q++;
  }
  return 1;
}

/* Index the clauses: watch their first literals and collect the short ones (index); 0 if a watch list has no
   room. */
static int index_clauses(struct solver *s) {
  int k = 0;
  s->nshorts = 0;
  while (k < s->ncl) {
    int b = s->cstart[k];
    int len = s->cstart[k + 1] - b;
    int a = 0;
    int c = 0;
    if (len >= 2) {
      a = s->clits[b];
      c = s->clits[b + 1];
    } else if (len == 1) {
      a = s->clits[b];
      c = a;
    }
    s->w1[k] = a;
    s->w2[k] = c;
    if (!wpush(s, a, k)) return 0;
    if (!wpush(s, c, k)) return 0;
    if (len <= 1) {
      s->shorts[s->nshorts] = k;
      s->nshorts = s->nshorts + 1;
    }
    k++;
  }
  return 1;
}

/* Set up the initial state for the ncl clauses of the input: clause i has the literals lits[start[i] ..
   start[i + 1]). The tables of s have their sizes for s->nv atoms, the clauses room for start[ncl] literals, and the
   watch lists room for room clauses. Returns 0 if a literal has no atom below s->nv, or the watch lists do not fit. */
int init(struct solver *s, int ncl, const int *start, const int *lits, int room) {
  int nv = s->nv;
  int pos = 0;
  int i = 0;
  s->ncl = ncl;
  zero(s->mrk, 2 * nv);
  zero(s->vals, nv);
  zero(s->tr, nv);
  zero(s->rsn, nv);
  zero(s->lvl, nv);
  zero(s->phs, nv);
  zero(s->wlen, 2 * nv);
  while (i < ncl) {
    s->cstart[i] = pos;
    pos = store_clause(s, lits, start[i], start[i + 1], pos);
    if (pos < 0) return 0;
    i++;
  }
  s->cstart[ncl] = pos;
  collect_lits(s);
  if (!make_room(s, room)) return 0;
  if (!index_clauses(s)) return 0;
  s->tlen = 0;
  s->qhead = 0;
  s->cur = 0;
  s->dl = 0;
  s->ltlen = 0;
  return 1;
}
