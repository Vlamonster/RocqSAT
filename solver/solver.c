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

/* Assign l with reason r at the end of the trail, at the current level (assign): 0 if the trail is full. */
static inline int assign(struct solver *s, int l, int r) {
  int a = l >> 1;
  int v = 1 - 2 * (l & 1);
  int t = s->tlen;
  if (t >= s->nv) return 0;
  set_value(s, a, v);
  s->tr[t] = l;
  s->tlen = t + 1;
  s->phs[a] = v;
  s->rsn[a] = r;
  s->lvl[a] = s->dl;
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
   rev_append of visit_t). */
static inline void keep_rest(struct solver *s, int p, int j, int k, int n) {
  int base = 2 * s->woff[p];
  while (k < n) {
    s->wpool[base + 2 * j] = s->wpool[base + 2 * k];
    s->wpool[base + 2 * j + 1] = s->wpool[base + 2 * k + 1];
    j++;
    k++;
  }
  s->wlen[p] = j;
}

/* Visit the watchers of the false literal p (visit_t): i + 1 on a conflict on clause i, 0, or -1 to give up. A watcher is a clause
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
      if (s->clits[b] == p) {
        keep_rest(s, p, j, k, n);
        return i + 1;
      }
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
            if (!assign(s, o, i + 1)) return -1;
            kb = o;
          } else {
            keep_rest(s, p, j, k, n);
            return i + 1;
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

/* Visit the watchers of the queued literals, at most nv + 1 of them, until a conflict (propagate_t): i + 1 on a
   conflict on clause i, 0, or -1 to give up. */
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

/* Check the clauses with fewer than two literals, newest first (check_shorts_t): i + 1 on a conflict on clause i,
   0, or -1 to give up. */
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
      if (!assign(s, a, i + 1)) return -1;
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

/* Activities stay below 2^30, so that C adds two of them without overflow (act_lim). */
#define ACT_LIM (1 << 30)

/* Divide the activities by 2^20, and make the bump c divided by it, at least 1 (rescale). */
static void rescale(struct solver *s, int c) {
  int a = 0;
  while (a < s->nv) {
    s->act[a] = s->act[a] >> 20;
    a++;
  }
  c = c >> 20;
  if (c < 1) c = 1;
  s->inc = c;
}

/* Move the atom at heap position i up while its parent has a lower activity, at most hsize times (heap_up). */
static void heap_up(struct solver *s, int i) {
  int a = s->heap[i];
  int fuel = s->hsize;
  while (fuel > 0) {
    if (i <= 0) break;
    int p = (i - 1) / 2;
    int b = s->heap[p];
    if (s->act[b] >= s->act[a]) break;
    s->heap[i] = b;
    s->hpos[b] = i;
    i = p;
    fuel--;
  }
  s->heap[i] = a;
  s->hpos[a] = i;
}

/* Move the atom at heap position i down while a child has a higher activity, at most hsize times (heap_down). */
static void heap_down(struct solver *s, int i) {
  int a = s->heap[i];
  int n = s->hsize;
  int fuel = n;
  while (fuel > 0) {
    int c = 2 * i + 1;
    if (c >= n) break;
    if (c + 1 < n) {
      if (s->act[s->heap[c + 1]] > s->act[s->heap[c]]) c = c + 1;
    }
    int b = s->heap[c];
    if (s->act[b] <= s->act[a]) break;
    s->heap[i] = b;
    s->hpos[b] = i;
    i = c;
    fuel--;
  }
  s->heap[i] = a;
  s->hpos[a] = i;
}

/* Put atom a in the heap, unless it is there, is not decided on, or the heap is full (heap_insert). */
static void heap_insert(struct solver *s, int a) {
  if (s->hpos[a] >= 0) return;
  if (s->dlit[a] < 0) return;
  int n = s->hsize;
  if (n >= s->nv) return;
  s->heap[n] = a;
  s->hpos[a] = n;
  s->hsize = n + 1;
  heap_up(s, n);
}

/* Take the atom at the top of the non-empty heap out of it (heap_pop). */
static int heap_pop(struct solver *s) {
  int a = s->heap[0];
  int n = s->hsize - 1;
  s->hsize = n;
  s->hpos[a] = -1;
  if (n > 0) {
    int b = s->heap[n];
    s->heap[0] = b;
    s->hpos[b] = 0;
    heap_down(s, 0);
  }
  return a;
}

/* Raise the activity of atom a by the bump, rescaling first if it would reach ACT_LIM (bump). */
static void bump(struct solver *s, int a) {
  if (s->act[a] >= ACT_LIM - s->inc) rescale(s, s->inc);
  s->act[a] = s->act[a] + s->inc;
  int i = s->hpos[a];
  if (i >= 0) heap_up(s, i);
}

/* Raise the bump by 1/19, the factor 1/0.95 of MiniSat, rescaling when it reaches ACT_LIM / 2 (decay). */
static void decay(struct solver *s) {
  int c = s->inc;
  c = c + c / 19;
  if (c >= ACT_LIM / 2) rescale(s, c);
  else s->inc = c;
}

/* Take atoms out of the heap, at most nv, until the literal to decide on of one is unassigned: that literal, or
   -1 (pick). */
static int pick(struct solver *s) {
  int fuel = s->nv;
  while (fuel > 0) {
    if (s->hsize <= 0) return -1;
    int b = heap_pop(s);
    int l = s->dlit[b];
    if (l >= 0) {
      if (lit_value(s, l) == 0) return l;
    }
    fuel--;
  }
  return -1;
}

/* Put the atoms of the trail positions j .. q - 1 back in the heap (reinsert). */
static void reinsert(struct solver *s, int j, int q) {
  while (q > j) {
    heap_insert(s, s->tr[q - 1] >> 1);
    q--;
  }
}

/* The number of reason clauses of the literals below trail position j: those at j and above are the newest
   (pop_reasons). */
static inline int pop_reasons(struct solver *s, int j) {
  int n = s->nr;
  while (n > 0) {
    if (s->rpos[n - 1] < j) return n;
    n--;
  }
  return n;
}

/* Cut the trail back to position j, putting the atoms from there on back in the heap and unassigning them, with an
   empty queue, and drop the reason clauses of the literals from j on (jump_heur). */
static void cut(struct solver *s, int j) {
  reinsert(s, j, s->tlen);
  int q = s->tlen;
  while (q > j) {
    set_value(s, s->tr[q - 1] >> 1, 0);
    q--;
  }
  s->tlen = j;
  s->qhead = j;
  int n = pop_reasons(s, j);
  if (n < s->nr) {
    s->rtop = s->rbeg[n];
    s->nr = n;
  }
}

/* Mark literal y for the analysis and bump its atom (the marking of add_lits). */
static inline void mark(struct solver *s, int y) {
  s->mrk[y] = 1;
  bump(s, y >> 1);
}

/* Add the literals cl[q .. e) other than t that are not marked to the analysis at level d (add_lits): mark them,
   count those of level d in pathc, and append the others to lt. The new count, or -1 if a count or lt would reach
   nv. */
static int add_lits(struct solver *s, int *cl, int q, int e, int t, int d, int pathc) {
  while (q < e) {
    int y = cl[q];
    if (y != t) {
      if (s->mrk[y] == 0) {
        if (s->lvl[y >> 1] == d) {
          if (pathc >= s->nv) return -1;
          mark(s, y);
          pathc++;
        } else {
          int n = s->ltlen;
          if (n >= s->nv) return -1;
          mark(s, y);
          s->lt[n] = y;
          s->ltlen = n + 1;
        }
      }
    }
    q++;
  }
  return pathc;
}

/* The position after the newest trail position below idx and from lo on whose literal has its negation marked, or
   lo (prev_marked). */
static int prev_marked(struct solver *s, int idx, int lo) {
  while (idx > lo) {
    if (s->mrk[s->tr[idx - 1] ^ 1]) return idx;
    idx--;
  }
  return idx;
}

/* Add the literals of the reason of the trail literal t other than t to the analysis at level d, as add_lits (the
   reason_lits of analyze_loop): the new count, or -1 if t has no reason clause or a count would reach nv. */
static int add_reason_lits(struct solver *s, int t, int d, int pathc) {
  int r = s->rsn[t >> 1];
  if (r > 0) {
    if (r > s->ncl) return -1;
    return add_lits(s, s->clits, s->cstart[r - 1], s->cstart[r], t, d, pathc);
  }
  if (r < 0) {
    if (r < -s->nr) return -1;
    int b = s->rbeg[-r - 1];
    return add_lits(s, s->rlits, b, b + s->rlen[-r - 1], t, d, pathc);
  }
  return -1;
}

/* Unmark the negations of the trail literals at positions lo .. idx - 1 (unmark_range). */
static void unmark_range(struct solver *s, int idx, int lo) {
  while (idx > lo) {
    s->mrk[s->tr[idx - 1] ^ 1] = 0;
    idx--;
  }
}

/* Analyse the conflict on clause i at level d, whose decision is at trail position lo (analyze): the literal to
   assert, or -1. Starts with lt empty, and leaves the lower literals of the analysed clause in lt, marked, and the
   literal to assert marked. */
static int analyze(struct solver *s, int i, int d, int lo) {
  int idx = s->tlen;
  int pathc = add_lits(s, s->clits, s->cstart[i], s->cstart[i + 1], -1, d, 0);
  int fuel = s->tlen;
  while (fuel > 0) {
    if (pathc <= 0) break;
    int idx1 = prev_marked(s, idx, lo);
    idx = idx1;
    if (idx1 <= lo) break;
    int t = s->tr[idx1 - 1];
    if (pathc == 1) return t ^ 1;
    s->mrk[t ^ 1] = 0;
    idx = idx1 - 1;
    pathc = add_reason_lits(s, t, d, pathc - 1);
    fuel--;
  }
  unmark_range(s, idx, lo);
  return -1;
}

/* Unmark the literals of lt, and return the highest of their levels, or 0 (unmark_lower). */
static int unmark_lower(struct solver *s) {
  int mx = 0;
  int q = 0;
  while (q < s->ltlen) {
    int y = s->lt[q];
    s->mrk[y] = 0;
    int v = s->lvl[y >> 1];
    if (v > mx) mx = v;
    q++;
  }
  return mx;
}

/* Store u and lt as the reason clause of the literal at trail position tlen (push_reason): its reason, or 0 if
   there is no room. */
static int push_reason(struct solver *s, int u) {
  int j = s->nr;
  int b = s->rtop;
  int n = s->ltlen;
  if (j >= s->nv) return 0;
  if (n >= s->rcap - b) return 0;
  s->rlits[b] = u;
  int q = 0;
  while (q < n) {
    s->rlits[b + 1 + q] = s->lt[q];
    q++;
  }
  s->rbeg[j] = b;
  s->rlen[j] = n + 1;
  s->rpos[j] = s->tlen;
  s->rtop = b + n + 1;
  s->nr = j + 1;
  return -(j + 1);
}

/* Resolve a conflict on clause i (resolve_t): fail without decisions; otherwise analyse it and backjump, asserting
   the literal the analysis gives with the analysed clause as its reason if there is room, or flip the last
   decision. 1 to fail, 2 to go on, or -1 to give up. */
static int resolve(struct solver *s, int i) {
  int d = s->dl;
  if (d == 0) return 1;
  decay(s);
  int lo = s->lims[d - 1];
  int u = analyze(s, i, d, lo);
  int mx = unmark_lower(s);
  if (u >= 0) {
    s->mrk[u] = 0;
    if (mx < d) {
      cut(s, s->lims[mx]);
      s->cur = s->saved[mx];
      s->dl = mx;
      int r = push_reason(s, u);
      s->ltlen = 0;
      if (!assign(s, u, r)) return -1;
      return 2;
    }
  }
  s->ltlen = 0;
  int l = s->tr[lo];
  cut(s, lo);
  s->cur = s->saved[d - 1];
  s->dl = d - 1;
  if (!assign(s, l ^ 1, 0)) return -1;
  return 2;
}

/* One step (cstep): 0 to stop, 1 to fail, 2 to go on, or -1 to give up. */
static int step(struct solver *s) {
  int t0 = s->tlen;
  int c = check_shorts(s);
  if (c < 0) return -1;
  if (c > 0) return resolve(s, c - 1);
  s->nshorts = 0;
  c = propagate(s);
  if (c < 0) return -1;
  if (c > 0) return resolve(s, c - 1);
  int l0 = pick(s);
  if (l0 >= 0) {
    int l = phase(s, l0);
    s->saved[s->dl] = s->cur;
    s->lims[s->dl] = s->tlen;
    s->dl = s->dl + 1;
    if (!assign(s, l, 0)) return -1;
    return 2;
  }
  int k = skip_from(s);
  if (k < s->nlits) {
    int l = phase(s, s->alls[k]);
    s->cur = k;
    s->saved[s->dl] = k;
    s->lims[s->dl] = s->tlen;
    s->dl = s->dl + 1;
    if (!assign(s, l, 0)) return -1;
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

/* Set n ints from p on to -1, "none" (fill_none). */
static void fill_none(int *p, int n) {
  int q = 0;
  while (q < n) {
    p[q] = -1;
    q++;
  }
}

/* Put the atoms of the literals to decide on in the heap, in their order: the first literal of each atom becomes
   its literal to decide on, with activity nlits - k for the literal at position k (add_atoms). */
static void add_atoms(struct solver *s) {
  int n = s->nlits;
  int k = 0;
  while (k < n) {
    int l = s->alls[k];
    int b = l >> 1;
    if (s->dlit[b] < 0) {
      s->dlit[b] = l;
      s->act[b] = n - k;
      heap_insert(s, b);
    }
    k++;
  }
}

int init(struct solver *s) {
  if (s->nv < 1) return 0;
  int n = 2 * s->nv;
  zero(s->vals, n);
  zero(s->tr, s->nv);
  zero(s->phs, s->nv);
  zero(s->mrk, n);
  zero(s->wlen, n);
  zero(s->rsn, s->nv);
  zero(s->lvl, s->nv);
  zero(s->act, s->nv);
  zero(s->heap, s->nv);
  fill_none(s->hpos, s->nv);
  fill_none(s->dlit, s->nv);
  s->tlen = 0;
  s->qhead = 0;
  s->nshorts = 0;
  s->cur = 0;
  s->dl = 0;
  s->ltlen = 0;
  s->rtop = 0;
  s->nr = 0;
  s->hsize = 0;
  if (!check_clauses(s)) return 0;
  if (!check_lits(s)) return 0;
  s->inc = s->nlits + 1;
  if (!check_room(s)) return 0;
  int ns = index_clauses(s);
  if (ns < 0) return 0;
  s->nshorts = ns;
  add_atoms(s);
  return 1;
}
