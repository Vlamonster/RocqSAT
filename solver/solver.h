/* The state of the RocqSAT solver (refinement/core/SolverStep.v). A literal is a key: atom a is 2a when
   positive and 2a + 1 when negative. Values are 1 (true), -1 (false) and 0 (unassigned). Stacks keep their newest
   entry last. */
struct solver {
  int nv;        /* the number of atoms: 0 .. nv - 1 */
  int ncl;       /* the number of clauses: 0 .. ncl - 1 */
  int *cstart;   /* [ncl + 1] clause i has the literals clits[cstart[i] .. cstart[i + 1]) */
  int *clits;    /* the literals of the clauses, the two watches of each first (cmap) */
  int *vals;     /* [2 nv] the value of each literal: of its atom, negated for a negative literal (vals) */
  int *wpool;    /* [2 npool] the watch lists (wls): that of literal l has the watchers woff[l] .. woff[l] + wlen[l],
                    watcher w taking entries 2w (its clause) and 2w + 1 (its blocker) */
  int npool;
  int *woff;     /* [2 nv] where each watch list starts in the pool, laid out by the caller */
  int *wlen;     /* [2 nv] */
  int *wcap;     /* [2 nv] the room of each watch list, laid out by the caller */
  int *tr;       /* [nv] the trail, oldest first (tr) */
  int tlen;      /* the length of the trail (tlen) */
  int qhead;     /* the trail literals from qhead on still have their watchers to visit (qhead) */
  int *shorts;   /* [ncl] the clauses with fewer than two literals still to check (shorts) */
  int nshorts;
  int *alls;     /* [2 nv] the literals to decide on (alls), in the caller's order; init checks them */
  int nlits;
  int cur;       /* the literals to decide on before cur are assigned (cur) */
  int *saved;    /* [nv] the cursor before each decision (saved) */
  int *lims;     /* [nv] the trail position of each decision */
  int dl;        /* the number of decisions, the length of saved and lims */
  int *phs;      /* [nv] the value each atom last had (phs) */
  int *mrk;      /* [2 nv] marks of literals, used to check them and by the analysis (mrk) */
  int *rsn;      /* [nv] the reason of each atom on the trail: 0 none, i + 1 input clause i, -(j + 1) reason clause j
                    (rsn) */
  int *lvl;      /* [nv] the decision level of each atom on the trail (lvl) */
  int *lt;       /* [nv] the literals of the lower levels of the clause being analysed */
  int ltlen;     /* their number, 0 outside resolve */
  int *rlits;    /* [rcap] the literals of the reason clauses, one after the other (rcl) */
  int rcap;      /* the room for them, laid out by the caller (rcap) */
  int rtop;      /* the number of them */
  int *rbeg;     /* [nv] where each reason clause starts in rlits */
  int *rlen;     /* [nv] its length */
  int *rpos;     /* [nv] the trail position of the literal it asserted (rps) */
  int nr;        /* the number of reason clauses (nr) */
};

/* Set up the initial state for the clauses already in cstart and clits, with the watch lists laid out in woff and
   wcap and the literals to decide on in alls[0 .. nlits): watch the first literals of the clauses. Returns 0 if
   there is no atom, a literal has no atom below nv, a clause has a literal
   twice, alls is not the literals of the clauses each once, or the watch lists do not fit in the pool one after
   the other. */
int init(struct solver *s);

/* Run the solver from its initial state: 1 if the trail is then a model, 0 if the formula is unsatisfiable, 2 if
   the solver ran out of room. */
int solve(struct solver *s);
