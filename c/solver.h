/* The state of the RocqSAT solver. A literal is a key: atom a is 2a when positive and 2a + 1 when negative. Values
   are 1 (true), -1 (false) and 0 (unassigned). Stacks keep their newest entry last. */
struct solver {
  int nv;        /* the number of atoms: 0 .. nv - 1 */
  int ncl;       /* the number of clauses: 0 .. ncl - 1 */
  int *cstart;   /* [ncl + 1] clause i has the literals clits[cstart[i] .. cstart[i + 1]) */
  int *clits;    /* the literals of the clauses */
  int *vals;     /* [nv] the value of each atom */
  int *w1;       /* [ncl] the first watched literal of each clause */
  int *w2;       /* [ncl] the second watched literal of each clause */
  int *wpool;    /* the watch lists: that of literal l is wpool[woff[l] .. woff[l] + wlen[l]) */
  int *woff;     /* [2 nv] */
  int *wlen;     /* [2 nv] */
  int *wcap;     /* [2 nv] the room of each watch list: woff[l + 1] = woff[l] + wcap[l] */
  int *tr;       /* [nv] the trail, oldest first */
  int tlen;      /* the length of the trail */
  int qhead;     /* the trail literals from qhead on still have their watchers to visit */
  int *shorts;   /* the clauses with fewer than two literals still to check, newest last */
  int nshorts;
  int *alls;     /* [nlits] the literals to decide on */
  int nlits;
  int cur;       /* the literals to decide on before cur are assigned */
  int *saved;    /* [nv] the cursor before each decision */
  int *lims;     /* [nv] the trail position of each decision */
  int dl;        /* the number of decisions, the length of saved and lims */
  int *rsn;      /* [nv] 1 + the clause that propagated each atom, or 0 */
  int *lvl;      /* [nv] the decision level at which each atom was assigned */
  int *mrk;      /* [2 nv] the marks of literals used by the analysis */
  int *phs;      /* [nv] the value each atom last had */
  int *lt;       /* [2 nv] the learnt clause of the analysis, newest last */
  int ltlen;
};

/* Set up the initial state for the ncl clauses of the input: clause i has the literals lits[start[i] ..
   start[i + 1]). The tables of s have their sizes for s->nv atoms, the clauses room for start[ncl] literals, and the
   watch lists room for room clauses. Returns 0 if a literal has no atom below s->nv, or the watch lists do not fit. */
int init(struct solver *s, int ncl, const int *start, const int *lits, int room);

/* Run the solver from its initial state: 1 if the trail is then a model, 0 if the formula is unsatisfiable, 2 if
   the solver ran out of room. */
int solve(struct solver *s);
