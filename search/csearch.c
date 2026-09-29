/*
 csearch.c -- floating-point search for a certificate of G(A;B) <= T (Section 5.5 of the paper).

 Starting from the box E_0, a box becomes a leaf if Gamma(E), computed in double precision, is at most
 T - margin; otherwise it is bisected along its widest coordinate. Pieces closer than 1e-9 count as touching.
 Both rules err on the safe side, but the result is not trusted: the checkers verify every leaf exactly.
 Up to depth -c, the program also evaluates Gamma at the centre of each box that it splits and stops with
 FAILED if the value exceeds T, since then no certificate exists.

 The tree is first expanded breadth first until it has `presplit` open boxes, whose subtrees are then
 searched in parallel (OpenMP) and written out in preorder, so the output does not depend on the number
 of threads.

 Input file (written by run_search.py):
   k W T margin presplit
   k lines  f0 f1 f2 g0 g1 g2         hallway j has f_j = f0 + f1 x + f2 y and g_j = g0 + g1 x + g2 y
   2k lines lo hi                     the intervals of E_0, in the order u^(1)_1, u^(1)_2, u^(2)_1, ...
 Usage:  csearch input.txt cert.txt [-c centre_check_depth] [-n max_nodes]
 The search stops with FAILED after about max_nodes nodes (default 4e9).
 Build:  cl -O2 -openmp csearch.c        or        gcc -O2 -fopenmp csearch.c -o csearch -lm
*/
#include <assert.h>
#include <math.h>
#include <omp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXK 16             /* hallways */
#define MAXV 64             /* vertices of a piece */
#define MAXP 4096           /* pieces of an intersection */
#define MAXC (4 + 4 * MAXK) /* half-planes that define a piece */
#define MAXTHREADS 256
#define STACK 4096 /* boxes on the stack of the depth-first search */
#define TOUCH 1e-9 /* pieces closer than this count as touching */
#define LEAF (-1)
#define FRONTIER (-2)

typedef struct {
    double x[MAXV], y[MAXV];
    int n;
} Poly;

typedef struct {
    double A, B, C; /* the half-plane A x + B y + C >= 0 */
} HalfPlane;

typedef struct {
    Poly poly;
    HalfPlane side[MAXC]; /* the piece is the intersection of these half-planes */
    int nside;
} Piece;

typedef struct {
    double lo[2 * MAXK], hi[2 * MAXK];
    int depth;
} Box;

typedef struct {
    Piece cur[MAXP], next[MAXP];
    double area[MAXP], bbox[MAXP][4], comp[MAXP];
    int parent[MAXP];
} Workspace;

/* the input */
static int K;
static double W, T, margin;
static int presplit;
static double F[MAXK][3], G[MAXK][3]; /* f_j = F[j][0] + F[j][1] x + F[j][2] y, and g_j likewise */
static Box root;

/* the options */
static int centre_depth = 1000;
static long long max_nodes = 4000000000LL;

static Piece window; /* the rectangle B_W = [0, W] x [0, 1] */
static Workspace *work[MAXTHREADS];
static volatile long long nodes_done = 0;
static volatile int failed = 0;

static void die(const char *message) {
    fprintf(stderr, "%s\n", message);
    exit(1);
}

static void add_vertex(Poly *p, double x, double y) {
    if (p->n >= MAXV) die("too many vertices (MAXV)");
    p->x[p->n] = x;
    p->y[p->n] = y;
    p->n++;
}

/* the part of the convex polygon `in` in the half-plane h; returns its number of vertices */
static int clip(const Poly *in, Poly *out, HalfPlane h) {
    int n = in->n;
    double v[MAXV], vmin = 1e300, vmax = -1e300;
    out->n = 0;
    if (n == 0) return 0;
    for (int i = 0; i < n; i++) {
        v[i] = h.A * in->x[i] + h.B * in->y[i] + h.C;
        if (v[i] < vmin) vmin = v[i];
        if (v[i] > vmax) vmax = v[i];
    }
    if (vmin >= 0) {
        *out = *in;
        return n;
    }
    if (vmax < 0) return 0;
    for (int i = 0; i < n; i++) {
        int j = (i + 1 == n) ? 0 : i + 1;
        if (v[i] >= 0) add_vertex(out, in->x[i], in->y[i]);
        if ((v[i] > 0 && v[j] < 0) || (v[i] < 0 && v[j] > 0)) {
            double t = v[i] / (v[i] - v[j]);
            add_vertex(out, in->x[i] + (in->x[j] - in->x[i]) * t, in->y[i] + (in->y[j] - in->y[i]) * t);
        }
    }
    return out->n;
}

static double area(const Poly *p) {
    double s = 0;
    if (p->n < 3) return 0;
    for (int i = 0; i < p->n; i++) {
        int j = (i + 1) % p->n;
        s += p->x[i] * p->y[j] - p->x[j] * p->y[i];
    }
    return fabs(s) * 0.5;
}

/* the half-planes h >= v and h <= v, for an affine function h = h[0] + h[1] x + h[2] y */
static HalfPlane half_plane(double A, double B, double C) {
    HalfPlane s;
    s.A = A;
    s.B = B;
    s.C = C;
    return s;
}

static HalfPlane at_least(const double *h, double v) {
    return half_plane(h[1], h[2], h[0] - v);
}

static HalfPlane at_most(const double *h, double v) {
    return half_plane(-h[1], -h[2], v - h[0]);
}

/* appends the polygon p, cut from `parent` by the half-planes `extra`, to the list out[0..*n-1] */
static void add_piece(Piece *out, int *n, const Poly *p, const Piece *parent, const HalfPlane *extra,
                      int nextra) {
    Piece *q;
    if (*n >= MAXP) die("too many pieces (MAXP)");
    q = &out[(*n)++];
    q->poly = *p;
    memcpy(q->side, parent->side, sizeof(HalfPlane) * parent->nside);
    memcpy(q->side + parent->nside, extra, sizeof(HalfPlane) * nextra);
    q->nside = parent->nside + nextra;
}

static int find(const int *parent, int i) {
    while (parent[i] != i) i = parent[i];
    return i;
}

/* whether the bounding boxes (xmin, xmax, ymin, ymax) are within TOUCH of each other */
static int boxes_close(const double *a, const double *b) {
    return !(a[1] < b[0] - TOUCH || b[1] < a[0] - TOUCH || a[3] < b[2] - TOUCH || b[3] < a[2] - TOUCH);
}

/* whether piece a meets piece b enlarged by TOUCH (each half-plane of b moved outwards by TOUCH) */
static int pieces_close(const Piece *a, const Piece *b) {
    Poly p = a->poly, q;
    for (int i = 0; i < b->nside; i++) {
        HalfPlane h = b->side[i];
        h.C += TOUCH * sqrt(h.A * h.A + h.B * h.B);
        if (!clip(&p, &q, h)) return 0;
        p = q;
    }
    return 1;
}

/*
 Gamma of the box [lo, hi] (Lemma 5.2): the largest area of a connected component of B_W cap X_E, where
 pieces within TOUCH of each other are merged. If the total area of the pieces is at most T - margin, the
 total is returned instead. *total gets the total area.
*/
static double gamma_box(const double *lo, const double *hi, double *total, Workspace *ws) {
    Piece *cur = ws->cur, *next = ws->next, *swap;
    int n = 1;
    double sum = 0, best = 0;
    cur[0] = window;
    for (int j = 0; j < K && n > 0; j++) {
        /* the union of the hallways L(u) over the box is {g <= d + 1, f <= b + 1, and f >= a or g >= c},
           taken here as the two pieces f >= a and f <= a, g >= c */
        double a = lo[2 * j], b = hi[2 * j], c = lo[2 * j + 1], d = hi[2 * j + 1];
        HalfPlane arm1[3], arm2[4];
        int m = 0;
        arm1[0] = arm2[0] = at_most(G[j], d + 1);
        arm1[1] = arm2[1] = at_most(F[j], b + 1);
        arm1[2] = at_least(F[j], a);
        arm2[2] = at_most(F[j], a);
        arm2[3] = at_least(G[j], c);
        for (int i = 0; i < n; i++) {
            Poly t1, t2, p, q;
            if (!clip(&cur[i].poly, &t1, arm1[0]) || !clip(&t1, &t2, arm1[1])) continue;
            if (clip(&t2, &p, arm1[2])) add_piece(next, &m, &p, &cur[i], arm1, 3);
            if (clip(&t2, &q, arm2[2]) && clip(&q, &p, arm2[3])) add_piece(next, &m, &p, &cur[i], arm2, 4);
        }
        swap = cur;
        cur = next;
        next = swap;
        n = m;
    }

    for (int i = 0; i < n; i++) {
        ws->area[i] = area(&cur[i].poly);
        sum += ws->area[i];
    }
    *total = sum;
    if (sum <= T - margin) return sum;

    /* connected components, by union-find */
    for (int i = 0; i < n; i++) {
        double *bb = ws->bbox[i];
        const Poly *p = &cur[i].poly;
        ws->parent[i] = i;
        bb[0] = bb[2] = 1e300;
        bb[1] = bb[3] = -1e300;
        for (int v = 0; v < p->n; v++) {
            if (p->x[v] < bb[0]) bb[0] = p->x[v];
            if (p->x[v] > bb[1]) bb[1] = p->x[v];
            if (p->y[v] < bb[2]) bb[2] = p->y[v];
            if (p->y[v] > bb[3]) bb[3] = p->y[v];
        }
    }
    for (int i = 0; i < n; i++) {
        for (int j = i + 1; j < n; j++) {
            int ri, rj;
            if (!boxes_close(ws->bbox[i], ws->bbox[j])) continue;
            ri = find(ws->parent, i);
            rj = find(ws->parent, j);
            if (ri != rj && pieces_close(&cur[i], &cur[j])) ws->parent[ri] = rj;
        }
    }
    for (int i = 0; i < n; i++) ws->comp[i] = 0;
    for (int i = 0; i < n; i++) {
        int r = find(ws->parent, i);
        ws->comp[r] += ws->area[i];
        if (ws->comp[r] > best) best = ws->comp[r];
    }
    return best;
}

static int widest(const Box *b) {
    int k = 0;
    double width = -1;
    for (int i = 0; i < 2 * K; i++) {
        if (b->hi[i] - b->lo[i] > width) {
            width = b->hi[i] - b->lo[i];
            k = i;
        }
    }
    return k;
}

static void bisect(const Box *b, int k, Box *lower, Box *upper) {
    double m = 0.5 * (b->lo[k] + b->hi[k]);
    *lower = *upper = *b;
    lower->hi[k] = upper->lo[k] = m;
    lower->depth = upper->depth = b->depth + 1;
}

/* LEAF if the box is a leaf, otherwise the coordinate to bisect; *value gets Gamma of the box */
static int evaluate(const Box *b, Workspace *ws, double *value) {
    double total;
    *value = gamma_box(b->lo, b->hi, &total, ws);
    if (*value <= T - margin) return LEAF;
    if (b->depth <= centre_depth) {
        double centre[2 * MAXK] = {0}, g;
        for (int i = 0; i < 2 * K; i++) centre[i] = 0.5 * (b->lo[i] + b->hi[i]);
        g = gamma_box(centre, centre, &total, ws);
        if (g > T + 1e-9) {
            failed = 1;
            fprintf(stderr, "FAIL: Gamma at the centre of a box is %.9f > T\n", g);
        }
    }
    return widest(b);
}

/* a growable list of tokens: LEAF, or k >= 0 for a bisection of coordinate k */
typedef struct {
    signed char *t;
    long n, cap;
} Tokens;

static void push(Tokens *tk, int token) {
    if (tk->n == tk->cap) {
        signed char *t;
        tk->cap = tk->cap ? 2 * tk->cap : 1 << 16;
        t = realloc(tk->t, tk->cap);
        if (!t) die("out of memory");
        tk->t = t;
    }
    tk->t[tk->n++] = (signed char)token;
}

/* adds n nodes to the shared count and stops the search at the node limit */
static void count_nodes(long n) {
    long long total;
#pragma omp critical
    {
        nodes_done += n;
        total = nodes_done;
    }
    if (total > max_nodes && !failed) {
        failed = 1;
        fprintf(stderr, "ABORT: node limit %lld reached\n", max_nodes);
    }
}

/* the result of searching one subtree */
typedef struct {
    Tokens tokens; /* in preorder */
    long nodes;
    double worst; /* the largest value of a leaf */
} Subtree;

/* depth-first search of the subtree at `top` */
static void search_subtree(const Box *top, Subtree *out, Workspace *ws) {
    Box *stack = malloc(sizeof(Box) * STACK);
    int sp = 0;
    if (!stack) die("out of memory");
    stack[sp++] = *top;
    while (sp > 0 && !failed) {
        Box b = stack[--sp];
        double value;
        int k;
        if ((++out->nodes & 0xFFFF) == 0) count_nodes(0x10000);
        k = evaluate(&b, ws, &value);
        if (k == LEAF) {
            push(&out->tokens, LEAF);
            if (value > out->worst) out->worst = value;
        } else {
            push(&out->tokens, k);
            if (sp + 2 >= STACK) die("stack overflow");
            bisect(&b, k, &stack[sp + 1], &stack[sp]); /* the lower half is searched first */
            sp += 2;
        }
    }
    count_nodes(out->nodes & 0xFFFF);
    free(stack);
}

/* the top of the tree, expanded breadth first; the children of a node are consecutive */
typedef struct {
    Box box;
    int kind;  /* LEAF, k >= 0 for a bisection of coordinate k, or FRONTIER for an open box */
    int child; /* the index of the lower child of a bisected node; the upper child follows it */
} Node;

static Node *tree;
static int ntree, tree_cap;

static int add_node(const Box *b) {
    if (ntree == tree_cap) {
        Node *t;
        tree_cap = tree_cap ? 2 * tree_cap : 1024;
        t = realloc(tree, sizeof(Node) * tree_cap);
        if (!t) die("out of memory");
        tree = t;
    }
    tree[ntree].box = *b;
    tree[ntree].kind = FRONTIER;
    tree[ntree].child = -1;
    return ntree++;
}

/* expands the top of the tree breadth first until `presplit` boxes are open. Since the nodes are numbered
   in breadth-first order, the open boxes are then the nodes head, ..., ntree - 1; returns head. */
static int expand_top(double *largest) {
    int head = 0;
    add_node(&root);
    while (head < ntree && ntree - head < presplit) {
        int id = head++, k;
        double value;
        Box lower, upper;
        k = evaluate(&tree[id].box, work[0], &value);
        tree[id].kind = k;
        if (k == LEAF) {
            if (value > *largest) *largest = value;
            continue;
        }
        bisect(&tree[id].box, k, &lower, &upper);
        tree[id].child = add_node(&lower);
        add_node(&upper);
    }
    return head;
}

/* writes the tokens of a subtree; returns its number of leaves */
static long write_tokens(FILE *out, const Tokens *tk) {
    char *buf = malloc(3 * tk->n + 8);
    long len = 0, leaves = 0;
    if (!buf) die("out of memory");
    for (long i = 0; i < tk->n; i++) {
        int v = tk->t[i];
        if (v == LEAF) {
            buf[len++] = 'L';
            leaves++;
        } else {
            if (v >= 10) buf[len++] = (char)('0' + v / 10);
            buf[len++] = (char)('0' + v % 10);
        }
        buf[len++] = ' ';
    }
    fwrite(buf, 1, len, out);
    free(buf);
    return leaves;
}

/* writes the tree in preorder, with the tokens of subtree i in place of the open box head + i */
static void write_certificate(const char *path, int head, Subtree *sub, long *nodes, long *leaves,
                              double *largest) {
    FILE *out = fopen(path, "w");
    int *stack, sp = 0;
    assert(ntree >= 1);
    stack = malloc(sizeof(int) * ((size_t)ntree + 16));
    if (!out) die("cannot create the certificate file");
    if (!stack) die("out of memory");
    stack[sp++] = 0;
    while (sp > 0) {
        int id = stack[--sp];
        const Node *nd = &tree[id];
        if (nd->kind == FRONTIER) {
            Subtree *s = &sub[id - head];
            *leaves += write_tokens(out, &s->tokens);
            *nodes += s->nodes;
            if (s->worst > *largest) *largest = s->worst;
            free(s->tokens.t);
        } else if (nd->kind == LEAF) {
            fputs("L ", out);
            (*leaves)++;
            (*nodes)++;
        } else {
            fprintf(out, "%d ", nd->kind);
            (*nodes)++;
            stack[sp++] = nd->child + 1;
            stack[sp++] = nd->child;
        }
    }
    free(stack);
    if (fclose(out) != 0) die("cannot write the certificate file");
}

static void read_input(const char *path) {
    FILE *in = fopen(path, "r");
    int ok;
    if (!in) {
        fprintf(stderr, "cannot open %s\n", path);
        exit(1);
    }
    ok = fscanf(in, "%d %lf %lf %lf %d", &K, &W, &T, &margin, &presplit) == 5 && K >= 1 && K <= MAXK &&
         presplit >= 1;
    for (int j = 0; ok && j < K; j++)
        ok = fscanf(in, "%lf %lf %lf %lf %lf %lf", &F[j][0], &F[j][1], &F[j][2], &G[j][0], &G[j][1],
                    &G[j][2]) == 6;
    for (int i = 0; ok && i < 2 * K; i++) ok = fscanf(in, "%lf %lf", &root.lo[i], &root.hi[i]) == 2;
    fclose(in);
    if (!ok) {
        fprintf(stderr, "malformed input file %s\n", path);
        exit(1);
    }
    root.depth = 0;
}

/* a whole-number command-line argument */
static long long parse_number(const char *s) {
    char *end;
    long long v = strtoll(s, &end, 10);
    if (end == s || *end) die("bad number on the command line");
    return v;
}

static void make_window(void) {
    window.poly.n = 0;
    add_vertex(&window.poly, 0, 0);
    add_vertex(&window.poly, W, 0);
    add_vertex(&window.poly, W, 1);
    add_vertex(&window.poly, 0, 1);
    window.side[0] = half_plane(1, 0, 0);  /* x >= 0 */
    window.side[1] = half_plane(-1, 0, W); /* x <= W */
    window.side[2] = half_plane(0, 1, 0);  /* y >= 0 */
    window.side[3] = half_plane(0, -1, 1); /* y <= 1 */
    window.nside = 4;
}

int main(int argc, char **argv) {
    int nthreads, head, nfront, i;
    long nodes = 0, leaves = 0;
    double largest = 0, t0;
    Subtree *sub;

    if (argc < 3 || argc % 2 == 0) die("usage: csearch input.txt cert.txt [-c depth] [-n max_nodes]");
    read_input(argv[1]);
    for (int a = 3; a + 1 < argc; a += 2) {
        if (!strcmp(argv[a], "-c"))
            centre_depth = (int)parse_number(argv[a + 1]);
        else if (!strcmp(argv[a], "-n"))
            max_nodes = parse_number(argv[a + 1]);
        else
            die("usage: csearch input.txt cert.txt [-c depth] [-n max_nodes]");
    }
    make_window();
    nthreads = omp_get_max_threads();
    if (nthreads > MAXTHREADS) {
        nthreads = MAXTHREADS;
        omp_set_num_threads(nthreads);
    }
    for (int t = 0; t < nthreads; t++) {
        work[t] = malloc(sizeof(Workspace));
        if (!work[t]) die("out of memory");
    }
    t0 = omp_get_wtime();

    head = expand_top(&largest);
    assert(0 <= head && head <= ntree);
    nfront = ntree - head;
    sub = calloc((size_t)nfront + 1, sizeof(Subtree));
    if (!sub) die("out of memory");
#pragma omp parallel for schedule(dynamic, 1)
    for (i = 0; i < nfront; i++) search_subtree(&tree[head + i].box, &sub[i], work[omp_get_thread_num()]);
    if (failed) {
        printf("FAILED\n");
        exit(2);
    }
    write_certificate(argv[2], head, sub, &nodes, &leaves, &largest);
    printf("certificate written: %ld nodes, %ld leaves, largest leaf value %.9f, %.1f s, %d threads, "
           "%d subtrees\n",
           nodes, leaves, largest, omp_get_wtime() - t0, nthreads, nfront);
    free(sub);
    return 0;
}
