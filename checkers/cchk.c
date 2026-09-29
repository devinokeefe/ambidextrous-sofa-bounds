/*
 cchk.c -- checks a certificate for G(A;B) <= T (Section 5 of the paper) in exact integer arithmetic.

 For every leaf box E of the certificate tree it checks
   Gamma(E) = lambda*( B_W  cap  cap_j Xhat_j ) <= T,   B_W = [0,W] x [0,1],
   Xhat_j = {a <= f_j <= b+1, g_j <= d+1}  U  {f_j <= a, c <= g_j <= d+1}          (Lemma 5.2),
 where lambda* is the largest area of a connected component, found from the contact graph of the closed
 convex pieces (degenerate pieces are kept; Section 5.3). The root box is E_0 of Lemma 5.1. The program
 also checks that each angle is given by a Pythagorean triple, that W >= min_j W_{a_j}, that the tokens
 form a complete binary tree in preorder, and that every split is at a midpoint.

 Arithmetic. The plane is scaled by M = den(W) * 2^Dk, where Dk is the largest number of splits of a single
 coordinate on one path of the tree. Every box endpoint of hallway j, multiplied by M h_j, is then an integer,
 and every half-plane has the form A X + B Y <= C with small integers A, B and a 64-bit C, where X = M x,
 Y = M y. With L the lcm of |det| over all pairs of non-parallel boundary directions, every vertex has integer
 coordinates L X, L Y, stored as 128-bit integers, and twice an area times (L M)^2 is an exact 256-bit
 integer. Every addition and multiplication is checked for overflow; an overflow stops the program with
 "CERTIFICATE NOT VERIFIED".
 The two numbers W and T read from the spec file are parsed with unchecked 64-bit arithmetic, so they must be
 positive with at most 18 digits in numerator and denominator.

 The tree is cut at depth `cut` into subtrees, which are checked in parallel (OpenMP).

 Usage:  cchk spec.json [threads=4] [cut=18]
 Exit status 0 if the certificate is valid, 1 if a leaf exceeds T, 2 if it could not be checked.
 Build:  cl -O2 -openmp cchk.c                              (MSVC)
         gcc -O2 -fopenmp -I portable cchk.c -o cchk         (gcc or clang, see portable/intrin.h)
*/
#include <intrin.h>
#include <omp.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef int64_t i64;
typedef uint64_t u64;

#define MAXH 12               /* hallways */
#define MAXC (2 * MAXH)       /* box coordinates */
#define MAXDIR (4 + 4 * MAXH) /* directions of boundary lines */
#define NLINE (4 + 5 * MAXH)  /* boundary lines: 4 of B_W and 5 for each hallway */
#define VMAX 160              /* vertices of a polygon */
#define MAXSTACK 512          /* depth of the tree */

static void die(const char *message) {
    printf("FATAL: %s\nCERTIFICATE NOT VERIFIED\n", message);
    fflush(stdout);
    exit(2);
}

/* ---------------------------------------------------------------- 128-bit signed integers */

typedef struct {
    u64 lo;
    i64 hi;
} i128;

static inline i128 i128_from(i64 x) {
    i128 r;
    r.lo = (u64)x;
    r.hi = (x < 0) ? -1 : 0;
    return r;
}

static inline int sgn128(i128 a) {
    if (a.hi < 0) return -1;
    return (a.hi > 0 || a.lo) ? 1 : 0;
}

static inline int eq128(i128 a, i128 b) {
    return a.lo == b.lo && a.hi == b.hi;
}

static inline int lt128(i128 a, i128 b) {
    return (a.hi < b.hi) || (a.hi == b.hi && a.lo < b.lo);
}

static inline i128 neg128(i128 a) {
    i128 r;
    if (a.hi == INT64_MIN && a.lo == 0) die("i128 neg overflow");
    r.lo = ~a.lo + 1;
    r.hi = (i64)(~(u64)a.hi + (r.lo == 0 ? 1 : 0));
    return r;
}

static inline i128 add128(i128 a, i128 b) {
    i128 r;
    u64 carry;
    r.lo = a.lo + b.lo;
    carry = (r.lo < a.lo) ? 1 : 0;
    r.hi = (i64)((u64)a.hi + (u64)b.hi + carry);
    if (((a.hi ^ r.hi) & (b.hi ^ r.hi)) < 0) die("i128 add overflow");
    return r;
}

static inline i128 sub128(i128 a, i128 b) {
    return add128(a, neg128(b));
}

static inline i128 mul64x64(i64 a, i64 b) {
    i128 r;
    i64 hi;
    r.lo = (u64)_mul128(a, b, &hi);
    r.hi = hi;
    return r;
}

static inline i128 mul128x64(i128 x, i64 a) {
    int negative = 0;
    u64 ua, h0, l0, h1, hi;
    i128 r;
    if (a == 0 || (x.hi == 0 && x.lo == 0)) return i128_from(0);
    if (x.hi < 0) {
        x = neg128(x);
        negative ^= 1;
    }
    if (a < 0) {
        if (a == INT64_MIN) die("i128 mul overflow");
        ua = (u64)(-a);
        negative ^= 1;
    } else {
        ua = (u64)a;
    }
    l0 = _umul128(x.lo, ua, &h0);
    hi = _umul128((u64)x.hi, ua, &h1);
    if (h1) die("i128 mul overflow");
    hi += h0;
    if (hi < h0 || (hi >> 63)) die("i128 mul overflow");
    r.lo = l0;
    r.hi = (i64)hi;
    return negative ? neg128(r) : r;
}

static inline i64 to64(i128 a) {
    if (!((a.hi == 0 && !(a.lo >> 63)) || (a.hi == -1 && (a.lo >> 63)))) die("value does not fit int64");
    return (i64)a.lo;
}

/* ------------------------------------------------ 256-bit signed integers (two's complement) */

typedef struct {
    u64 w[4];
} i256;

static inline i256 zero256(void) {
    i256 r;
    r.w[0] = r.w[1] = r.w[2] = r.w[3] = 0;
    return r;
}

static inline int sgn256(i256 a) {
    if ((i64)a.w[3] < 0) return -1;
    return (a.w[0] | a.w[1] | a.w[2] | a.w[3]) ? 1 : 0;
}

static inline i256 add256(i256 a, i256 b) {
    i256 r;
    unsigned char c = 0;
    c = _addcarry_u64(c, a.w[0], b.w[0], &r.w[0]);
    c = _addcarry_u64(c, a.w[1], b.w[1], &r.w[1]);
    c = _addcarry_u64(c, a.w[2], b.w[2], &r.w[2]);
    _addcarry_u64(c, a.w[3], b.w[3], &r.w[3]);
    if ((((i64)(a.w[3] ^ r.w[3])) & ((i64)(b.w[3] ^ r.w[3]))) < 0) die("i256 add overflow");
    return r;
}

static inline i256 neg256(i256 a) {
    i256 r;
    unsigned char c = 1;
    if (a.w[3] == 0x8000000000000000ULL && !(a.w[0] | a.w[1] | a.w[2])) die("i256 neg overflow");
    c = _addcarry_u64(c, ~a.w[0], 0, &r.w[0]);
    c = _addcarry_u64(c, ~a.w[1], 0, &r.w[1]);
    c = _addcarry_u64(c, ~a.w[2], 0, &r.w[2]);
    _addcarry_u64(c, ~a.w[3], 0, &r.w[3]);
    return r;
}

static inline i256 sub256(i256 a, i256 b) {
    return add256(a, neg256(b));
}

static inline int cmp256(i256 a, i256 b) {
    return sgn256(sub256(a, b));
}

/* the exact product; |a|, |b| < 2^127, so |a b| < 2^254 */
static inline i256 mul128x128(i128 a, i128 b) {
    int negative = 0;
    u64 p00h, p00l, p01h, p01l, p10h, p10l, p11h, p11l;
    i256 r;
    unsigned char c;
    if (a.hi < 0) {
        a = neg128(a);
        negative ^= 1;
    }
    if (b.hi < 0) {
        b = neg128(b);
        negative ^= 1;
    }
    p00l = _umul128(a.lo, b.lo, &p00h);
    p01l = _umul128(a.lo, (u64)b.hi, &p01h);
    p10l = _umul128((u64)a.hi, b.lo, &p10h);
    p11l = _umul128((u64)a.hi, (u64)b.hi, &p11h);
    r.w[0] = p00l;
    c = _addcarry_u64(0, p00h, p01l, &r.w[1]);
    c = _addcarry_u64(c, p01h, p11l, &r.w[2]);
    _addcarry_u64(c, p11h, 0, &r.w[3]);
    c = _addcarry_u64(0, r.w[1], p10l, &r.w[1]);
    c = _addcarry_u64(c, r.w[2], p10h, &r.w[2]);
    _addcarry_u64(c, r.w[3], 0, &r.w[3]);
    if (r.w[3] >> 63) die("i256 mul overflow");
    return negative ? neg256(r) : r;
}

static i256 mul256x64(i256 a, u64 s) {
    int negative = 0;
    u64 carry = 0, h, l;
    unsigned char c;
    i256 r;
    if (sgn256(a) < 0) {
        a = neg256(a);
        negative = 1;
    }
    for (int i = 0; i < 4; i++) {
        l = _umul128(a.w[i], s, &h);
        c = _addcarry_u64(0, l, carry, &r.w[i]);
        carry = h + c;
    }
    if (carry || (r.w[3] >> 63)) die("i256 small-mul overflow");
    return negative ? neg256(r) : r;
}

static double to_double(i256 a) {
    int negative = 0;
    double d;
    if (sgn256(a) < 0) {
        a = neg256(a);
        negative = 1;
    }
    d = (double)a.w[3];
    d = d * 18446744073709551616.0 + (double)a.w[2];
    d = d * 18446744073709551616.0 + (double)a.w[1];
    d = d * 18446744073709551616.0 + (double)a.w[0];
    return negative ? -d : d;
}

/* ---------------------------------------------------------------- the problem (fixed after setup) */

static int nhall;                  /* number of hallways */
static i64 hyp[MAXH];              /* h_j, the hypotenuse of the triple of hallway j */
static i64 F[MAXH][3], G[MAXH][3]; /* h_j f_j = F[j][0] + F[j][1] x + F[j][2] y, and h_j g_j likewise */
static i64 Wn, Wd, Tn, Td;         /* W = Wn/Wd, T = Tn/Td */
static int Dk;                     /* the largest number of splits of one coordinate on a path */
static i64 M, MW, L;               /* the scale M, M W, and the lcm L of the determinants */
static i64 Mh[MAXH], MF0[MAXH], MG0[MAXH]; /* M h_j, M F[j][0], M G[j][0] */
static i64 root_lo[MAXC], root_hi[MAXC];   /* E_0, coordinate 2j + i scaled by M h_j */
static int ndir;                           /* the directions (A, B) of the boundary lines */
static i64 dir_A[MAXDIR], dir_B[MAXDIR];
static i64 inv_det[MAXDIR][MAXDIR]; /* L / det(direction i, direction k), 0 if they are parallel */
static int dir_f[MAXH], dir_fneg[MAXH], dir_g[MAXH], dir_gneg[MAXH]; /* of +-(F1, F2) and +-(G1, G2) */
static i256 T_scaled; /* 2 Tn (M L)^2: an area with V = 2 area (M L)^2 is at most T iff Td V <= T_scaled */
static double area_scale; /* 2 (M L)^2 as a double, for printing areas */

static i64 gcd64(i64 a, i64 b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) {
        i64 t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int dir_index(i64 A, i64 B) {
    for (int i = 0; i < ndir; i++)
        if (dir_A[i] == A && dir_B[i] == B) return i;
    if (ndir >= MAXDIR) die("too many directions");
    dir_A[ndir] = A;
    dir_B[ndir] = B;
    return ndir++;
}

/* ---------------------------------------------------------------- exact geometry */

typedef struct {
    i64 A, B, C; /* the half-plane A X + B Y <= C */
    i128 CL;     /* C L */
    int dir;     /* the index of the direction (A, B) */
} Line;

typedef struct {
    i128 X, Y; /* L X and L Y */
    int e;     /* the index of the line through this vertex and the next */
} Vertex;

typedef struct {
    int n;
    Vertex v[VMAX];
} Poly;

static Line rect_line[4]; /* B_W: bottom, right, top, left */
static Poly rect;

static inline void set_line(Line *l, i64 A, i64 B, i64 C, int dir) {
    l->A = A;
    l->B = B;
    l->C = C;
    l->CL = mul64x64(C, L);
    l->dir = dir;
}

static inline void copy_poly(Poly *to, const Poly *from) {
    memcpy(to, from, offsetof(Poly, v) + from->n * sizeof(Vertex));
}

/* the sign of A (L X) + B (L Y) - C L: at most 0 if the vertex is in the half-plane */
static inline int side(const Line *l, const Vertex *p) {
    return sgn128(sub128(add128(mul128x64(p->X, l->A), mul128x64(p->Y, l->B)), l->CL));
}

/* the intersection point of the boundary lines of e and h */
static void cross(const Line *e, const Line *h, Vertex *out) {
    i64 q = inv_det[e->dir][h->dir];
    i128 nx, ny;
    if (q == 0) die("crossing of parallel lines");
    /* X = (Ce Bh - Ch Be) / det and Y = (Ae Ch - Ah Ce) / det, with det = Ae Bh - Ah Be and q = L / det */
    nx = sub128(mul64x64(e->C, h->B), mul64x64(h->C, e->B));
    ny = sub128(mul64x64(e->A, h->C), mul64x64(h->A, e->C));
    out->X = mul128x64(nx, q);
    out->Y = mul128x64(ny, q);
}

static inline void add_vertex(Poly *o, const Vertex *v, int e) {
    if (o->n > 0 && eq128(o->v[o->n - 1].X, v->X) && eq128(o->v[o->n - 1].Y, v->Y)) {
        o->v[o->n - 1].e = e; /* an edge of length zero: drop the earlier vertex */
        return;
    }
    if (o->n >= VMAX) die("VMAX exceeded");
    o->v[o->n].X = v->X;
    o->v[o->n].Y = v->Y;
    o->v[o->n].e = e;
    o->n++;
}

/* o = P cap (half-plane of line h), by exact Sutherland-Hodgman clipping; degenerate results are kept */
static void clip(const Poly *P, const Line *lines, int h, Poly *o) {
    const Line *H = &lines[h];
    int s[VMAX], n = P->n, all_in = 1, all_out = 1;
    Vertex I;
    o->n = 0;
    if (n == 0) return;
    for (int k = 0; k < n; k++) {
        s[k] = side(H, &P->v[k]);
        if (s[k] > 0)
            all_in = 0;
        else
            all_out = 0;
    }
    if (all_out) return;
    if (all_in) {
        copy_poly(o, P);
        return;
    }
    for (int k = 0; k < n; k++) {
        int next = (k + 1 == n) ? 0 : k + 1;
        const Vertex *p = &P->v[k];
        if (s[k] <= 0) {
            add_vertex(o, p, p->e);
            if (s[next] > 0) {
                cross(&lines[p->e], H, &I);
                add_vertex(o, &I, h);
            }
        } else if (s[next] <= 0) {
            cross(&lines[p->e], H, &I);
            add_vertex(o, &I, p->e);
        }
    }
    while (o->n > 1 && eq128(o->v[o->n - 1].X, o->v[0].X) && eq128(o->v[o->n - 1].Y, o->v[0].Y)) o->n--;
}

/* 2 area (L M)^2 */
static i256 twice_area(const Poly *P) {
    i256 s = zero256();
    for (int k = 0; k < P->n; k++) {
        const Vertex *a = &P->v[k], *b = &P->v[(k + 1) % P->n];
        s = add256(s, sub256(mul128x128(a->X, b->Y), mul128x128(b->X, a->Y)));
    }
    if (sgn256(s) < 0) die("negative polygon area (orientation bug)");
    return s;
}

/* whether an area, given as 2 area (L M)^2, is at most T */
static int at_most_T(i256 area2) {
    return cmp256(mul256x64(area2, (u64)Td), T_scaled) <= 0;
}

/* ---------------------------------------------------------------- one leaf */

typedef struct {
    Poly poly;
    unsigned arms; /* bit j is set if the piece lies in the second part {f_j <= a, g_j >= c} of Xhat_j */
    i256 area2;    /* 2 area (L M)^2 */
    i128 x0, x1, y0, y1; /* the bounding box */
} Piece;

typedef struct {
    Line line[NLINE];                        /* B_W, then 5 lines for each hallway (see set_lines) */
    Poly bufA[MAXH], bufB[MAXH], bufC[MAXH]; /* for each level of add_pieces */
    Piece *piece;                            /* room for 2^nhall pieces */
    int npiece;
    Poly t1, t2; /* for meets */
    int parent[1 << MAXH];
    i256 comp[1 << MAXH];
} Work;

/* the boundary lines of the leaf box [lo, hi] (all multiplied by M h_j) */
static void set_lines(Work *w, const i64 *lo, const i64 *hi) {
    memcpy(w->line, rect_line, sizeof(rect_line));
    for (int j = 0; j < nhall; j++) {
        i64 a = lo[2 * j], b = hi[2 * j], c = lo[2 * j + 1], d = hi[2 * j + 1];
        Line *l = &w->line[4 + 5 * j];
        set_line(&l[0], G[j][1], G[j][2], d + Mh[j] - MG0[j], dir_g[j]); /* g <= d + 1 */
        set_line(&l[1], F[j][1], F[j][2], b + Mh[j] - MF0[j], dir_f[j]); /* f <= b + 1 */
        set_line(&l[2], -F[j][1], -F[j][2], MF0[j] - a, dir_fneg[j]);    /* f >= a */
        set_line(&l[3], F[j][1], F[j][2], a - MF0[j], dir_f[j]);         /* f <= a */
        set_line(&l[4], -G[j][1], -G[j][2], MG0[j] - c, dir_gneg[j]);    /* g >= c */
    }
}

/* the pieces of P cap Xhat_j cap ... cap Xhat_{nhall-1}, one for each choice of parts, added to w->piece */
static void add_pieces(Work *w, int j, const Poly *P, unsigned arms) {
    Poly *A, *B, *C;
    int base = 4 + 5 * j;
    if (j == nhall) {
        Piece *q = &w->piece[w->npiece++];
        copy_poly(&q->poly, P);
        q->arms = arms;
        q->area2 = twice_area(P);
        q->x0 = q->x1 = P->v[0].X;
        q->y0 = q->y1 = P->v[0].Y;
        for (int k = 1; k < P->n; k++) {
            if (lt128(P->v[k].X, q->x0)) q->x0 = P->v[k].X;
            if (lt128(q->x1, P->v[k].X)) q->x1 = P->v[k].X;
            if (lt128(P->v[k].Y, q->y0)) q->y0 = P->v[k].Y;
            if (lt128(q->y1, P->v[k].Y)) q->y1 = P->v[k].Y;
        }
        return;
    }
    A = &w->bufA[j];
    B = &w->bufB[j];
    C = &w->bufC[j];
    clip(P, w->line, base + 0, A); /* g <= d + 1 (both parts) */
    if (!A->n) return;
    clip(A, w->line, base + 1, B); /* f <= b + 1 (both parts) */
    if (!B->n) return;
    clip(B, w->line, base + 2, A); /* part 1: f >= a */
    if (A->n) add_pieces(w, j + 1, A, arms);
    clip(B, w->line, base + 3, C); /* part 2: f <= a, g >= c */
    if (C->n) {
        clip(C, w->line, base + 4, A);
        if (A->n) add_pieces(w, j + 1, A, arms | (1u << j));
    }
}

static int uf_find(int *parent, int x) {
    while (parent[x] != x) {
        parent[x] = parent[parent[x]];
        x = parent[x];
    }
    return x;
}

/* whether the closed pieces pi and pk meet: pi is clipped by the half-planes of pk that it does not share */
static int meets(Work *w, const Piece *pi, const Piece *pk) {
    const Poly *cur = &pi->poly;
    Poly *out = &w->t1, *spare = &w->t2, *t;
    if (lt128(pi->x1, pk->x0) || lt128(pk->x1, pi->x0) || lt128(pi->y1, pk->y0) || lt128(pk->y1, pi->y0))
        return 0;
    for (int j = 0; j < nhall; j++) {
        unsigned ai = (pi->arms >> j) & 1u, ak = (pk->arms >> j) & 1u;
        int base = 4 + 5 * j;
        if (ai == ak) continue;
        if (ak == 0) {
            clip(cur, w->line, base + 2, out);
            if (!out->n) return 0;
            cur = out;
            t = out;
            out = spare;
            spare = t;
        } else {
            clip(cur, w->line, base + 3, out);
            if (!out->n) return 0;
            cur = out;
            t = out;
            out = spare;
            spare = t;
            clip(cur, w->line, base + 4, out);
            if (!out->n) return 0;
            cur = out;
            t = out;
            out = spare;
            spare = t;
        }
    }
    return 1;
}

/*
 Whether Gamma(E) <= T for the leaf box E = [lo, hi]. *value gets the certified value, as 2 area (L M)^2:
 the total area of the pieces if that is at most T, and otherwise the largest area of a connected
 component. *used_components tells which.
*/
static int check_leaf(Work *w, const i64 *lo, const i64 *hi, i256 *value, int *used_components) {
    i256 total = zero256(), best = zero256();
    int n;
    set_lines(w, lo, hi);
    w->npiece = 0;
    add_pieces(w, 0, &rect, 0);
    n = w->npiece;
    for (int i = 0; i < n; i++) total = add256(total, w->piece[i].area2);
    *used_components = 0;
    if (at_most_T(total)) {
        *value = total;
        return 1;
    }
    *used_components = 1;
    for (int i = 0; i < n; i++) w->parent[i] = i;
    for (int i = 0; i < n; i++) {
        for (int k = i + 1; k < n; k++) {
            int ri = uf_find(w->parent, i), rk = uf_find(w->parent, k);
            if (ri != rk && meets(w, &w->piece[i], &w->piece[k])) w->parent[ri] = rk;
        }
    }
    for (int i = 0; i < n; i++) w->comp[i] = zero256();
    for (int i = 0; i < n; i++) {
        int r = uf_find(w->parent, i);
        w->comp[r] = add256(w->comp[r], w->piece[i].area2);
    }
    for (int i = 0; i < n; i++)
        if (cmp256(w->comp[i], best) > 0) best = w->comp[i];
    *value = best;
    return at_most_T(best);
}

/* ---------------------------------------------------------------- the spec file */

static char *read_file(const char *path, size_t *len) {
    FILE *f = fopen(path, "rb");
    char *b;
    long n;
    if (!f) {
        printf("cannot open %s\n", path);
        die("open");
    }
    fseek(f, 0, SEEK_END);
    n = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (n < 0) die("cannot read the file (on Windows, files over 2 GB are not supported)");
    b = malloc((size_t)n + 1);
    if (!b) die("malloc");
    if (fread(b, 1, (size_t)n, f) != (size_t)n) die("read");
    b[n] = 0; /* NOLINT(clang-analyzer-security.ArrayBound): b has n + 1 bytes */
    fclose(f);
    if (len) *len = (size_t)n;
    return b;
}

/* the string value of "key" in the JSON text js */
static char *json_string(const char *js, const char *key, char *out, int cap) {
    char pattern[64];
    const char *p, *q;
    snprintf(pattern, sizeof pattern, "\"%s\"", key);
    p = strstr(js, pattern);
    if (!p) die("spec key missing");
    p = strchr(p + strlen(pattern), ':');
    if (!p) die("spec");
    p = strchr(p, '"');
    if (!p) die("spec value not a string");
    q = strchr(p + 1, '"');
    if (!q || q - p - 1 >= cap) die("spec");
    memcpy(out, p + 1, q - p - 1);
    out[q - p - 1] = 0;
    return out;
}

/* a fraction "p/q", a decimal "12.345" or an integer, in lowest terms */
static void parse_fraction(const char *s, i64 *num, i64 *den) {
    const char *slash = strchr(s, '/'), *dot = strchr(s, '.');
    i64 g;
    if (slash) {
        *num = _strtoi64(s, NULL, 10);
        *den = _strtoi64(slash + 1, NULL, 10);
    } else if (dot) {
        i64 whole = _strtoi64(s, NULL, 10), frac = 0, d = 1;
        if (s[0] == '-') die("negative decimal");
        for (const char *p = dot + 1; *p >= '0' && *p <= '9'; p++) {
            frac = frac * 10 + (*p - '0');
            d *= 10;
        }
        *num = whole * d + frac;
        *den = d;
    } else {
        *num = _strtoi64(s, NULL, 10);
        *den = 1;
    }
    if (*den <= 0) die("bad rational");
    g = gcd64(*num, *den);
    *num /= g;
    *den /= g;
}

/* one hallway [q, p, r, sign, flip, mirrored]: sin = sign p/r, cos = q/r, turned by 180 degrees if flip */
static void add_hallway(const i64 *v, i64 *Wmin_n, i64 *Wmin_d) {
    i64 a = v[0], b = v[1], c = v[2], sign = v[3], flip = v[4], mirrored = v[5], C, S, wn, wd;
    if (nhall >= MAXH) die("too many hallways");
    if (a <= 0 || b <= 0 || c <= 0 || !eq128(add128(mul64x64(a, a), mul64x64(b, b)), mul64x64(c, c)))
        die("not a Pythagorean triple");
    if (!(sign == 1 || sign == -1) || !(flip == 0 || flip == 1) || !(mirrored == 0 || mirrored == 1))
        die("flags");
    C = a; /* h cos and h sin */
    S = sign * b;
    if (flip) {
        C = -C;
        S = -S;
    }
    hyp[nhall] = c;
    if (!mirrored) { /* f = x cos + y sin, g = -x sin + y cos */
        F[nhall][0] = 0;
        F[nhall][1] = C;
        F[nhall][2] = S;
        G[nhall][0] = 0;
        G[nhall][1] = -S;
        G[nhall][2] = C;
    } else { /* f and g at rho(x, y) = (x, 1 - y) */
        F[nhall][0] = S;
        F[nhall][1] = C;
        F[nhall][2] = -S;
        G[nhall][0] = C;
        G[nhall][1] = -S;
        G[nhall][2] = -C;
    }
    /* W_a = (1 + |s|)/|c| + (1 + |c|)/|s| = ((c + b) b + (c + a) a) / (a b) */
    wn = to64(add128(mul64x64(c + b, b), mul64x64(c + a, a)));
    wd = to64(mul64x64(a, b));
    if (nhall == 0 || lt128(mul64x64(wn, *Wmin_d), mul64x64(*Wmin_n, wd))) {
        *Wmin_n = wn;
        *Wmin_d = wd;
    }
    nhall++;
}

static void read_spec(const char *spec_path, char *cert_path) {
    char *js = read_file(spec_path, NULL), buf[256];
    const char *p;
    i64 Wmin_n = 0, Wmin_d = 1;
    p = strstr(js, "\"hallways\"");
    if (!p) die("no hallways");
    p = strchr(p, '[');
    if (!p) die("hallways");
    p++;
    nhall = 0;
    for (;;) {
        i64 v[6];
        while (*p == ' ' || *p == ',') p++;
        if (*p == ']') break;
        if (*p != '[') die("hallway list syntax");
        p++;
        for (int i = 0; i < 6; i++) {
            char *end;
            while (*p == ' ' || *p == ',') p++;
            v[i] = _strtoi64(p, &end, 10);
            if (end == p) die("hallway number");
            p = end;
        }
        while (*p == ' ') p++;
        if (*p != ']') die("hallway entry must have 6 integers");
        p++;
        add_hallway(v, &Wmin_n, &Wmin_d);
    }
    parse_fraction(json_string(js, "W", buf, sizeof buf), &Wn, &Wd);
    parse_fraction(json_string(js, "T", buf, sizeof buf), &Tn, &Td);
    json_string(js, "cert", cert_path, 1024);
    free(js);
    if (nhall < 1) die("no hallways");
    if (lt128(mul64x64(Wn, Wmin_d), mul64x64(Wmin_n, Wd))) die("W < min_a W_a (Lemma 5.1)");
    printf("spec %s: %d hallways, W=%lld/%lld (min W_a=%lld/%lld = %.6f), T=%lld/%lld = %.9f\n", spec_path,
           nhall, (long long)Wn, (long long)Wd, (long long)Wmin_n, (long long)Wmin_d,
           (double)Wmin_n / (double)Wmin_d, (long long)Tn, (long long)Td, (double)Tn / (double)Td);
    for (int j = 0; j < nhall; j++)
        printf("  hallway %d: h=%lld  h*f = %lld + %lld x + %lld y ;  h*g = %lld + %lld x + %lld y\n", j,
               (long long)hyp[j], (long long)F[j][0], (long long)F[j][1], (long long)F[j][2],
               (long long)G[j][0], (long long)G[j][1], (long long)G[j][2]);
}

/* the directions of all boundary lines, their lcm L of determinants, and the table L / det */
static void setup_directions(void) {
    ndir = 0;
    dir_index(0, -1);
    dir_index(1, 0);
    dir_index(0, 1);
    dir_index(-1, 0);
    for (int j = 0; j < nhall; j++) {
        dir_f[j] = dir_index(F[j][1], F[j][2]);
        dir_fneg[j] = dir_index(-F[j][1], -F[j][2]);
        dir_g[j] = dir_index(G[j][1], G[j][2]);
        dir_gneg[j] = dir_index(-G[j][1], -G[j][2]);
    }
    L = 1;
    for (int i = 0; i < ndir; i++) {
        for (int k = 0; k < ndir; k++) {
            i64 d = to64(sub128(mul64x64(dir_A[i], dir_B[k]), mul64x64(dir_A[k], dir_B[i])));
            if (d) {
                d = d < 0 ? -d : d;
                L = to64(mul64x64(L / gcd64(L, d), d));
            }
        }
    }
    for (int i = 0; i < ndir; i++) {
        for (int k = 0; k < ndir; k++) {
            i64 d = dir_A[i] * dir_B[k] - dir_A[k] * dir_B[i]; /* checked above */
            inv_det[i][k] = 0;
            if (d) {
                if (L % d) die("lcm");
                inv_det[i][k] = L / d;
            }
        }
    }
}

/* ---------------------------------------------------------------- the certificate */

static signed char *tokens; /* -1 for a leaf, k >= 0 for a split of coordinate k */
static i64 ntokens, nleaves;

static int is_space(char c) {
    return c == ' ' || c == '\n' || c == '\r' || c == '\t';
}

static void read_cert(const char *path) {
    size_t n, i = 0;
    char *b = read_file(path, &n);
    tokens = malloc(n / 2 + 16);
    if (!tokens) die("malloc tokens");
    ntokens = 0;
    nleaves = 0;
    while (i < n) {
        while (i < n && is_space(b[i])) i++;
        if (i >= n) break;
        if (b[i] == 'L') {
            tokens[ntokens++] = -1;
            nleaves++;
            i++;
        } else if (b[i] >= '0' && b[i] <= '9') {
            int v = 0;
            while (i < n && b[i] >= '0' && b[i] <= '9') {
                v = v * 10 + (b[i] - '0');
                if (v > 1000) die("bad token");
                i++;
            }
            if (v >= 2 * nhall) die("split coordinate out of range");
            tokens[ntokens++] = (signed char)v;
        } else {
            die("bad character in certificate");
        }
        if (i < n && !is_space(b[i])) die("tokens not separated");
    }
    free(b);
}

/* checks that the tokens form a complete binary tree in preorder, and finds Dk */
static void check_structure(void) {
    static int split[MAXSTACK], in_upper[MAXSTACK]; /* the open split nodes on the current path */
    int sp = 0, depth[MAXC] = {0}, max_depth = 0;
    i64 i = 0;
    Dk = 0;
    for (;;) {
        if (i >= ntokens) die("STRUCTURE: certificate ends before the tree is complete");
        if (tokens[i] >= 0) {
            int k = tokens[i++];
            if (sp >= MAXSTACK) die("tree too deep");
            split[sp] = k;
            in_upper[sp] = 0;
            sp++;
            if (++depth[k] > Dk) Dk = depth[k];
            if (sp > max_depth) max_depth = sp;
        } else {
            i++;
            while (sp > 0 && in_upper[sp - 1]) depth[split[--sp]]--;
            if (sp == 0) break;
            in_upper[sp - 1] = 1;
        }
    }
    if (i != ntokens) die("STRUCTURE: tokens remain after the tree is complete");
    printf(
        "structure: complete binary tree, %lld tokens, %lld leaves, max depth %d, max per-coordinate depth "
        "%d\n",
        (long long)ntokens, (long long)nleaves, max_depth, Dk);
}

/* the scale M, B_W, the root box E_0 and the threshold, once Dk is known */
static void setup_scale(void) {
    i64 X[4], Y[4];
    if (Dk > 40) die("per-coordinate depth too large for this scale choice");
    M = to64(mul64x64(Wd, (i64)1 << Dk));
    MW = to64(mul64x64(Wn, (i64)1 << Dk));
    for (int j = 0; j < nhall; j++) {
        Mh[j] = to64(mul64x64(M, hyp[j]));
        MF0[j] = to64(mul64x64(M, F[j][0]));
        MG0[j] = to64(mul64x64(M, G[j][0]));
    }
    set_line(&rect_line[0], 0, -1, 0, dir_index(0, -1));
    set_line(&rect_line[1], 1, 0, MW, dir_index(1, 0));
    set_line(&rect_line[2], 0, 1, M, dir_index(0, 1));
    set_line(&rect_line[3], -1, 0, 0, dir_index(-1, 0));
    rect.n = 4; /* counterclockwise; vertex k starts the edge on line k */
    rect.v[0].X = i128_from(0);
    rect.v[0].Y = i128_from(0);
    rect.v[1].X = mul64x64(MW, L);
    rect.v[1].Y = i128_from(0);
    rect.v[2].X = mul64x64(MW, L);
    rect.v[2].Y = mul64x64(M, L);
    rect.v[3].X = i128_from(0);
    rect.v[3].Y = mul64x64(M, L);
    for (int k = 0; k < 4; k++) rect.v[k].e = k;

    X[0] = X[3] = 0; /* the corners of B_W, scaled by M */
    X[1] = X[2] = MW;
    Y[0] = Y[1] = 0;
    Y[2] = Y[3] = M;
    /* E_0 of Lemma 5.1, scaled by M h: u_1 in [min f - 1, max f] and u_2 in [min g - 1, max g] over B_W */
    for (int j = 0; j < nhall; j++) {
        for (int i = 0; i < 2; i++) {
            const i64 *fn = i ? G[j] : F[j];
            i64 lo = 0, hi = 0, lim = (i64)1 << 60;
            for (int c = 0; c < 4; c++) {
                i64 v =
                    to64(add128(add128(mul64x64(M, fn[0]), mul64x64(fn[1], X[c])), mul64x64(fn[2], Y[c])));
                if (c == 0 || v < lo) lo = v;
                if (c == 0 || v > hi) hi = v;
            }
            root_lo[2 * j + i] = to64(sub128(i128_from(lo), i128_from(Mh[j])));
            root_hi[2 * j + i] = hi;
            /* headroom: every line constant is tau + M h - M F0 with tau in [root_lo, root_hi] */
            if (hi > lim || -root_lo[2 * j + i] > lim || Mh[j] > lim || (i ? MG0[j] : MF0[j]) > lim ||
                -(i ? MG0[j] : MF0[j]) > lim)
                die("int64 headroom");
        }
    }
    {
        i128 ML = mul64x64(M, L);
        i256 ML2 = mul128x128(ML, ML);
        T_scaled = mul256x64(ML2, (u64)(2 * Tn));
        area_scale = 2.0 * to_double(ML2);
    }
    printf("scale: Dk=%d M=%lld L=%lld (%d directions)\n", Dk, (long long)M, (long long)L, ndir);
}

/* ---------------------------------------------------------------- walking the tree */

typedef struct {
    int k;      /* the split coordinate */
    int upper;  /* 0 while in the lower child, 1 in the upper child */
    i64 lo, hi; /* the interval of coordinate k at the split node */
} Frame;

/* a walk in preorder through the subtree at token `start`, keeping the box of the current node */
typedef struct {
    i64 i;  /* the current token */
    int sp; /* the depth below the start node */
    Frame stack[MAXSTACK];
    i64 lo[MAXC], hi[MAXC];
} TreeWalk;

static inline i64 midpoint(i64 a, i64 b) {
    i64 s = a + b;
    if (s & 1) die("midpoint not exact at chosen scale");
    return s / 2;
}

static void start_walk(TreeWalk *w, i64 start, const i64 *lo, const i64 *hi) {
    w->i = start;
    w->sp = 0;
    memcpy(w->lo, lo, sizeof w->lo);
    memcpy(w->hi, hi, sizeof w->hi);
}

/* from a split node to its lower child */
static void descend(TreeWalk *w) {
    Frame *f;
    if (w->sp >= MAXSTACK) die("tree too deep");
    f = &w->stack[w->sp++];
    f->k = tokens[w->i++];
    f->upper = 0;
    f->lo = w->lo[f->k];
    f->hi = w->hi[f->k];
    w->hi[f->k] = midpoint(f->lo, f->hi);
}

/* once w->i is past the subtree of the current node: to the next node of the walk; 0 at the end */
static int next_node(TreeWalk *w) {
    Frame *f;
    while (w->sp > 0 && w->stack[w->sp - 1].upper) {
        f = &w->stack[--w->sp];
        w->lo[f->k] = f->lo;
        w->hi[f->k] = f->hi;
    }
    if (w->sp == 0) return 0;
    f = &w->stack[w->sp - 1];
    f->upper = 1;
    w->lo[f->k] = midpoint(f->lo, f->hi);
    w->hi[f->k] = f->hi;
    return 1;
}

static i64 skip_subtree(i64 i) {
    i64 need = 1; /* the number of subtrees still to be passed */
    while (need > 0) need += tokens[i++] >= 0 ? 1 : -1;
    return i;
}

typedef struct {
    i64 start;              /* the token at the root of the subtree */
    i64 lo[MAXC], hi[MAXC]; /* its box */
} Task;

static Task *tasks;
static i64 ntasks, task_cap;

static void add_task(i64 start, const i64 *lo, const i64 *hi) {
    if (ntasks == task_cap) {
        Task *t;
        task_cap = task_cap ? 2 * task_cap : 4096;
        t = realloc(tasks, (size_t)task_cap * sizeof(Task));
        if (!t) die("realloc tasks");
        tasks = t;
    }
    tasks[ntasks].start = start;
    memcpy(tasks[ntasks].lo, lo, sizeof tasks[ntasks].lo);
    memcpy(tasks[ntasks].hi, hi, sizeof tasks[ntasks].hi);
    ntasks++;
}

/* cuts the tree into tasks: the nodes at depth `cut` and the leaves above that depth, in preorder */
static void make_tasks(int cut) {
    TreeWalk w;
    start_walk(&w, 0, root_lo, root_hi);
    do {
        while (tokens[w.i] >= 0 && w.sp < cut) descend(&w);
        add_task(w.i, w.lo, w.hi);
        w.i = skip_subtree(w.i);
    } while (next_node(&w));
    if (w.i != ntokens) die("task pass did not consume all tokens");
}

typedef struct {
    i64 leaves, with_components, exceeding;
    i256 worst;
    i64 first_bad; /* the token of the first leaf exceeding T, or -1 */
    double first_bad_value;
} Stats;

static void check_task(const Task *task, Work *work, Stats *s) {
    TreeWalk w;
    start_walk(&w, task->start, task->lo, task->hi);
    do {
        i256 value;
        int used_components, ok;
        while (tokens[w.i] >= 0) descend(&w);
        ok = check_leaf(work, w.lo, w.hi, &value, &used_components);
        s->leaves++;
        s->with_components += used_components;
        if (cmp256(value, s->worst) > 0) s->worst = value;
        if (!ok) {
            if (s->first_bad < 0 || w.i < s->first_bad) {
                s->first_bad = w.i;
                s->first_bad_value = to_double(value) / area_scale;
            }
            s->exceeding++;
        }
        w.i++;
    } while (next_node(&w));
}

/* a whole-number command-line argument */
static long long parse_number(const char *s) {
    char *end;
    long long v = strtoll(s, &end, 10);
    if (end == s || *end) die("bad number on the command line");
    return v;
}

int main(int argc, char **argv) {
    char cert_path[1024];
    int nthreads = 4, cut = 18, ntask_int, ti;
    clock_t c0 = clock();
    double t0 = omp_get_wtime();
    Stats total, *per_thread;
    Work **work;

    if (argc < 2 || argc > 4) {
        printf("usage: cchk spec.json [threads] [cut]\n");
        return 2;
    }
    if (argc >= 3) nthreads = (int)parse_number(argv[2]);
    if (argc >= 4) cut = (int)parse_number(argv[3]);
    if (nthreads < 1) die("the number of threads must be at least 1");
    if (cut < 0 || cut >= MAXSTACK) die("bad cut depth");
    read_spec(argv[1], cert_path);
    read_cert(cert_path);
    printf("cert %s: %lld tokens (%.1fs)\n", cert_path, (long long)ntokens, omp_get_wtime() - t0);
    check_structure();
    setup_directions();
    setup_scale();
    make_tasks(cut);
    printf("tasks: %lld (cut depth %d), setup %.1fs\n", (long long)ntasks, cut, omp_get_wtime() - t0);
    fflush(stdout);

    per_thread = calloc(nthreads, sizeof(Stats));
    work = (Work **)calloc(nthreads, sizeof(Work *));
    if (!per_thread || !work) die("malloc work");
    for (int t = 0; t < nthreads; t++) {
        work[t] = calloc(1, sizeof(Work));
        if (!work[t]) die("malloc work");
        work[t]->piece = malloc(sizeof(Piece) << nhall);
        if (!work[t]->piece) die("malloc work");
        per_thread[t].worst = zero256();
        per_thread[t].first_bad = -1;
    }
    omp_set_num_threads(nthreads);
    ntask_int = (int)ntasks;
#pragma omp parallel for schedule(dynamic, 8)
    for (ti = 0; ti < ntask_int; ti++) {
        int me = omp_get_thread_num();
        check_task(&tasks[ti], work[me], &per_thread[me]);
    }

    memset(&total, 0, sizeof total);
    total.worst = zero256();
    total.first_bad = -1;
    for (int t = 0; t < nthreads; t++) {
        const Stats *s = &per_thread[t];
        total.leaves += s->leaves;
        total.with_components += s->with_components;
        total.exceeding += s->exceeding;
        if (cmp256(s->worst, total.worst) > 0) total.worst = s->worst;
        if (s->first_bad >= 0 && (total.first_bad < 0 || s->first_bad < total.first_bad)) {
            total.first_bad = s->first_bad;
            total.first_bad_value = s->first_bad_value;
        }
    }
    printf("leaves checked %lld (tokens say %lld) ; worst certified leaf value %.10f ; leaves exceeding T: "
           "%lld ;"
           " leaves needing components: %lld ; wall %.1fs cpu %.1fs\n",
           (long long)total.leaves, (long long)nleaves, to_double(total.worst) / area_scale,
           (long long)total.exceeding, (long long)total.with_components, omp_get_wtime() - t0,
           (double)(clock() - c0) / CLOCKS_PER_SEC);
    if (total.exceeding)
        printf("first failing leaf at token %lld, value %.10f > T\n", (long long)total.first_bad,
               total.first_bad_value);
    if (total.leaves != nleaves) die("leaf count mismatch (coverage)");
    puts(total.exceeding ? "CERTIFICATE INVALID" : "CERTIFICATE VALID");
    return total.exceeding ? 1 : 0;
}
