/*
 * clauclator.c - a scientific + university-level math calculator in C
 *
 * Build:  gcc -O2 -o clauclator clauclator.c -lm
 * Run:    ./clauclator
 *
 * Expressions : + - * / % ^ ! ( ) , implicit multiplication (2x, 3(4+1))
 * Constants   : pi e phi ans      Variables: x y a=5 ...
 * Functions   : sin cos tan asin acos atan atan2 sinh cosh tanh asinh acosh atanh
 *               exp ln log log2 sqrt cbrt abs floor ceil round sign
 *               fact gamma erf pow min max mod gcd lcm ncr npr hypot deg rad
 * Unicode     : x², x³, x¹⁰, −, ×, ÷, π, √(...) are understood
 * Equations   : 3(x - 2) + 4 = 2(x + 5) - 7   (solves for x; linear exactly, others numerically)
 * Commands    :
 *   diff  EXPR @ X0            derivative at a point (variable x)
 *   int   EXPR from A to B     definite integral (variable x), adaptive Simpson
 *   root  EXPR near G          solve EXPR = 0 (Newton + bisection fallback)
 *   limit EXPR @ X0            numerical limit as x -> X0 (variable x)
 *   sum   EXPR from A to B     summation (variable k)
 *   prod  EXPR from A to B     product   (variable k)
 *   taylor EXPR @ X0 order N   Taylor coefficients about X0
 *   factor N                   prime factorisation
 *   isprime N
 *   det N / solve N            determinant / linear system (matrix read from input)
 *   help, quit
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <ctype.h>
#include <stdint.h>

#define MAXV 128
static struct { char name[32]; double v; } vars[MAXV];
static int nvars = 0;
static const char *p;
static int err = 0;
static char errmsg[160];

static void fail(const char *m) { if (!err) { err = 1; snprintf(errmsg, sizeof errmsg, "%s", m); } }

static void setvar(const char *n, double v) {
    for (int i = 0; i < nvars; i++) if (!strcmp(vars[i].name, n)) { vars[i].v = v; return; }
    if (nvars < MAXV) { snprintf(vars[nvars].name, 32, "%s", n); vars[nvars++].v = v; }
}
static int getvar(const char *n, double *out) {
    for (int i = 0; i < nvars; i++) if (!strcmp(vars[i].name, n)) { *out = vars[i].v; return 1; }
    return 0;
}

static void skip(void) { while (*p == ' ' || *p == '\t') p++; }
static double parse_expr(void);

static double gcd_d(double a, double b) {
    a = fabs(floor(a)); b = fabs(floor(b));
    while (b > 0) { double t = fmod(a, b); a = b; b = t; }
    return a;
}
static double fact_d(double n) {
    if (n < 0) { fail("factorial of negative"); return NAN; }
    if (n == floor(n) && n <= 20) { double r = 1; for (int i = 2; i <= (int)n; i++) r *= i; return r; }
    return tgamma(n + 1);
}
static double ncr_d(double n, double k) {
    if (k < 0 || k > n) return 0;
    if (k > n - k) k = n - k;
    double r = 1;
    for (int i = 1; i <= (int)k; i++) r = r * (n - k + i) / i;
    return round(r);
}

static double call_fn(const char *f, double *a, int n) {
#define F1(name, expr) if (!strcmp(f, name)) { if (n != 1) { fail(name " needs 1 argument"); return NAN; } double x = a[0]; return (expr); }
#define F2(name, expr) if (!strcmp(f, name)) { if (n != 2) { fail(name " needs 2 arguments"); return NAN; } double x = a[0], y = a[1]; return (expr); }
    F1("sin", sin(x)) F1("cos", cos(x)) F1("tan", tan(x))
    F1("asin", asin(x)) F1("acos", acos(x)) F1("atan", atan(x))
    F1("sinh", sinh(x)) F1("cosh", cosh(x)) F1("tanh", tanh(x))
    F1("asinh", asinh(x)) F1("acosh", acosh(x)) F1("atanh", atanh(x))
    F1("exp", exp(x)) F1("ln", log(x)) F1("log", log10(x)) F1("log2", log2(x))
    F1("sqrt", sqrt(x)) F1("cbrt", cbrt(x)) F1("abs", fabs(x))
    F1("floor", floor(x)) F1("ceil", ceil(x)) F1("round", round(x))
    F1("sign", (x > 0) - (x < 0)) F1("fact", fact_d(x)) F1("gamma", tgamma(x))
    F1("erf", erf(x)) F1("deg", x * 180.0 / M_PI) F1("rad", x * M_PI / 180.0)
    F2("atan2", atan2(x, y)) F2("pow", pow(x, y)) F2("min", fmin(x, y)) F2("max", fmax(x, y))
    F2("mod", fmod(x, y)) F2("gcd", gcd_d(x, y)) F2("hypot", hypot(x, y))
    F2("lcm", (x == 0 || y == 0) ? 0 : fabs(floor(x) * floor(y)) / gcd_d(x, y))
    F2("ncr", ncr_d(x, y)) F2("npr", ncr_d(x, y) * fact_d(y))
    char m[64]; snprintf(m, sizeof m, "unknown function '%s'", f); fail(m);
    return NAN;
}

static double parse_atom(void) {
    skip();
    if (*p == '(') {
        p++; double v = parse_expr(); skip();
        if (*p != ')') fail("missing ')'"); else p++;
        return v;
    }
    if (isdigit((unsigned char)*p) || *p == '.') {
        char *end; double v = strtod(p, &end); p = end; return v;
    }
    if (isalpha((unsigned char)*p) || *p == '_') {
        char id[32]; int i = 0;
        while ((isalnum((unsigned char)*p) || *p == '_') && i < 31) id[i++] = *p++;
        id[i] = 0; skip();
        if (*p == '(') {
            p++; double args[4]; int n = 0;
            skip();
            if (*p != ')') {
                do { if (n < 4) args[n++] = parse_expr(); skip(); } while (*p == ',' && (p++, 1));
            }
            if (*p != ')') { fail("missing ')' in call"); return NAN; }
            p++;
            return call_fn(id, args, n);
        }
        double v;
        if (getvar(id, &v)) return v;
        if (!strcmp(id, "pi")) return M_PI;
        if (!strcmp(id, "e")) return M_E;
        if (!strcmp(id, "phi")) return (1 + sqrt(5.0)) / 2;
        char m[64]; snprintf(m, sizeof m, "unknown name '%s'", id); fail(m);
        return NAN;
    }
    fail("unexpected input");
    return NAN;
}

static double parse_unary(void);
static double parse_power(void) {
    double b = parse_atom();
    for (;;) { skip(); if (*p == '!' && p[1] != '=') { p++; b = fact_d(b); } else break; }
    skip();
    if (*p == '^') { p++; double e = parse_unary(); return pow(b, e); }
    return b;
}
static double parse_unary(void) {
    skip();
    if (*p == '-') { p++; return -parse_unary(); }
    if (*p == '+') { p++; return parse_unary(); }
    return parse_power();
}
static double parse_term(void) {
    double v = parse_unary();
    for (;;) {
        skip();
        if (*p == '*') { p++; v *= parse_unary(); }
        else if (*p == '/') { p++; double d = parse_unary(); if (d == 0) { fail("division by zero"); return NAN; } v /= d; }
        else if (*p == '%') { p++; v = fmod(v, parse_unary()); }
        else if (*p == '(' || isalpha((unsigned char)*p)) v *= parse_power();   /* implicit multiply */
        else break;
        if (err) return NAN;
    }
    return v;
}
static double parse_expr(void) {
    double v = parse_term();
    for (;;) {
        skip();
        if (*p == '+') { p++; v += parse_term(); }
        else if (*p == '-') { p++; v -= parse_term(); }
        else break;
        if (err) return NAN;
    }
    return v;
}

static double eval_str(const char *s) {
    const char *save = p; p = s; err = 0;
    double v = parse_expr(); skip();
    if (!err && *p) fail("trailing characters");
    p = save;
    return v;
}

/* ---------- calculus helpers ---------- */
static char gexpr[512];
static double fx(double x) { setvar("x", x); return eval_str(gexpr); }

static double asr(double a, double b, double fa, double fm, double fb, double whole, double eps, int d) {
    double m = (a + b) / 2, lm = (a + m) / 2, rm = (m + b) / 2;
    double flm = fx(lm), frm = fx(rm);
    double l = (m - a) / 6 * (fa + 4 * flm + fm), r = (b - m) / 6 * (fm + 4 * frm + fb);
    if (d <= 0 || fabs(l + r - whole) <= 15 * eps) return l + r + (l + r - whole) / 15;
    return asr(a, m, fa, flm, fm, l, eps / 2, d - 1) + asr(m, b, fm, frm, fb, r, eps / 2, d - 1);
}
static double integrate(double a, double b) {
    double fa = fx(a), fb = fx(b), fm = fx((a + b) / 2);
    double whole = (b - a) / 6 * (fa + 4 * fm + fb);
    return asr(a, b, fa, fm, fb, whole, 1e-10, 40);
}
static double deriv(double x0, int order) {
    double h = 1e-3 * fmax(1.0, fabs(x0));
    if (order == 1) return (-fx(x0 + 2*h) + 8*fx(x0 + h) - 8*fx(x0 - h) + fx(x0 - 2*h)) / (12*h);
    h = 1e-2 * fmax(1.0, fabs(x0));
    if (order == 2) return (-fx(x0+2*h) + 16*fx(x0+h) - 30*fx(x0) + 16*fx(x0-h) - fx(x0-2*h)) / (12*h*h);
    return NAN;
}
static double rich_deriv(double x0) {   /* Richardson-improved first derivative */
    double h = 1e-2 * fmax(1.0, fabs(x0)), D[6][6];
    for (int i = 0; i < 6; i++) {
        D[i][0] = (fx(x0 + h) - fx(x0 - h)) / (2 * h);
        double f = 4;
        for (int j = 1; j <= i; j++, f *= 4) D[i][j] = D[i][j-1] + (D[i][j-1] - D[i-1][j-1]) / (f - 1);
        h /= 2;
    }
    return D[5][5];
}
static int find_root(double g, double *out) {
    double x = g;
    for (int i = 0; i < 200; i++) {
        double f = fx(x); if (err) return 0;
        if (fabs(f) < 1e-14) { *out = x; return 1; }
        double d = rich_deriv(x);
        if (d == 0 || isnan(d)) break;
        double nx = x - f / d;
        if (fabs(nx - x) < 1e-13 * fmax(1.0, fabs(x))) { *out = nx; return 1; }
        x = nx;
    }
    /* bisection fallback: expand a bracket around the guess */
    for (double w = 0.5; w < 1e6; w *= 2) {
        double a = g - w, b = g + w, fa = fx(a), fb = fx(b);
        if (fa * fb <= 0) {
            for (int i = 0; i < 200; i++) {
                double m = (a + b) / 2, fm = fx(m);
                if (fa * fm <= 0) { b = m; fb = fm; } else { a = m; fa = fm; }
            }
            *out = (a + b) / 2; return 1;
        }
    }
    return 0;
}

/* ---------- number theory & linear algebra ---------- */
static void factor(uint64_t n) {
    if (n < 2) { printf("%llu has no prime factorisation\n", (unsigned long long)n); return; }
    printf("%llu =", (unsigned long long)n);
    int first = 1;
    for (uint64_t d = 2; d * d <= n; d += (d == 2 ? 1 : 2)) {
        int c = 0; while (n % d == 0) { n /= d; c++; }
        if (c) { printf("%s %llu", first ? "" : " *", (unsigned long long)d); if (c > 1) printf("^%d", c); first = 0; }
    }
    if (n > 1) printf("%s %llu", first ? "" : " *", (unsigned long long)n);
    printf("\n");
}
static int isprime(uint64_t n) {
    if (n < 2) return 0;
    for (uint64_t d = 2; d * d <= n; d++) if (n % d == 0) return 0;
    return 1;
}
static double M[20][21];
static int read_matrix(int n, int cols) {
    printf("Enter %d rows of %d numbers:\n", n, cols);
    for (int i = 0; i < n; i++) for (int j = 0; j < cols; j++)
        if (scanf("%lf", &M[i][j]) != 1) return 0;
    return 1;
}
static double gauss(int n, int cols, int *singular) {
    double det = 1; *singular = 0;
    for (int c = 0; c < n; c++) {
        int pv = c;
        for (int r = c + 1; r < n; r++) if (fabs(M[r][c]) > fabs(M[pv][c])) pv = r;
        if (fabs(M[pv][c]) < 1e-12) { *singular = 1; return 0; }
        if (pv != c) { for (int j = 0; j < cols; j++) { double t = M[c][j]; M[c][j] = M[pv][j]; M[pv][j] = t; } det = -det; }
        det *= M[c][c];
        for (int r = 0; r < n; r++) if (r != c) {
            double f = M[r][c] / M[c][c];
            for (int j = c; j < cols; j++) M[r][j] -= f * M[c][j];
        }
    }
    return det;
}

/* ---------- command plumbing ---------- */
static char *find_kw(char *s, const char *kw) {
    char pat[32]; snprintf(pat, sizeof pat, " %s ", kw);
    return strstr(s, pat);
}
static void pr(double v) {
    if (isnan(v)) printf("= undefined\n");
    else if (isinf(v)) printf("= %s\n", v > 0 ? "infinity" : "-infinity");
    else { printf("= %.12g\n", v); setvar("ans", v); }
}
static int ok(void) { if (err) { printf("error: %s\n", errmsg); err = 0; return 0; } return 1; }

static void help(void) {
    puts("Expressions: 2+3*4  sin(pi/2)  2^10  5!  ncr(10,3)  gcd(48,18)  3x+1  a=5");
    puts("Commands:");
    puts("  diff EXPR @ X0          e.g. diff x^3 + sin(x) @ 2");
    puts("  int EXPR from A to B    e.g. int exp(-x^2) from -10 to 10");
    puts("  root EXPR near G        e.g. root x^3 - 2x - 5 near 2");
    puts("  limit EXPR @ X0         e.g. limit sin(x)/x @ 0");
    puts("  sum EXPR from A to B    uses k, e.g. sum 1/k^2 from 1 to 100000");
    puts("  prod EXPR from A to B   uses k");
    puts("  taylor EXPR @ X0 order N");
    puts("  factor N | isprime N | det N | solve N | help | quit");
}

static void normalize(char *s) {
    char out[2048], *w = out, *orig = s;           /* rewrite into a separate buffer: output can be longer than input */
    int sup = 0;                                   /* inside a run of superscript digits */
    while (*s) {
        unsigned char c = (unsigned char)s[0], c1 = (unsigned char)s[1], c2 = c1 ? (unsigned char)s[2] : 0;
        int d = -1, len = 0;
        if (c == 0xC2 && c1 == 0xB2) { d = 2; len = 2; }
        else if (c == 0xC2 && c1 == 0xB3) { d = 3; len = 2; }
        else if (c == 0xC2 && c1 == 0xB9) { d = 1; len = 2; }
        else if (c == 0xE2 && c1 == 0x81 && c2 == 0xB0) { d = 0; len = 3; }
        else if (c == 0xE2 && c1 == 0x81 && c2 >= 0xB4 && c2 <= 0xB9) { d = 4 + (c2 - 0xB4); len = 3; }
        else if (c == 0xE2 && c1 == 0x81 && c2 == 0xBB) { d = 10; len = 3; }          /* superscript minus */
        if (d >= 0) {
            if (!sup) *w++ = '^';
            *w++ = d == 10 ? '-' : (char)('0' + d);
            sup = 1; s += len; continue;
        }
        sup = 0;
        if (c == 0xE2 && c1 == 0x88 && c2 == 0x9A) { *w++='s'; *w++='q'; *w++='r'; *w++='t'; s += 3; continue; } /* sqrt sign */
        if (c == 0xE2 && c1 == 0x88 && c2 == 0x92) { *w++ = '-'; s += 3; }          /* U+2212 minus */
        else if (c == 0xE2 && c1 == 0x80 && (c2 == 0x93 || c2 == 0x94)) { *w++ = '-'; s += 3; } /* en/em dash */
        else if (c == 0xC3 && c1 == 0x97) { *w++ = '*'; s += 2; }                    /* x */
        else if (c == 0xC3 && c1 == 0xB7) { *w++ = '/'; s += 2; }                    /* division sign */
        else if (c == 0xCF && c1 == 0x80) { *w++ = 'p'; *w++ = 'i'; s += 2; }        /* pi */
        else *w++ = *s++;
    }
    *w = 0;
    out[511] = 0;                                  /* callers' buffers hold 512 bytes */
    strcpy(orig, out);
}

static void run(char *line) {
    normalize(line);
    char *s = line;
    while (isspace((unsigned char)*s)) s++;
    size_t L = strlen(s); while (L && isspace((unsigned char)s[L-1])) s[--L] = 0;
    if (!*s) return;
    if (!strcmp(s, "quit") || !strcmp(s, "exit") || !strcmp(s, "q")) exit(0);
    if (!strcmp(s, "help")) { help(); return; }

    if (!strncmp(s, "diff ", 5)) {
        char *at = find_kw(s + 4, "@"); if (!at) { puts("usage: diff EXPR @ X0"); return; }
        *at = 0; snprintf(gexpr, sizeof gexpr, "%s", s + 5);
        double x0 = eval_str(at + 3); if (!ok()) return;
        double v = rich_deriv(x0); if (!ok()) return;
        printf("f'(%g) ", x0); pr(v);
        double v2 = deriv(x0, 2); if (ok()) printf("f''(%g) = %.8g\n", x0, v2);
        return;
    }
    if (!strncmp(s, "int ", 4) || !strncmp(s, "sum ", 4) || !strncmp(s, "prod ", 5)) {
        int kind = s[0] == 'i' ? 0 : (s[1] == 'u' ? 1 : 2);
        char *body = s + (kind == 2 ? 5 : 4);
        char *fr = find_kw(body, "from"), *to = fr ? find_kw(fr + 1, "to") : NULL;
        if (!fr || !to) { puts("usage: int|sum|prod EXPR from A to B"); return; }
        *fr = 0; *to = 0;
        snprintf(gexpr, sizeof gexpr, "%s", body);
        double a = eval_str(fr + 6); if (!ok()) return;
        double b = eval_str(to + 4); if (!ok()) return;
        if (kind == 0) {
            double v = integrate(a, b); if (!ok()) return; pr(v);
        } else {
            double acc = kind == 1 ? 0 : 1;
            if (b - a > 5e7) { puts("range too large"); return; }
            for (double k = a; k <= b; k++) {
                setvar("k", k); double t = eval_str(gexpr); if (!ok()) return;
                if (kind == 1) acc += t; else acc *= t;
            }
            pr(acc);
        }
        return;
    }
    if (!strncmp(s, "root ", 5)) {
        char *nr = find_kw(s + 4, "near"); double g = 0;
        if (nr) { *nr = 0; snprintf(gexpr, sizeof gexpr, "%s", s + 5); g = eval_str(nr + 6); if (!ok()) return; }
        else snprintf(gexpr, sizeof gexpr, "%s", s + 5);
        double r; if (find_root(g, &r)) { printf("x "); pr(r); } else if (ok()) puts("no root found near that guess");
        return;
    }
    if (!strncmp(s, "limit ", 6)) {
        char *at = find_kw(s + 5, "@"); if (!at) { puts("usage: limit EXPR @ X0"); return; }
        *at = 0; snprintf(gexpr, sizeof gexpr, "%s", s + 6);
        double x0 = eval_str(at + 3); if (!ok()) return;
        double hs[] = {1e-4, 1e-6, 1e-8}, lo = 0, hi = 0;
        for (int i = 0; i < 3; i++) { lo = fx(x0 - hs[i]); hi = fx(x0 + hs[i]); }
        if (!ok()) return;
        if (fabs(lo - hi) <= 1e-5 * fmax(1.0, fabs(lo))) { printf("limit "); pr((lo + hi) / 2); }
        else printf("left limit ~ %.8g, right limit ~ %.8g (two-sided limit does not exist)\n", lo, hi);
        return;
    }
    if (!strncmp(s, "taylor ", 7)) {
        char *at = find_kw(s + 6, "@"), *od = at ? find_kw(at + 1, "order") : NULL;
        if (!at || !od) { puts("usage: taylor EXPR @ X0 order N"); return; }
        *at = 0; *od = 0; snprintf(gexpr, sizeof gexpr, "%s", s + 7);
        double x0 = eval_str(at + 3); if (!ok()) return;
        int N = (int)eval_str(od + 7); if (!ok()) return;
        if (N > 8) N = 8;
        /* coefficients via Cauchy integral on a circle is complex-valued; use finite differences instead */
        double h = 0.05, c[10];
        for (int n = 0; n <= N; n++) {
            double sum = 0;
            for (int k = 0; k <= n; k++)
                sum += ((n - k) % 2 ? -1 : 1) * ncr_d(n, k) * fx(x0 + (k - n / 2.0) * h);
            c[n] = sum / pow(h, n);
            double nf = 1; for (int i = 2; i <= n; i++) nf *= i;
            c[n] /= nf;
        }
        if (!ok()) return;
        printf("f(x) ~ ");
        for (int n = 0; n <= N; n++) printf("%s%.6g(x-%g)^%d", n ? " + " : "", c[n], x0, n);
        printf("   (numerical estimate)\n");
        return;
    }
    if (!strncmp(s, "factor ", 7)) { double v = eval_str(s + 7); if (ok()) factor((uint64_t)v); return; }
    if (!strncmp(s, "isprime ", 8)) { double v = eval_str(s + 8); if (ok()) printf("%s\n", isprime((uint64_t)v) ? "prime" : "not prime"); return; }
    if (!strncmp(s, "det ", 4) || !strncmp(s, "solve ", 6)) {
        int solve = s[0] == 's';
        int n = (int)eval_str(s + (solve ? 6 : 4)); if (!ok()) return;
        if (n < 1 || n > 20) { puts("size must be 1..20"); return; }
        int cols = solve ? n + 1 : n;
        if (!read_matrix(n, cols)) { puts("bad matrix input"); return; }
        int sing; double d = gauss(n, cols, &sing);
        if (solve) {
            if (sing) puts("system is singular (no unique solution)");
            else for (int i = 0; i < n; i++) printf("x%d = %.10g\n", i + 1, M[i][n] / M[i][i]);
        } else { printf("det "); pr(sing ? 0 : d); }
        return;
    }
    /* assignment: name = expr */
    {
        const char *q = s; char nm[32]; int i = 0;
        while ((isalnum((unsigned char)*q) || *q == '_') && i < 31) nm[i++] = *q++;
        nm[i] = 0;
        while (*q == ' ') q++;
        if (i && isalpha((unsigned char)nm[0]) && *q == '=' && q[1] != '=') {
            double v = eval_str(q + 1); if (ok()) { setvar(nm, v); printf("%s = %.12g\n", nm, v); }
            return;
        }
    }
    /* equation: LHS = RHS  -> solve for x */
    {
        char *eq = strchr(s, '=');
        if (eq && eq[1] != '=') {
            *eq = 0;
            snprintf(gexpr, sizeof gexpr, "(%s)-(%s)", s, eq + 1);
            double f0 = fx(0), f1 = fx(1), f2 = fx(2);
            if (!ok()) return;
            double a = f1 - f0;
            if (fabs((f2 - f1) - a) < 1e-9 * fmax(1.0, fabs(a))) {      /* linear in x: exact */
                if (fabs(a) < 1e-12) puts(fabs(f0) < 1e-12 ? "identity: true for every x" : "no solution");
                else { printf("x "); pr(-f0 / a); }
            } else {                                                    /* nonlinear: search for several roots */
                double found[16]; int nf = 0;
                for (double g = -50; g <= 50; g += 0.5) {
                    double r; if (!find_root(g, &r)) { err = 0; continue; }
                    int dup = 0; for (int i = 0; i < nf; i++) if (fabs(found[i] - r) < 1e-6) dup = 1;
                    if (!dup && fabs(fx(r)) < 1e-7 && nf < 16) found[nf++] = r;
                }
                err = 0;
                if (!nf) puts("no real solution found for x in [-50, 50]");
                for (int i = 0; i < nf; i++) printf("x = %.12g\n", found[i]);
            }
            return;
        }
    }
    double v = eval_str(s);
    if (ok()) pr(v);
}

int main(int argc, char **argv) {
    setvar("ans", 0); setvar("x", 0);
    if (argc > 1) {             /* one-shot: ./clauclator "int x^2 from 0 to 3" */
        char buf[512] = ""; for (int i = 1; i < argc; i++) { strncat(buf, argv[i], sizeof buf - strlen(buf) - 2); strcat(buf, " "); }
        run(buf); return 0;
    }
    puts("Clauclator - type 'help' for commands, 'quit' to exit");
    char line[512];
    for (;;) {
        printf("> "); fflush(stdout);
        if (!fgets(line, sizeof line, stdin)) break;
        run(line);
    }
    return 0;
}
