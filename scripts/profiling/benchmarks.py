"""Benchmark generation for CBMC profiling."""

import shutil
import subprocess
import textwrap
from pathlib import Path

from .utils import die, info, ok, warn


def generate_auto_benchmarks(output_dir):
    """Generate 3 quick built-in benchmarks exercising different CBMC stages."""
    benchmarks = []
    bench_dir = output_dir / "benchmarks"
    bench_dir.mkdir(parents=True, exist_ok=True)

    (bench_dir / "linked_list.c").write_text(textwrap.dedent("""\
        #include <assert.h>
        #include <stdlib.h>
        struct node { int data; struct node *next; };
        struct node *build(int n) {
          struct node *head = NULL;
          for(int i = 0; i < n; i++) {
            struct node *p = malloc(sizeof(struct node));
            if(!p) return head;
            p->data = i; p->next = head; head = p;
          }
          return head;
        }
        int sum(struct node *h) {
          int s = 0;
          while(h) { s += h->data; h = h->next; }
          return s;
        }
        int main() {
          struct node *l = build(5);
          int s = sum(l);
          assert(s >= 0);
          return 0;
        }
    """))
    benchmarks.append({
        "name": "linked_list",
        "file": str(bench_dir / "linked_list.c"),
        "args": ["--bounds-check", "--pointer-check", "--unwind", "200"],
    })

    (bench_dir / "array_ops.c").write_text(textwrap.dedent("""\
        #include <assert.h>
        #include <string.h>
        #define N 50
        void sort(int a[], int n) {
          for(int i = 0; i < n-1; i++)
            for(int j = 0; j < n-i-1; j++)
              if(a[j] > a[j+1]) { int t = a[j]; a[j] = a[j+1]; a[j+1] = t; }
        }
        int main() {
          int a[N];
          sort(a, N);
          for(int i = 0; i < N-1; i++)
            assert(a[i] <= a[i+1]);
          return 0;
        }
    """))
    benchmarks.append({
        "name": "array_ops",
        "file": str(bench_dir / "array_ops.c"),
        "args": ["--bounds-check", "--unwind", "55"],
    })

    (bench_dir / "structs.c").write_text(textwrap.dedent("""\
        #include <assert.h>
        #include <stdlib.h>
        #include <string.h>
        struct inner { int x; int y; };
        struct middle { struct inner a; struct inner b; int tag; };
        struct outer { struct middle m[3]; int count; };
        void init(struct outer *o) {
          o->count = 3;
          for(int i = 0; i < 3; i++) {
            o->m[i].a.x = i; o->m[i].a.y = i*2;
            o->m[i].b.x = i+10; o->m[i].b.y = i*3;
            o->m[i].tag = i;
          }
        }
        int total(struct outer *o) {
          int s = 0;
          for(int i = 0; i < o->count; i++)
            s += o->m[i].a.x + o->m[i].a.y + o->m[i].b.x + o->m[i].b.y;
          return s;
        }
        int main() {
          struct outer o;
          init(&o);
          struct outer o2;
          memcpy(&o2, &o, sizeof(o));
          assert(total(&o) == total(&o2));
          return 0;
        }
    """))
    benchmarks.append({
        "name": "structs",
        "file": str(bench_dir / "structs.c"),
        "args": ["--bounds-check", "--pointer-check", "--unwind", "10"],
    })

    ok(f"Generated {len(benchmarks)} auto-benchmarks in {bench_dir}")
    return benchmarks


def generate_auto_large_benchmarks(output_dir):
    """Generate extended benchmark suite (10 tests)."""
    benchmarks = generate_auto_benchmarks(output_dir)
    bench_dir = output_dir / "benchmarks"

    (bench_dir / "dlinked_list.c").write_text(textwrap.dedent("""\
        #include <assert.h>
        #include <stdlib.h>
        struct dnode { int data; struct dnode *next; struct dnode *prev; };
        struct dnode *build(int n) {
          struct dnode *head = NULL;
          for(int i = 0; i < n; i++) {
            struct dnode *p = malloc(sizeof(struct dnode));
            if(!p) return head;
            p->data = i; p->next = head; p->prev = NULL;
            if(head) head->prev = p;
            head = p;
          }
          return head;
        }
        int forward_sum(struct dnode *h) {
          int s = 0;
          while(h) { s += h->data; h = h->next; }
          return s;
        }
        struct dnode *tail(struct dnode *h) {
          if(!h) return NULL;
          while(h->next) h = h->next;
          return h;
        }
        int backward_sum(struct dnode *t) {
          int s = 0;
          while(t) { s += t->data; t = t->prev; }
          return s;
        }
        int main() {
          struct dnode *l = build(4);
          struct dnode *t = tail(l);
          assert(forward_sum(l) == backward_sum(t));
          return 0;
        }
    """))
    benchmarks.append({
        "name": "dlinked_list",
        "file": str(bench_dir / "dlinked_list.c"),
        "args": ["--bounds-check", "--pointer-check", "--unwind", "150"],
    })

    (bench_dir / "string_ops.c").write_text(textwrap.dedent("""\
        #include <assert.h>
        #include <string.h>
        #include <stdlib.h>
        char *my_strdup(const char *s) {
          size_t len = strlen(s) + 1;
          char *d = malloc(len);
          if(d) memcpy(d, s, len);
          return d;
        }
        int my_strcmp(const char *a, const char *b) {
          while(*a && *a == *b) { a++; b++; }
          return *a - *b;
        }
        void my_strrev(char *s) {
          size_t len = strlen(s);
          for(size_t i = 0; i < len/2; i++) {
            char t = s[i]; s[i] = s[len-1-i]; s[len-1-i] = t;
          }
        }
        int main() {
          char buf[20];
          buf[0] = 'h'; buf[1] = 'e'; buf[2] = 'l';
          buf[3] = 'l'; buf[4] = 'o'; buf[5] = 0;
          char *copy = my_strdup(buf);
          if(copy) {
            assert(my_strcmp(buf, copy) == 0);
            my_strrev(copy);
            assert(my_strcmp(copy, "olleh") == 0);
            free(copy);
          }
          return 0;
        }
    """))
    benchmarks.append({
        "name": "string_ops",
        "file": str(bench_dir / "string_ops.c"),
        "args": ["--bounds-check", "--pointer-check", "--unwind", "25"],
    })

    (bench_dir / "func_ptrs.c").write_text(textwrap.dedent("""\
        #include <assert.h>
        typedef int (*binop_t)(int, int);
        int add(int a, int b) { return a + b; }
        int sub(int a, int b) { return a - b; }
        int mul(int a, int b) { return a * b; }
        int apply(binop_t f, int x, int y) { return f(x, y); }
        int fold(binop_t f, int arr[], int n) {
          int acc = arr[0];
          for(int i = 1; i < n; i++) acc = f(acc, arr[i]);
          return acc;
        }
        int main() {
          int a[] = {1, 2, 3, 4, 5, 6, 7, 8};
          assert(fold(add, a, 8) == 36);
          assert(apply(sub, 10, 3) == 7);
          assert(apply(mul, 4, 5) == 20);
          binop_t ops[] = {add, sub, mul};
          for(int i = 0; i < 3; i++)
            assert(apply(ops[i], 6, 3) >= 3);
          return 0;
        }
    """))
    benchmarks.append({
        "name": "func_ptrs",
        "file": str(bench_dir / "func_ptrs.c"),
        "args": ["--bounds-check", "--pointer-check", "--unwind", "15"],
    })

    (bench_dir / "bitvector.c").write_text(textwrap.dedent("""\
        #include <assert.h>
        #include <limits.h>
        unsigned popcount(unsigned x) {
          unsigned c = 0;
          while(x) { c += x & 1; x >>= 1; }
          return c;
        }
        unsigned reverse_bits(unsigned x) {
          unsigned r = 0;
          for(int i = 0; i < sizeof(unsigned)*CHAR_BIT; i++) {
            r = (r << 1) | (x & 1); x >>= 1;
          }
          return r;
        }
        unsigned next_pow2(unsigned x) {
          x--; x |= x >> 1; x |= x >> 2; x |= x >> 4;
          x |= x >> 8; x |= x >> 16; x++;
          return x;
        }
        int main() {
          assert(popcount(0) == 0);
          assert(popcount(0xFF) == 8);
          assert(popcount(0x80000000u) == 1);
          assert(reverse_bits(reverse_bits(0x12345678u)) == 0x12345678u);
          assert(next_pow2(1) == 1);
          assert(next_pow2(5) == 8);
          assert(next_pow2(1023) == 1024);
          return 0;
        }
    """))
    benchmarks.append({
        "name": "bitvector",
        "file": str(bench_dir / "bitvector.c"),
        "args": ["--bounds-check", "--unwind", "40"],
    })

    (bench_dir / "matrix.c").write_text(textwrap.dedent("""\
        #include <assert.h>
        #define SZ 8
        void matmul(int C[SZ][SZ], int A[SZ][SZ], int B[SZ][SZ]) {
          for(int i = 0; i < SZ; i++)
            for(int j = 0; j < SZ; j++) {
              C[i][j] = 0;
              for(int k = 0; k < SZ; k++)
                C[i][j] += A[i][k] * B[k][j];
            }
        }
        void identity(int M[SZ][SZ]) {
          for(int i = 0; i < SZ; i++)
            for(int j = 0; j < SZ; j++)
              M[i][j] = (i == j) ? 1 : 0;
        }
        int main() {
          int A[SZ][SZ], I[SZ][SZ], R[SZ][SZ];
          identity(I);
          for(int i = 0; i < SZ; i++)
            for(int j = 0; j < SZ; j++)
              A[i][j] = i * SZ + j;
          matmul(R, A, I);
          for(int i = 0; i < SZ; i++)
            for(int j = 0; j < SZ; j++)
              assert(R[i][j] == A[i][j]);
          return 0;
        }
    """))
    benchmarks.append({
        "name": "matrix",
        "file": str(bench_dir / "matrix.c"),
        "args": ["--bounds-check", "--unwind", "12"],
    })

    (bench_dir / "unions.c").write_text(textwrap.dedent("""\
        #include <assert.h>
        #include <string.h>
        union val { int i; float f; unsigned char bytes[4]; };
        struct tagged { int tag; union val v; };
        unsigned char checksum(unsigned char *p, int n) {
          unsigned char s = 0;
          for(int i = 0; i < n; i++) s ^= p[i];
          return s;
        }
        int main() {
          struct tagged arr[5];
          for(int i = 0; i < 5; i++) {
            arr[i].tag = i % 2;
            if(arr[i].tag == 0) arr[i].v.i = i * 100;
            else { arr[i].v.f = 0; memset(&arr[i].v, i, 4); }
          }
          for(int i = 0; i < 5; i++) {
            unsigned char cs = checksum(arr[i].v.bytes, 4);
            assert(cs == cs);
          }
          return 0;
        }
    """))
    benchmarks.append({
        "name": "unions",
        "file": str(bench_dir / "unions.c"),
        "args": ["--bounds-check", "--pointer-check", "--unwind", "10"],
    })

    (bench_dir / "tree.c").write_text(textwrap.dedent("""\
        #include <assert.h>
        #include <stdlib.h>
        struct tree { int val; struct tree *left; struct tree *right; };
        struct tree *make(int depth, int val) {
          if(depth <= 0) return NULL;
          struct tree *t = malloc(sizeof(struct tree));
          if(!t) return NULL;
          t->val = val;
          t->left = make(depth - 1, val * 2);
          t->right = make(depth - 1, val * 2 + 1);
          return t;
        }
        int tree_sum(struct tree *t) {
          if(!t) return 0;
          return t->val + tree_sum(t->left) + tree_sum(t->right);
        }
        int tree_depth(struct tree *t) {
          if(!t) return 0;
          int ld = tree_depth(t->left);
          int rd = tree_depth(t->right);
          return 1 + (ld > rd ? ld : rd);
        }
        int main() {
          struct tree *t = make(4, 1);
          assert(tree_depth(t) <= 4);
          assert(tree_sum(t) >= 0);
          return 0;
        }
    """))
    benchmarks.append({
        "name": "tree",
        "file": str(bench_dir / "tree.c"),
        "args": ["--bounds-check", "--pointer-check", "--unwind", "8"],
    })

    ok(f"Generated {len(benchmarks)} auto-large benchmarks in {bench_dir}")
    return benchmarks


# Fixed CSmith seeds producing programs that exercise different CBMC features:
# 1234567890: medium complexity, several loops and conditionals
# 42:         simpler control flow, good baseline
# 1111111111: array-heavy operations
# 2718281828: multiple function calls and returns
# 314159265:  nested struct access patterns
CSMITH_SEEDS = [1234567890, 42, 1111111111, 2718281828, 314159265]


def generate_csmith_benchmarks(output_dir):
    """Generate benchmarks using CSmith with fixed seeds for reproducibility."""
    if not shutil.which("csmith"):
        die("csmith not found. Install with: apt-get install csmith")
    csmith_inc = None
    for d in ["/usr/include/csmith", "/usr/local/include/csmith"]:
        if Path(d).is_dir():
            csmith_inc = d
            break
    if not csmith_inc:
        die("CSmith headers not found")

    benchmarks = []
    bench_dir = output_dir / "benchmarks"
    bench_dir.mkdir(parents=True, exist_ok=True)

    for seed in CSMITH_SEEDS:
        name = f"csmith_{seed}"
        src = bench_dir / f"{name}.c"
        info(f"Generating CSmith test with seed {seed}...")
        try:
            result = subprocess.run(
                ["csmith", "--seed", str(seed)],
                capture_output=True, text=True, timeout=30)
        except subprocess.TimeoutExpired:
            warn(f"CSmith timed out for seed {seed}, skipping")
            continue
        if result.returncode != 0:
            warn(f"CSmith failed for seed {seed}, skipping")
            continue
        src.write_text(result.stdout)
        benchmarks.append({
            "name": name,
            "file": str(src),
            "args": [f"-I{csmith_inc}", "--unwind", "257",
                     "--no-unwinding-assertions", "--object-bits", "13"],
        })

    ok(f"Generated {len(benchmarks)} CSmith benchmarks in {bench_dir}")
    return benchmarks
