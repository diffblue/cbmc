// --generate-function-body havoc on a function whose return type reaches a
// deep struct hierarchy without recursion: max_nondet_tree_depth does not
// limit it, as no struct tag recurs on a pointer chain, and the object factory
// allocates 341 objects.  --max-dynamic-object-instances limits this number.
//
// With this 5-level, 4-way-branching hierarchy the uncapped factory would
// allocate 1 + 4 + 16 + 64 + 256 = 341 dynamic objects.  The test caps it
// at 10 and checks -- via the --show-goto-functions step in the test
// harness -- that generation is bounded accordingly: the 11th allocation
// site (make_l1::malloc_site$9) is absent.  Without the cap that site
// would be present, so the test fails if the fix is reverted.  The test
// only exercises goto-instrument body generation (the harness additionally
// runs cbmc on the result, which trivially succeeds).

typedef struct l5
{
  int a, b, c, d;
} l5_t;

typedef struct l4
{
  l5_t *p1, *p2, *p3, *p4;
  int x;
} l4_t;

typedef struct l3
{
  l4_t *p1, *p2, *p3, *p4;
  int x;
} l3_t;

typedef struct l2
{
  l3_t *p1, *p2, *p3, *p4;
  int x;
} l2_t;

typedef struct l1
{
  l2_t *p1, *p2, *p3, *p4;
  int x;
} l1_t;

// Without the cap, havoc-body generation recursively nondet-inits
// l1 -> l2 -> l3 -> l4 -> l5, branching 4-way at each level, producing an
// exponentially large init body.  With the cap, generation terminates
// after a bounded number of allocations.
l1_t *make_l1(void);

int main(void)
{
  l1_t *p = make_l1();
  return p != (l1_t *)0 ? 1 : 0;
}
