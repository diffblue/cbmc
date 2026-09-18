// A function indexing an array that is declared (extern, unsized) before its
// sized definition is typechecked before the array size becomes known.  The C
// front-end must rewrite the stale size-less array types carried on the symbol
// expressions in that function body to the concrete array type when the size is
// refined, otherwise the same object is typed both as a sized and as a
// size-less array and the solver hits an internal error.
extern unsigned long lookup[];

unsigned long lookup_fn(unsigned long base, unsigned long i)
{
  return base + lookup[i & 63UL];
}

unsigned long lookup[64];

int main(void)
{
  unsigned long base = 1000;
  unsigned long i = 5;
  unsigned long v = lookup_fn(base, i);
  __CPROVER_assert(v > 0, "value is positive");
  return 0;
}
