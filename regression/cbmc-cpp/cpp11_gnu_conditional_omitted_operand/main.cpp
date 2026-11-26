extern "C" void __CPROVER_assert(bool, const char *);
static int calls = 0;
int next()
{
  return ++calls;
}
const char *name(const char *a, const char *b)
{
  return a ?: (b ?: "unknown");
}
int main()
{
  // GNU `a ?: b': a if it is nonzero, else b; a is evaluated once
  __CPROVER_assert(*name(nullptr, "x") == 'x', "pointer");
  __CPROVER_assert(*name(nullptr, nullptr) == 'u', "nested");
  int v = next() ?: 10;
  __CPROVER_assert(v == 1 && calls == 1, "evaluated once");
  int zero = 0;
  __CPROVER_assert((zero ?: 7) == 7, "zero");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
