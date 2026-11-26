extern "C" void __CPROVER_assert(bool, const char *);

// [temp.names]/3: `<' after a name starts a template-argument-list only if
// the name is a template-name.  For variables, these are comparisons.
static bool either(int a, int b)
{
  return a < b || a > (5);
}

static bool range(int offset, int len, unsigned long n)
{
  return offset < 0 || len < 0 || offset > ((int)n) - len;
}

static bool both(int a, int b, int c)
{
  return a < b && c > -1;
}

template <int N>
bool parameter(int b, int c)
{
  return N < b && c > -1;
}

template <class T>
T maximum(T a, T b)
{
  return a < b ? b : a;
}

int main()
{
  __CPROVER_assert(either(1, 2) && either(7, 2) && !either(3, 2), "or");
  __CPROVER_assert(
    range(-1, 0, 3) && range(0, -1, 3) && range(3, 1, 3) && !range(1, 1, 3),
    "or with a cast");
  __CPROVER_assert(both(1, 2, 0) && !both(1, 2, -1), "and");
  __CPROVER_assert(
    parameter<1>(2, 0) && !parameter<3>(2, 0), "template parameter");
  // a template-id is still one
  __CPROVER_assert(maximum<int>(2 < 3 || 1 > 0, 0) == 1, "template-id");

  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
