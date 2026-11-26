// N5008 [expr.cond]/7: array-to-pointer and function-to-pointer
// conversions are applied to the second and third operands; then, as one
// has pointer type, 7.3: their composite pointer type ([expr.type]/3.2: a
// null pointer constant takes the other operand's type).
extern "C" void __CPROVER_assert(bool, const char *);

template <class T, class U>
struct same
{
  static const bool value = false;
};
template <class T>
struct same<T, T>
{
  static const bool value = true;
};

int f(int x)
{
  return x + 1;
}

bool nondet_bool();

int main()
{
  bool b = nondet_bool();
  char buf[4] = {'x', 0, 0, 0};
  const char *cp = "y";
  const char *p = b ? "C" : nullptr;
  static_assert(same<decltype(b ? "C" : nullptr), const char *>::value, "");
  const char *q = b ? buf : cp;
  static_assert(same<decltype(b ? buf : cp), const char *>::value, "");
  int (*fp)(int) = b ? f : nullptr;
  static_assert(same<decltype(b ? f : nullptr), int (*)(int)>::value, "");
  char *r = b ? 0 : buf;
  __CPROVER_assert(b ? p[0] == 'C' : p == nullptr, "string or null");
  __CPROVER_assert(b ? q[0] == 'x' : q[0] == 'y', "array or pointer");
  __CPROVER_assert(b ? fp(1) == 2 : fp == nullptr, "function or null");
  __CPROVER_assert(b ? r == nullptr : r[0] == 'x', "null or array");
  __CPROVER_assert(p != nullptr, "WRONG (must FAIL)");
  return 0;
}
