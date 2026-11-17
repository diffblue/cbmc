// N5008 [expr.const]/10.22 (C++26): an exception may be thrown and caught
// within a constant evaluation, when its object is destroyed within it.
// Handlers are matched in order ([except.handle]/5), across nested
// try-blocks, `throw;' rethrows ([expr.throw]/3), and the exception
// object may be of class type and caught by reference.
extern "C" void __CPROVER_assert(bool, const char *);
struct E
{
  int code;
};
constexpr int nested(int x)
{
  try
  {
    try
    {
      if(x > 0)
        throw x;
      return -1;
    }
    catch(long)
    {
      return 100;
    }
  }
  catch(int v)
  {
    return v * 2;
  }
}
constexpr int rethrown(int x)
{
  try
  {
    try
    {
      throw x;
    }
    catch(...)
    {
      throw;
    }
  }
  catch(int v)
  {
    return v + 1;
  }
  return 0;
}
constexpr int with_class(int x)
{
  try
  {
    throw E{x};
  }
  catch(const E &e)
  {
    return e.code;
  }
  return 0;
}
constexpr int loop(int n)
{
  int s = 0;
  for(int i = 0; i < n; ++i)
  {
    try
    {
      if(i % 2)
        throw i;
      s += 1;
    }
    catch(int j)
    {
      s += 10 * j;
    }
  }
  return s;
}
static_assert(nested(3) == 6);
static_assert(nested(0) == -1);
static_assert(rethrown(4) == 5);
static_assert(with_class(7) == 7);
static_assert(loop(4) == 42);
template <int V>
struct W
{
  static constexpr int value = V;
};
int main()
{
  __CPROVER_assert(
    W<nested(5)>::value == 10 && W<loop(4)>::value == 42,
    "constant evaluation");
  __CPROVER_assert(
    nested(2) == 4 && rethrown(1) == 2 && with_class(3) == 3, "run time");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
