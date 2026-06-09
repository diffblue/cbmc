#include <cassert>
#include <functional>

struct S
{
  int v;
};

int inc(const S &s)
{
  return s.v + 1;
}

// std::function whose call signature takes a reference (or pointer) to a
// class type.  The instantiated operator() parameter is derived from the
// _ArgTypes pack and must be a usable reference type, so the call f(s)
// must resolve ([over.match]).  Regression for "found no match for symbol
// 'operator()'" where the parameter remained an unconverted
// frontend_pointer.
int main()
{
  std::function<int(const S &)> f = inc;
  S s{41};
  assert(f(s) == 42);
  return 0;
}
