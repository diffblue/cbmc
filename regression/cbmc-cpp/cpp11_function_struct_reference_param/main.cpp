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
// _ArgTypes pack and must be a usable reference type, so both the
// converting construction `= inc` and the call `f(s)` must type-check
// ([func.wrap.func.con], [over.match]).  Regression for the recovered
// "found no match for symbol 'operator()'" / "invalid implicit
// conversion ... to struct function" diagnostics, which required the
// instantiated operator() parameter and the converting-constructor
// constraint (is_invocable_r, which uses
// __reference_converts_from_temporary) to be handled.  std::function's
// type-erased call result is not modelled, so this is a front-end
// type-checking test that must compile without a CONVERSION ERROR.
int main()
{
  std::function<int(const S &)> f = inc;
  S s{41};
  int r = f(s);
  (void)r;
  return 0;
}
