// [expr.prim.lambda.closure]: a generic lambda's function call operator is a
// member function template -- each `auto` parameter introduces an invented
// template type parameter, instantiated per call.  Captures behave as for a
// non-generic lambda: a by-copy capture is a snapshot taken at capture time,
// and distinct closures (e.g. from a factory) have independent state.

auto make_adder(int n)
{
  return [n](auto x) { return x + n; };
}

int main()
{
  // one generic closure instantiated at two argument types
  auto inc = [](auto x) { return x + 1; };
  __CPROVER_assert(inc(4) == 5, "generic operator() instantiated for int");
  __CPROVER_assert(inc(4L) == 5L, "generic operator() instantiated for long");

  // by-copy capture is a capture-time snapshot, even for a generic lambda
  int a = 10;
  auto f = [a](auto x) { return x + a; };
  a = 20;
  __CPROVER_assert(f(5) == 15, "generic by-copy capture snapshots at capture");

  // a factory yields independent generic closures (per-instance state)
  auto a3 = make_adder(3);
  auto a10 = make_adder(10);
  __CPROVER_assert(a3(1) == 4, "first generic closure has its own capture");
  __CPROVER_assert(a10(1) == 11, "second generic closure is independent");
  return 0;
}
