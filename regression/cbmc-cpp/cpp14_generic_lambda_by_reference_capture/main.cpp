extern "C" void __CPROVER_assert(bool, const char *);
// [expr.prim.lambda.closure]/4: the call operator of a generic lambda is a
// template, instantiated for each call's argument types -- also with
// by-reference captures and in a member function ([expr.prim.lambda.capture])
template <class Fn>
int call2(Fn f)
{
  return f(1) + f(2L);
}
struct S
{
  int k = 10;
  int arr[2] = {3, 4};
  int run()
  {
    return call2([this](auto a) { return k + (int)a; });
  }
  void bump()
  {
    auto g = [&](auto d) { k += (int)d; };
    g(5);
    g(1L);
  }
  int &ref()
  {
    auto r = [this](auto) -> int & { return k; };
    return r(0);
  }
  int idx()
  {
    auto f = [=](auto i) { return arr[i]; };
    return f(1) + f(0L);
  }
};
int main()
{
  int x = 1;
  auto add = [&x](auto v)
  {
    x += (int)v;
    return x;
  };
  add(2);
  add(3L);
  __CPROVER_assert(x == 6, "by-ref capture, generic");
  auto get = [&x](auto) -> int & { return x; };
  get(0) = 9;
  __CPROVER_assert(x == 9, "reference return");
  S s;
  __CPROVER_assert(s.run() == 23, "member, two instantiations");
  s.bump();
  __CPROVER_assert(s.k == 16, "member by-ref mutation");
  s.ref() = 1;
  __CPROVER_assert(s.k == 1, "member reference return");
  __CPROVER_assert(s.idx() == 7, "[=] member array");
  __CPROVER_assert(s.idx() != 7, "WRONG (must FAIL)");
}
