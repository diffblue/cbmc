// N5008 [dcl.spec.auto.general], [dcl.type.auto.deduct], [dcl.type.decltype]:
// placeholder type deduction -- variables, return types, lambdas.
extern "C" void __CPROVER_assert(bool, const char *);

int i = 1;
const int ci = 3;
int &&f();
int &&f()
{
  static int x = 5;
  return static_cast<int &&>(x);
}
struct S
{
  int m = 6;
  const int cm = 7;
};

// [dcl.type.auto.deduct]/4, Example 3
auto x2a(i);
decltype(auto) x2d(i);
auto x3a = i;
decltype(auto) x3d = i;
auto x4a = (i);
decltype(auto) x4d = (i);
auto x5a = f();
decltype(auto) x5d = f();
auto *x7a = &i;
static_assert(__is_same(decltype(x2a), int), "x2a");
static_assert(__is_same(decltype(x2d), int), "x2d");
static_assert(__is_same(decltype(x3a), int), "x3a");
static_assert(__is_same(decltype(x3d), int), "x3d");
static_assert(__is_same(decltype(x4a), int), "x4a");
static_assert(__is_same(decltype(x4d), int &), "x4d: decltype((i)) is int&");
static_assert(__is_same(decltype(x5a), int), "x5a");
static_assert(__is_same(decltype(x5d), int &&), "x5d: xvalue");
static_assert(__is_same(decltype(x7a), int *), "x7a");

// [dcl.spec.auto.general]/5, Example 1 + [dcl.type.auto.deduct]/3, Example 2
const auto *v = &i, u = 6;
const auto &cr = i;
auto &mr = i;
auto &&fwd_l = i;   // forwarding reference bound to an lvalue: int&
auto &&fwd_r = f(); // bound to an xvalue: int&&
static_assert(__is_same(decltype(v), const int *), "v");
static_assert(__is_same(decltype(u), const int), "u");
static_assert(__is_same(decltype(cr), const int &), "cr");
static_assert(__is_same(decltype(mr), int &), "mr");
static_assert(__is_same(decltype(fwd_l), int &), "auto&& of lvalue");
static_assert(__is_same(decltype(fwd_r), int &&), "auto&& of xvalue");
auto ac = ci; // top-level const dropped
const S cs{};
auto am = cs.m;              // int
decltype(auto) dm = cs.m;    // declared type of the member: int
decltype(auto) dpm = (cs.m); // const int&
static_assert(__is_same(decltype(ac), int), "ac");
static_assert(__is_same(decltype(am), int), "am");
static_assert(__is_same(decltype(dm), int), "dm: unparenthesized member");
static_assert(
  __is_same(decltype(dpm), const int &),
  "dpm: parenthesized member");

// return types: [dcl.spec.auto.general]/4, /10, /11, /13
auto g()
{
  return 0.0;
}
auto h()
{
} // /11: void
auto sum(int n) // /13, Example 4: the type is usable after the first return
{
  if(n == 1)
    return n;
  else
    return sum(n - 1) + n;
}
auto two_returns(bool b) // /10: same type in each deduction
{
  if(b)
    return 1;
  return 2;
}
auto &lref()
{
  return i;
}
const auto &clref()
{
  return i;
}
auto &cref()
{
  return ci;
} // const int &
auto *pret()
{
  return &ci;
} // const int *
decltype(auto) da_id()
{
  return i;
} // int
decltype(auto) da_paren()
{
  return (i);
} // int&
decltype(auto) da_xval()
{
  return f();
} // int&&
decltype(auto) da_member()
{
  return cs.m;
} // int
auto arr_decay(int (&a)[3])
{
  return a;
} // int*
static_assert(__is_same(decltype(g()), double), "g");
static_assert(__is_same(decltype(h()), void), "h: void");
static_assert(__is_same(decltype(sum(3)), int), "sum");
static_assert(__is_same(decltype(two_returns(true)), int), "two_returns");
static_assert(__is_same(decltype(lref()), int &), "lref");
static_assert(__is_same(decltype(clref()), const int &), "clref");
static_assert(__is_same(decltype(cref()), const int &), "cref");
static_assert(__is_same(decltype(pret()), const int *), "pret");
static_assert(
  __is_same(decltype(da_id()), int),
  "decltype(auto) id-expression");
static_assert(__is_same(decltype(da_paren()), int &), "decltype(auto) (id)");
static_assert(__is_same(decltype(da_xval()), int &&), "decltype(auto) xvalue");
static_assert(__is_same(decltype(da_member()), int), "decltype(auto) member");
int main()
{
  int a3[3] = {1, 2, 3};
  static_assert(__is_same(decltype(arr_decay(a3)), int *), "array decays");
  // lambdas: return type deduced from the body ([expr.prim.lambda.closure]/4)
  auto l1 = []() { return 2.5; };
  auto l2 = [](int k)
  {
    if(k > 0)
      return k;
    return -k;
  };
  auto l3 = []() {};
  auto l4 = [](int &r) -> decltype(auto) { return (r); };
  static_assert(__is_same(decltype(l1()), double), "l1");
  static_assert(__is_same(decltype(l2(1)), int), "l2");
  static_assert(__is_same(decltype(l3()), void), "l3: void");
  static_assert(__is_same(decltype(l4(i)), int &), "l4");
  lref() = 9;
  l4(i) = 10;
  __CPROVER_assert(
    i == 10 && sum(4) == 10 && two_returns(false) == 2 && cref() == 3 &&
      *pret() == 3 && da_paren() == 10 && *arr_decay(a3) == 1 && l2(-4) == 4 &&
      l1() == 2.5,
    "values");
  __CPROVER_assert(sum(4) == 11, "WRONG (must FAIL)");
  return 0;
}
