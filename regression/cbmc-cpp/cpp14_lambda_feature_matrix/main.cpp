// Lambda feature matrix (found while testing the shapes around user Issue
// 11).  Each failing case below was a separate front-end bug:
//  * N5008 [expr.prim.lambda.capture]/6: an init-capture by reference
//    `[&r = k]' names the referent `r' in the body ("symbol 'r' is unknown");
//  * [expr.prim.lambda.closure]/1: each lambda-expression has its own closure
//    type -- the closure was cached by source LINE (the lexer records no
//    column), so two lambdas on one line, or in two one-line member
//    functions, shared a closure and the second call ran the first body
//    (wrong value, or an invariant in symex for `[*this]');
//  * [dcl.spec.auto.general]/3 + [temp.param]: `auto... xs' invents a
//    template parameter PACK -- it accepted exactly one argument;
//  * [expr.prim.fold]/2: the binary fold `(xs op ... op init)' (pack on the
//    left) was not expanded in a generic lambda's operator();
//  * [expr.sizeof]/2: sizeof of a reference-typed expression is the size of
//    the referenced type.
extern "C" void __CPROVER_assert(bool, const char *);
#include <utility>
struct W
{
  int soc;
  int get() const
  {
    return soc;
  }
};
struct Holder
{
  int v = 5;
  int run() const
  {
    return [this] { return v; }();
  }
  int run2() const
  {
    return [*this] { return v + 1; }();
  }
  int run3() const
  {
    return [this] { return v * 2; }();
  }
};
struct NS
{
  int v = [] { return 6; }();
};
int main()
{
  int k = 3, m = 4;
  W w{4};
  // init-captures
  auto a = [x = k + 1] { return x; };
  auto b = [&rr = k]
  {
    rr = 10;
    return rr;
  };
  auto c = [w2 = std::move(w)] { return w2.soc; };
  int arr[2] = {1, 2};
  auto d = [&x = arr[1]]
  {
    x = 9;
    return x;
  };
  auto e = [cw = W{8}] { return cw.soc; };
  __CPROVER_assert(
    a() == 4 && b() == 10 && k == 10 && c() == 4,
    "init-captures by value, reference, move");
  __CPROVER_assert(
    d() == 9 && arr[1] == 9 && e() == 8,
    "init-capture of an element by reference, of a temporary");
  // mutable state
  auto cnt = [n = 0]() mutable { return ++n; };
  cnt();
  cnt();
  __CPROVER_assert(cnt() == 3, "mutable state persists in the closure");
  // two lambdas on one line, and one per one-line member function
  auto p1 = [](int x) { return x + 1; };
  auto p2 = [](int x) { return x + 2; };
  __CPROVER_assert(
    p1(0) == 1 && p2(0) == 2, "two lambdas on one line have distinct closures");
  Holder h;
  __CPROVER_assert(
    h.run() == 5 && h.run2() == 6 && h.run3() == 10,
    "this, *this and a second this-lambda");
  NS ns;
  __CPROVER_assert(ns.v == 6, "lambda in a default member initializer");
  // generic lambdas
  auto fwd = [](auto &&x) -> decltype(auto)
  { return std::forward<decltype(x)>(x); };
  auto sum = [](auto... xs) { return (xs + ... + 0); };
  auto lsum = [](auto... xs) { return (0 + ... + xs); };
  auto rsub = [](auto... xs) { return (xs - ... - 0); };
  auto lsub = [](auto... xs) { return (100 - ... - xs); };
  auto usum = [](auto &&...xs) { return (xs + ...); };
  auto cntp = [](auto... xs) { return sizeof...(xs); };
  auto lead = [](int a0, auto... xs) -> int { return a0 + (xs + ... + 0); };
  __CPROVER_assert(fwd(m) == 4, "forwarding generic lambda");
  __CPROVER_assert(
    sum(1, 2, 3) == 6 && sum() == 0 && sum(5) == 5,
    "auto... with a binary right fold, 3/0/1 arguments");
  __CPROVER_assert(
    lsum(1, 2, 3) == 6 && rsub(10, 3, 2) == 9 && lsub(10, 3, 2) == 85,
    "left/right associativity of binary folds");
  __CPROVER_assert(
    usum(1, 2, 3) == 6 && cntp(1, 2) == 2 && cntp() == 0,
    "unary fold, sizeof...");
  __CPROVER_assert(
    lead(1, 2, 3) == 6,
    "leading parameter before the pack, explicit return type");
  // sizeof of a reference
  auto sz = [](auto &&x) { return sizeof(x); };
  int &kr = k;
  __CPROVER_assert(
    sz(k) == sizeof(int) && sizeof(kr) == sizeof(int),
    "sizeof of a reference is the referenced type's");
  // returning a reference; nested lambdas; conversion to function pointer
  auto ref = [](int &x) -> int & { return x; };
  ref(m) = 7;
  auto outer = [k](int x) { return [x, k](int y) { return x + y + k; }; };
  int (*fp)(int) = [](int x) { return x + 1; };
  __CPROVER_assert(
    m == 7 && outer(1)(2) == 13 && fp(1) == 2,
    "reference return, nested lambda, function pointer");
  return 0;
}
