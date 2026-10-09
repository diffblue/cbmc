// N5008 [dcl.type.decltype]/1: an unparenthesized id-expression or member
// access denotes the declared type (1.3); an xvalue gives T&& (1.4); any
// other lvalue -- subscript, assignment, prefix increment, comma,
// conditional, a PARENTHESIZED id-expression or member access -- gives T&
// (1.5); a prvalue gives T (1.6).  Only `*p' and string literals had the
// lvalue rule; `decltype(a[i])' was `int'.
extern "C" void __CPROVER_assert(bool, const char *);
#include <type_traits>
#include <utility>
struct S
{
  int m;
  double d;
};
int gi;
int &lref();
int &&rref();
int val();
S sval();
#define SAME(a, b) static_assert(std::is_same<a, b>::value, #a " == " #b)
int main()
{
  int x = 0, y = 0;
  int arr[3] = {0};
  int *p = arr;
  S s{1, 2.0};
  const S cs{1, 2.0};
  bool c = true;
  SAME(decltype(x), int);
  SAME(decltype(arr[1]), int &);
  SAME(decltype(*p), int &);
  SAME(decltype(x = 1), int &);
  SAME(decltype(x += 1), int &);
  SAME(decltype(++x), int &);
  SAME(decltype(x++), int);
  SAME(decltype(c ? x : y), int &);
  SAME(decltype(c ? x : 1), int);
  SAME(decltype(x, y), int &);
  SAME(decltype(s.m), int);
  SAME(decltype(cs.m), int);
  SAME(decltype(s.d), double);
  SAME(decltype(S()), S);
  SAME(decltype(S{}), S);
  SAME(decltype(sval()), S);
  SAME(decltype(sval().m), int);
  SAME(decltype(lref()), int &);
  SAME(decltype(rref()), int &&);
  SAME(decltype(val()), int);
  SAME(decltype(std::move(x)), int &&);
  SAME(decltype(gi), int);
  SAME(decltype(p[0]), int &);
  SAME(decltype(arr), int[3]);
  SAME(decltype(*p + 1), int);
  SAME(decltype(-x), int);
  SAME(decltype(&x), int *);
  SAME(decltype(s.m = 3), int &);
  SAME(decltype(static_cast<int &>(x)), int &);
  SAME(decltype(static_cast<int &&>(x)), int &&);
  SAME(decltype(static_cast<int>(x)), int);
  SAME(decltype((x)), int &);
  SAME(decltype((s.m)), int &);
  SAME(decltype((cs.m)), const int &);
  decltype(arr[1]) r = arr[0];
  r = 5;
  __CPROVER_assert(arr[0] == 5, "decltype(arr[1]) is int &: r aliases arr[0]");
  decltype((s.m)) rm = s.m;
  rm = 9;
  __CPROVER_assert(s.m == 9, "decltype((s.m)) is int &");
  return 0;
}
