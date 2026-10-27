// N5008 [over.match.class.deduct]/3 (C++20): class template argument
// deduction for an alias template -- `Q q{3, 4}' with `template <class T>
// using Q = P<T, int>' deduces T = int from the guides of P.  g++ 13
// accepts the program; clang++ implements this from version 19.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T, class U>
struct P
{
  T a;
  U b;
};
template <class T>
using Q = P<T, int>;
int main()
{
  Q q{3, 4};
  __CPROVER_assert(q.a + q.b == 7, "alias template CTAD");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
