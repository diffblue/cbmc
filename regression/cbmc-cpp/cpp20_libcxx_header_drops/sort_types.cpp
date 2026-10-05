// N5008 [alg.sort]/1: sort leaves [first, last) in non-decreasing order
// (libc++ defines its std::__sort for these types only in libc++.so)
#include <algorithm>
#include <functional>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  double d[4] = {2.5, -1.0, 2.5, 0.0};
  std::sort(d, d + 4);
  __CPROVER_assert(
    d[0] == -1.0 && d[1] == 0.0 && d[2] == 2.5 && d[3] == 2.5, "double");
  unsigned u[3] = {7u, 0u, 4294967295u};
  std::sort(u, u + 3, std::less<unsigned>());
  __CPROVER_assert(u[0] == 0u && u[2] == 4294967295u, "unsigned, less");
  long e[1] = {5};
  std::sort(e, e + 1);
  std::sort(e, e);
  __CPROVER_assert(e[0] == 5, "one element and empty ranges");
  char c[3] = {'c', 'a', 'b'};
  std::sort(c, c + 3);
  __CPROVER_assert(c[0] == 'a' && c[1] == 'b' && c[2] == 'c', "char");
  __CPROVER_assert(d[0] == 0.0, "WRONG (must FAIL)");
}
