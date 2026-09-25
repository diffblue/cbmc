extern "C" void __CPROVER_assert(bool, const char *);
#include <type_traits>
using FP = int (*)(int, int);
template <class Fn>
using RA = typename std::result_of<Fn(int, int)>::type;
template <class Fn>
using RB = typename std::result_of<Fn &(int &, int &)>::type;
template <class Fn>
struct S
{
  typedef typename std::result_of<Fn &(int &, int &)>::type type;
};
int main()
{
  S<FP>::type a = 1;
  __CPROVER_assert(a == 1, "RA");
  return 0;
}
