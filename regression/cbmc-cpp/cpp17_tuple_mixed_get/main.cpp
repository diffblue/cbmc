// N5008 [intro.object]/[class.derived] + [tuple.elem]: std::get on a
// directly-constructed two-element std::tuple with elements of DIFFERENT sizes
// (int then double).  Exercises the base-subobject byte-offset computation for
// the recursive _Tuple_impl layout: the second element's _Head_base is a
// non-first base whose offset depends on the (differently-sized) preceding
// element, so a correct, data-only offset is required for std::get<1> to read
// the right subobject.
//
// Non-vacuous: the int element is nondet so the passing assertions are not
// folded, and the last assertion is a deliberately wrong claim that must FAIL.

#include <tuple>

extern "C" void __CPROVER_assert(int, const char *);
extern int nondet_int(void);

int main()
{
  int a = nondet_int();
  std::tuple<int, double> t(a, 2.5);
  __CPROVER_assert(std::get<0>(t) == a, "tuple get<0> reads the int element");
  __CPROVER_assert(
    std::get<1>(t) == 2.5, "tuple get<1> reads the double element");
  __CPROVER_assert(std::get<1>(t) == 1.5, "WRONG must FAIL");
  return 0;
}
