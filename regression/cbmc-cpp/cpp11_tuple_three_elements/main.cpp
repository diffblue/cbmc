// Real libstdc++ std::tuple with THREE elements: direct construction and
// std::get<0/1/2> must read the element placed at each position.  This is the
// end-to-end check for the recursive _Tuple_impl construction (trailing-pack
// partial-specialization matching, base-specifier and member-initializer pack
// expansion) together with std::get's deduction of _Head/_Tail... from the
// _Tuple_impl base argument (which requires the partial-spec instance to record
// its full template-argument list).  N5008 [tuple], [temp.deduct.type],
// [temp.variadic].
//
// Non-vacuous: operands are nondet and the last assertion is a deliberately
// wrong claim that must FAIL.
#include <tuple>

extern "C" void __CPROVER_assert(int, const char *);
extern int nondet_int(void);

int main()
{
  int a = nondet_int();
  int b = nondet_int();
  int c = nondet_int();
  std::tuple<int, int, int> t(a, b, c);
  __CPROVER_assert(std::get<0>(t) == a, "get<0> is the first element");
  __CPROVER_assert(std::get<1>(t) == b, "get<1> is the second element");
  __CPROVER_assert(std::get<2>(t) == c, "get<2> is the third element");
  __CPROVER_assert(std::get<2>(t) == a, "WRONG must FAIL");
  return 0;
}
