extern "C" void __CPROVER_assert(bool, const char *);
// As main.cpp, with unsatisfied constrained partial specializations on the
// way ([temp.spec.partial.match]/1: a partial specialization whose
// constraints are not satisfied does not match), as in libstdc++ 16's
// common_reference<int &, long &>, which reaches bullet 4
template <typename T, int B = 1>
struct impl : impl<T, B + 1>
{
};
template <typename T>
requires false struct impl<T, 1>
{
  using type = void;
};
template <typename T>
requires false struct impl<T, 2>
{
  using type = void;
};
template <typename T>
requires true struct impl<T, 3>
{
  using type = T;
};
int main()
{
  __CPROVER_assert(__is_same(impl<int>::type, int), "bullet 3");
  __CPROVER_assert(!__is_same(impl<int>::type, int), "WRONG (must FAIL)");
}
