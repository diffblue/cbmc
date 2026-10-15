extern "C" void __CPROVER_assert(bool, const char *);
// The shape of libstdc++ 16's __common_reference_impl<_Tp1, _Tp2, _Bullet>:
// each specialization derives from the next one until a (constrained)
// partial specialization matches ([temp.spec.partial.match]/1,
// [temp.constr.decl]/1).  impl<int, 2> needs two steps: impl<int, 3>, then
// the partial specialization impl<int, 4>.
template <typename T, int B = 1>
struct impl : impl<T, B + 1>
{
};
template <typename T>
requires true struct impl<T, 4>
{
  using type = T;
};
int main()
{
  // impl<int, 3> must not be instantiated first: then the chain works
  __CPROVER_assert(__is_same(impl<int, 2>::type, int), "two steps");
  __CPROVER_assert(__is_same(impl<int, 3>::type, int), "one step");
  __CPROVER_assert(!__is_same(impl<int, 2>::type, int), "WRONG (must FAIL)");
}
