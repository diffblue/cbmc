// Dog-food kernel (src/util/interval_union.cpp): CBMC's ranget has a
// template CONVERSION OPERATOR 'template<class C> operator C()'
// ([class.conv.fct], [temp.deduct.conv]); passing a ranget where a
// const std::vector<exprt>& parameter is expected must use it.  CBMC
// reports 'found no match' for the callee instead.
#include <vector>
extern "C" void __CPROVER_assert(bool, const char *);
template <class It> struct ranget
{
  It b_, e_;
  It begin() const
  {
    return b_;
  }
  It end() const
  {
    return e_;
  }
  template <class C> operator C() const
  {
    return C(begin(), end());
  }
};
int sum(const std::vector<int> &v)
{
  int s = 0;
  for(int x : v)
    s += x;
  return s;
}
int main()
{
  int arr[3] = {1, 2, 3};
  ranget<int *> r{arr, arr + 3};
  __CPROVER_assert(sum(r) == 6, "range converts to vector parameter");
  return 0;
}
