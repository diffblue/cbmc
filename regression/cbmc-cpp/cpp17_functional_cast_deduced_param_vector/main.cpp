// Residual layer behind cpp17_conversion_operator_to_container (round
// 87): inside an INSTANTIATED template conversion operator
// `template <class C> operator C() const { return C(begin(), end()); }`
// with C = std::vector<int>, the functional cast C(b, e) must resolve
// vector's member-template iterator-pair constructor
// ([expr.type.conv], [over.match.ctor]).  CBMC reports "found no match
// for symbol 'C'" at the cast.  The non-vector sibling (plain class
// with a two-pointer constructor) works.
#include <vector>
extern "C" void __CPROVER_assert(bool, const char *);
struct ranget
{
  int *b_, *e_;
  int *begin() const
  {
    return b_;
  }
  int *end() const
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
  ranget r{arr, arr + 3};
  __CPROVER_assert(sum(r) == 6, "conversion op to vector");
  return 0;
}
