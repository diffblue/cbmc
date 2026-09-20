// User-reported Issue 13 (first half).  N5008 [temp.deduct.conv]/1 deduces
// the conversion function template's parameter from the target type;
// [temp.deduct]/5 supplies the remaining parameters from their default
// template arguments -- the SFINAE idiom `template <class U, class =
// enable_if_t<...>> operator U() const'.  The defaulted parameter was left
// unassigned and the candidate dropped ("invalid implicit conversion").
// The default may name the enclosing class template's parameter (T).
extern "C" void __CPROVER_assert(bool, const char *);
#include <type_traits>
typedef unsigned int uint32_t;
typedef unsigned long uint64_t;
template <class T>
struct __attribute__((packed)) Wrap
{
  using value_type = T;
  T v;
  template <class U, class = std::enable_if_t<std::is_convertible_v<T, U>>>
  operator U() const
  {
    return static_cast<U>(v);
  }
};
template <class T>
struct Wrap2
{
  T v;
  template <class U, std::enable_if_t<std::is_arithmetic_v<U>, int> = 0>
  operator U() const
  {
    return static_cast<U>(v) + 1;
  }
};
int main()
{
  Wrap<uint32_t> w{5};
  uint64_t h = w;
  int i = w;
  Wrap2<int> w2{6};
  long l = w2;
  __CPROVER_assert(h == 5 && i == 5, "defaulted type parameter (enable_if_t)");
  __CPROVER_assert(l == 7, "defaulted non-type parameter");
  return 0;
}
