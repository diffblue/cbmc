// N5008 [over.match.oper]/3.4: for `a < b', the rewritten candidates
// include every operator<=> found for `a <=> b', here a hidden friend
// template ([class.friend]/6) of the class template.  Its return type is an
// alias template whose arguments depend on the enclosing class's parameter
// T -- the shape of libstdc++ 16's __normal_iterator, whose return type is
// std::__detail::__synth3way_t<_Iterator, _Iter>.
#include <compare>
extern "C" void __CPROVER_assert(bool, const char *);

namespace detail
{
template <typename, typename>
using three_way_t = std::strong_ordering;
}

template <typename T>
struct iter
{
  T p;
  template <typename U>
  friend detail::three_way_t<T, U> operator<=>(const iter &l, const iter<U> &r)
  {
    return l.p < r.p   ? std::strong_ordering::less
           : r.p < l.p ? std::strong_ordering::greater
                       : std::strong_ordering::equal;
  }
};

int main()
{
  iter<int> a{1}, b{2};
  __CPROVER_assert(a < b, "a < b");
  __CPROVER_assert(!(b < a), "!(b < a)");
  __CPROVER_assert(b < a, "WRONG (must FAIL)");
}
