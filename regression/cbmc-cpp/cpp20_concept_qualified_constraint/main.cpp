// C++20: a *qualified* concept name used as a type-constraint on a template
// parameter (N5008 [temp.param]/4, [temp.names]) must be recognised as a
// type-constraint, not mistaken for a non-type parameter because of the
// leading namespace.  This is the shape libstdc++ uses for iter_reference_t:
//   namespace std::__detail { template<class T> concept __dereferenceable; }
//   template<__detail::__dereferenceable T> using iter_reference_t = ...;
//
// Previously CBMC parsed `__detail::__dereferenceable _Tp` as a non-type
// parameter of type `__detail::__dereferenceable`, so instantiating the alias
// with a type argument failed ("expected expression, but got type"); when the
// enclosing class was first instantiated in a declaration context (a function
// signature), the failure truncated the class to zero components and the
// truncated form was cached, so a later brace-construction fell back to
// aggregate initialisation and went out of bounds.

namespace ns
{
namespace __detail
{
template <typename _Tp>
concept __dereferenceable = true;
}
// Alias template with a QUALIFIED concept name as its type-constraint.
template <__detail::__dereferenceable _Tp>
using ref_t = _Tp;

template <typename>
struct container
{
  ref_t<int> member;
  container(char *, long) {}
};

// A declaration whose signature instantiates container<wchar_t> *before* the
// construction below -- this is what made the truncation observable.
container<wchar_t> make();
} // namespace ns

int main()
{
  char *p = nullptr;
  long n = 2;
  ns::container<wchar_t> c{p, n};
  // If the class elaborated correctly it has its 'member' component.
  __CPROVER_assert(sizeof(c.member) == sizeof(int), "member elaborated");
  return 0;
}
