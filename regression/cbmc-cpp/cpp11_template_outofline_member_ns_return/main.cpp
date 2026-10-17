// N5008 [temp.inst]/2, [basic.lookup.unqual], [dcl.meaning]: when a class
// template is instantiated, its member functions -- including those defined
// out of line -- are instantiated in the context of the (instantiated) class;
// unqualified names in a member are looked up as if in the class, so they reach
// the class's own members and, through the class's enclosing namespace,
// namespace-scope names.  In particular a namespace-scope name in the leading
// return type of an out-of-line member definition `RetT C<T>::m(...)` resolves
// in the template's namespace, regardless of where the instantiation is
// triggered.
//
// Regression test reduced (via cvise) from the src/util/interval_union.cpp
// dog-food failure ("symbol '_StateIdT' is unknown" while instantiating
// std::__detail::_NFA<regex_traits> during std::regex use).  Instantiating a
// class template's method created that method's scope under whatever scope
// first triggered the instantiation -- here a namespace-scope overload
// resolution of `operator<<` that considers an alias-template return type makes
// NFA<char> first be instantiated from a function-body scope -- rather than the
// instantiated class's scope, so the namespace-scope typedef `SID` in the
// out-of-line member's return type was looked up in the wrong scope.
// assertion "WRONG" must FAIL (non-vacuity).

extern "C" void __CPROVER_assert(int, const char *);

struct OS
{
};
struct OS2 : OS
{
};
enum byte : char;
template <typename I>
using bop = typename I::__type;
template <typename I>
bop<I> operator<<(byte, I);
void operator<<(OS, int)
{
  OS2 o;
  o << 0;
}

namespace det
{
typedef long SID;
template <typename>
struct NFA
{
  SID ins(SID v);
};
// out-of-line member: leading return type `SID` is a namespace-scope typedef
template <typename T>
SID NFA<T>::ins(SID v)
{
  return v + 1;
}
} // namespace det

int main()
{
  det::NFA<char> n;
  __CPROVER_assert(
    n.ins(41) == 42,
    "out-of-line template member return type resolved; body correct");
  __CPROVER_assert(n.ins(41) != 42, "WRONG must FAIL");
  return 0;
}
