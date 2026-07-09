// N5008 [temp.inst]/2, [basic.lookup.unqual], [dcl.meaning]: when a class
// template is instantiated, its member functions -- including those defined
// out of line -- are instantiated with unqualified names looked up in the scope
// of the template definition, not the scope where the instantiation is
// triggered.  A namespace-scope name in the leading return type of an
// out-of-line member definition `RetT C<T>::m(...)` is resolved in the
// template's namespace.
//
// KNOWNBUG: reduced (via cvise) from the src/util/interval_union.cpp dog-food
// failure ("symbol '_StateIdT' is unknown" while instantiating
// std::__detail::_NFA<regex_traits> during std::regex use).  When instantiating
// a class template's methods, CBMC restores the scope saved at entry to
// instantiate_template -- i.e. the scope that first triggered the instantiation
// -- before creating each method's template scope.  A preceding namespace-scope
// overload resolution of `operator<<` (which considers an alias-template return
// type `bop<I> = I::__type`) makes NFA<char> first be instantiated from a
// function-body scope; the out-of-line member `ins`'s template scope is then
// created under that function-body scope, so the namespace-scope typedef `SID`
// in its return type is looked up in the wrong scope and not found.
//
// A fix that unconditionally re-enters the template scope before instantiating
// each method resolves this case but has an unacceptable blast radius (it
// regresses many real-STL template instantiations such as std::unordered_map,
// whose method instantiation relies on the restored instantiation-context
// scope).  A correct, narrowly-scoped fix -- likely preserving the
// instantiation-context using-scopes while ensuring the template's namespace is
// reachable -- is still needed.  Flip to CORE once that lands.
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
