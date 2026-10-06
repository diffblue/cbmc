// N5008 [expr.prim.req.general]/2, [dcl.type.decltype]/1,
// [basic.def.odr]/5, [temp.inst]/4: the operands of a requires-expression
// and of decltype are unevaluated, so the member functions they name are
// not odr-used and their definitions are not instantiated there
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct wrap
{
  typedef int reference;
};
template <class It>
concept cpp17_iterator =
  requires(It it) { typename wrap<decltype(it++)>::reference; };
// libstdc++'s __cpp17_iterator: a compound requirement
template <class T>
concept can_reference = requires { typename wrap<T>; };
template <class It>
concept compound_iterator = requires(It it) {
                              {
                                it++
                                } -> can_reference;
                            };
// libstdc++'s __normal_iterator over a pointer to an incomplete class
template <class P>
struct normal_iterator
{
  P current;
  normal_iterator operator++(int)
  {
    normal_iterator old = *this;
    current++;
    return old;
  }
};
// libstdc++'s iterator_traits checks __cpp17_iterator for
// __normal_iterator<_BigBlock *> (vector<_BigBlock> in __pool_resource);
// opaque is never defined, so that body would be ill-formed
struct opaque;
constexpr bool checked = cpp17_iterator<normal_iterator<opaque *>>;
struct other;
constexpr bool compound = compound_iterator<normal_iterator<other *>>;
struct block
{
  int n;
};
int main()
{
  __CPROVER_assert(checked, "concept satisfied");
  __CPROVER_assert(compound, "compound requirement satisfied");
  block b[2] = {{1}, {2}};
  normal_iterator<block *> it{b};
  it++;
  __CPROVER_assert(it.current->n == 2, "instantiated when odr-used");
  __CPROVER_assert(it.current->n == 1, "WRONG (must FAIL)");
}
