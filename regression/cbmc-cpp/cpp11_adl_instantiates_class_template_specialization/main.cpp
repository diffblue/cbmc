// N5008 [basic.lookup.argdep]/2: the associated namespaces of an argument of
// class template specialization type include the namespace of the class
// template; [temp.inst]/2: the specialization is instantiated, as its
// definition (friends, bases) affects the lookup.  Here `ns::it<int>'
// appears only in the return type of the member box<int>::first, so it was
// not yet instantiated at `count(b.first(), b.first())' and ADL searched no
// namespace: "symbol 'count' is unknown" (`transform(s.begin(), ...)' over
// __gnu_cxx::__normal_iterator, CBMC's own ms_link_cmdline.cpp,
// dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
namespace ns
{
template <typename T>
struct it
{
  T v;
};
template <typename I>
int count(I a, I b)
{
  return a.v + b.v;
}
} // namespace ns
template <typename T>
struct box
{
  T v;
  ns::it<T> first()
  {
    return {v};
  }
};
int main()
{
  box<int> b{3};
  __CPROVER_assert(count(b.first(), b.first()) == 6, "found by ADL");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
