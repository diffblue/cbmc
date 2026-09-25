// N5008 [temp.param]/14, [temp.variadic]/5: a member template's
// template-parameter-list may contain MULTIPLE parameter packs when each is
// deducible from the function parameter list -- the std::pair piecewise
// constructor `template<class... _Args1, class... _Args2>
// pair(piecewise_construct_t, tuple<_Args1...>, tuple<_Args2...>)`.
// Instantiating the winner must keep each pack's own deduced elements
// (here A1 = {int&&}, A2 = {}), not swap or collapse them.
//
// Was KNOWNBUG: the flat template-argument list of the deduced instance
// cannot encode the split between two packs; rebuilding the template map
// from it bound the packs wrongly (first pack empty, second pack getting
// the first's element), instantiating `pair(pc_t, tuple<>, tuple<int&&>)`
// -- no viable candidate remained and the enclosing body was dropped.
extern "C" void __CPROVER_assert(int, const char *);

struct pc_t
{
};

template <typename... E>
struct tuple
{
};
template <>
struct tuple<int &&>
{
  int v;
  tuple(int &&x) : v(x)
  {
  }
};

template <typename T1, typename T2>
struct pair
{
  T1 first;
  T2 second;
  pair() : first(), second()
  {
  }
  template <typename... A1, typename... A2>
  pair(pc_t, tuple<A1...> t1, tuple<A2...>) : first(t1.v), second(sizeof...(A1))
  {
  }
};

template <typename T>
int make(tuple<int &&> t1, tuple<> t2)
{
  T p(pc_t{}, t1, t2);
  return p.first * 10 + p.second;
}

int main()
{
  int x = 4;
  tuple<int &&> t1(static_cast<int &&>(x));
  tuple<> t2;
  // first = t1.v = 4; second = 1 (A1 deduced to one element, A2 to zero --
  // a swapped instantiation would fail to resolve or read v from tuple<>)
  __CPROVER_assert(
    make<pair<const int, int>>(t1, t2) == 41, "two-pack piecewise ctor");
  return 0;
}
