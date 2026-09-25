// N5008 [temp.deduct.type]: deducing `tuple<A1...>` from an argument of
// type `tuple<int&&>` compares the pattern's template-argument list with
// the argument type's arguments RELATIVE TO THE PRIMARY TEMPLATE -- also
// when `tuple<int&&>` is an explicit (full) specialization
// (`template<> struct tuple<int&&>`), whose own template-parameter list is
// empty.  The member constructor template with a deduced pack (the
// std::pair piecewise-constructor shape) must then be viable.
//
// Was KNOWNBUG: the instance symbol of a full specialization recorded only
// the specialization-relative (empty) argument list; pack deduction read it
// and bound A1 to ZERO elements, instantiating `pair(pc_t, tuple<>)` and
// rejecting the call ("found no match"), which dropped the enclosing
// function body.
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
  template <typename... A1>
  pair(pc_t, tuple<A1...> t1) : first(sizeof...(A1)), second(t1.v)
  {
  }
};

template <typename T>
int make(tuple<int &&> t1)
{
  T p(pc_t{}, t1);
  return p.first * 100 + p.second;
}

int main()
{
  int x = 42;
  tuple<int &&> t1(static_cast<int &&>(x));
  __CPROVER_assert(
    make<pair<const int, int>>(t1) == 142,
    "pack deduced from explicit specialization");
  return 0;
}
