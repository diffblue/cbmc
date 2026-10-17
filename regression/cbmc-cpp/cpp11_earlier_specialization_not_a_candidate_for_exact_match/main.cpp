// N5008 [temp.over]/1: for each function template, deduction for this call
// synthesizes the specialization that is a candidate.  pair(int, tup<>,
// tup<>), instantiated for holder(int), is not a candidate of its own for
// the call in holder(): checking it converted tup<int> to tup<> through
// tup's constructor template with U = tup<int>, and instantiated that
// specialization's definition, which [temp.inst]/5 requires only when it
// is used.  Its impl constructor body was then dropped.  libc++'s
// std::function (__alloc_func, __compressed_pair, tuple) does this.
extern "C" void __CPROVER_assert(bool, const char *);
template <int...>
struct seq
{
};
template <int N>
struct make_seq
{
  typedef seq<> type;
};
template <int>
struct leaf
{
};
template <class>
struct impl;
template <int... I>
struct impl<seq<I...>>
{
  template <int... J>
  impl(seq<J...>, ...) : leaf<J>()...
  {
  }
};
template <class... T>
struct tup
{
  impl<typename make_seq<sizeof...(T)>::type> base;
  template <class... U>
  constexpr tup(U...)
    : base(typename make_seq<sizeof...(U)>::type(), make_seq<sizeof...(U)>())
  {
  }
};
template <class... T>
tup<T...> make(T... t)
{
  return tup<T...>(t...);
}
struct pair
{
  int n;
  template <class... A>
  pair(int, tup<>, tup<A...>) : n(sizeof...(A))
  {
  }
};
struct holder
{
  pair p;
  holder(int) : p(0, make(), make())
  {
  }
  holder() : p(0, make(), make(1))
  {
  }
};
int main()
{
  holder none(0);
  holder one;
  __CPROVER_assert(none.p.n == 0 && one.p.n == 1, "deduced per call");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
