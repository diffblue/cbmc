// N5008 [class.base.init]/6 (delegating constructors) + [temp.variadic]/5:
// std::pair's piecewise constructor is defined out-of-line in <tuple> as a
// DELEGATING constructor:
//
//   template<class _T1, class _T2>
//     template<typename... _Args1, typename... _Args2>
//     pair<_T1,_T2>::pair(piecewise_construct_t,
//                         tuple<_Args1...> __first, tuple<_Args2...> __second)
//     : pair(__first, __second,
//            typename _Build_index_tuple<sizeof...(_Args1)>::__type(),
//            typename _Build_index_tuple<sizeof...(_Args2)>::__type())
//     { }
//
// The delegation target is a member constructor template with FOUR
// parameter packs (_Args1, _Indexes1, _Args2, _Indexes2), two of them
// non-type index packs.  g++/clang++ run this to completion
// (runtime-verified).
//
// KNOWNBUG: resolving the delegation target inside the mem-initializer
// fails (deduction of the four zipped packs -- the two-pack machinery
// handles two type packs, not the mixed four-pack form), the swallowed
// error leaves the piecewise constructor's instance with an EMPTY body,
// and the constructed pair keeps garbage.  On std::map this is the
// remaining blocker of cpp20_map_basic: the first insert stores a garbage
// key, the read-back re-inserts, and unbounded unwinding diverges.
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

template <unsigned long... I>
struct index_tuple
{
};
template <unsigned long N>
struct build_index;
template <>
struct build_index<0>
{
  typedef index_tuple<> type;
};
template <>
struct build_index<1>
{
  typedef index_tuple<0> type;
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
  pair(pc_t, tuple<A1...>, tuple<A2...>); // defined out-of-line below

  template <
    typename... A1,
    unsigned long... I1,
    typename... A2,
    unsigned long... I2>
  pair(tuple<A1...> &t1, tuple<A2...> &, index_tuple<I1...>, index_tuple<I2...>)
    : first(t1.v), second(sizeof...(A1))
  {
  }
};

// out-of-line DELEGATING definition (the <tuple> shape)
template <typename T1, typename T2>
template <typename... A1, typename... A2>
pair<T1, T2>::pair(pc_t, tuple<A1...> t1, tuple<A2...> t2)
  : pair(
      t1,
      t2,
      typename build_index<sizeof...(A1)>::type(),
      typename build_index<sizeof...(A2)>::type())
{
}

int main()
{
  int x = 4;
  tuple<int &&> t1(static_cast<int &&>(x));
  tuple<> t2;
  pair<const int, int> p(pc_t{}, t1, t2);
  __CPROVER_assert(p.first == 4, "first through delegation");
  __CPROVER_assert(p.second == 1, "second through delegation");
  return 0;
}
