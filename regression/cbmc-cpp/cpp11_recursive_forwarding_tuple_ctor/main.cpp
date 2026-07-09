// N5008 [class.base.init] + [temp.variadic] + [temp.param]/11: a recursive
// variadic *forwarding* constructor whose member-initializer constructs its
// base class from the tail pack, with an enable_if trailing constraint that
// references both the constructor's own parameter pack and the enclosing
// class's parameter pack -- the shape of libstdc++'s std::_Tuple_impl:
//
//   template <int I, class Head, class... Tail>
//   struct TI<I, Head, Tail...> : TI<I + 1, Tail...>, HB<I, Head> {
//     typedef TI<I + 1, Tail...> Inh;
//     template <class UH, class... UT,
//               class = enable_if_t<sizeof...(UT) == sizeof...(Tail)>>
//     TI(UH&& h, UT&&... t) : Inh(fwd<UT>(t)...), Base(fwd<UH>(h)) {}
//   };
//
// This exercises a family of "a template parameter pack is not the last
// template parameter" ([temp.param]/11) cases that previously failed:
//   * the enable_if trailing parameter after the constructor's pack `UT`,
//   * `sizeof...(Tail)` (the enclosing CLASS pack) evaluated while checking the
//     trailing default of a recursively-instantiated constructor, and
//   * the terminal recursion step where the pack is EMPTY (the base-class
//     member-initializer `Inh(fwd<UT>(t)...)` with zero tail elements) --
// which together made `mk(...)` report "found no match for symbol 'Inh'".
//
// The three elements must be stored at their correct recursive positions.
// assertion "WRONG" must FAIL (non-vacuity).

extern "C" void __CPROVER_assert(int, const char *);

template <class T>
struct rr
{
  using type = T;
};
template <class T>
struct rr<T &>
{
  using type = T;
};
template <class T>
struct rr<T &&>
{
  using type = T;
};
template <class T>
T &&fwd(typename rr<T>::type &t)
{
  return static_cast<T &&>(t);
}
template <class T>
T &&fwd(typename rr<T>::type &&t)
{
  return static_cast<T &&>(t);
}

template <bool B, class T = void>
struct eif
{
};
template <class T>
struct eif<true, T>
{
  using type = T;
};

template <int I, class Head>
struct HB
{
  Head _M;
  HB() : _M()
  {
  }
  template <class U>
  HB(U &&h) : _M(fwd<U>(h))
  {
  }
};

template <int I, class... T>
struct TI;
template <int I>
struct TI<I>
{
  TI()
  {
  }
};
template <int I, class Head, class... Tail>
struct TI<I, Head, Tail...> : TI<I + 1, Tail...>, HB<I, Head>
{
  typedef TI<I + 1, Tail...> Inh;
  typedef HB<I, Head> Base;
  TI()
  {
  }
  template <
    class UH,
    class... UT,
    class = typename eif<(sizeof...(UT) == sizeof...(Tail))>::type>
  TI(UH &&h, UT &&...t) : Inh(fwd<UT>(t)...), Base(fwd<UH>(h))
  {
  }
};

template <class... T>
struct Tup : TI<0, T...>
{
  Tup()
  {
  }
  template <class... U>
  Tup(U &&...u) : TI<0, T...>(fwd<U>(u)...)
  {
  }
};

template <class... T>
Tup<T...> mk(T &&...t)
{
  return Tup<T...>(fwd<T>(t)...);
}

int main()
{
  auto t = mk(10, 20, 30);
  __CPROVER_assert(static_cast<HB<0, int> &>(t)._M == 10, "elem0 stored");
  __CPROVER_assert(static_cast<HB<1, int> &>(t)._M == 20, "elem1 stored");
  __CPROVER_assert(static_cast<HB<2, int> &>(t)._M == 30, "elem2 stored");
  __CPROVER_assert(static_cast<HB<0, int> &>(t)._M != 10, "WRONG must FAIL");
  return 0;
}
