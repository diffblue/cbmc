// Header-free isolation of cpp17_tuple_basic's 3-element failure
// (std::make_tuple(1, 2.0, 3.0f) then std::get<0> reads the wrong value),
// obtained by cvise-reducing the preprocessed std::tuple case and repairing the
// reduction into standard-conforming C++ -- both g++ and clang++ accept it and
// run it with get<0> == 1.
//
// N5008 [temp.deduct]/8 + [temp.variadic]/4-5: this mirrors libstdc++ std::tuple.
// A `tuple<_Elements...> : _Tuple_impl<0, _Elements...>` has a variadic
// converting constructor guarded by a defaulted SFINAE template parameter whose
// condition is a TWO-parallel-pack fold over the class pack `_Elements` and the
// constructor's own pack `_UElements`
// (`_TupleConstraints<_Elements...>::ic<_UElements...>()` ==
// `and_<is_ctible<_Elements, _UElements>::value...>::value`, exactly libstdc++'s
// `_TupleConstraints<_Types...>::__is_implicitly_constructible<_UTypes...>()`).
// `get<I>` uses the (fixed) derived-to-base deduction of the `_Tuple_impl<I,...>`
// base.
//
// KNOWNBUG: for THREE elements CBMC fails to evaluate the two-parallel-pack
// constraint in the constructor's SFINAE default template argument, reports
// "found no match for symbol 'tuple'" when make_tuple constructs the result, so
// the tuple is left unconstructed and get<0> reads a nondeterministic value; the
// assertion get<0> == 1 then fails.  TWO elements are handled correctly.  A
// hand-written tuple WITHOUT the two-parallel-pack SFINAE constructor (a plain
// variadic constructor) is handled correctly by CBMC, so the residual is
// specifically the two-parallel-pack constexpr constraint in a variadic
// constructor's SFINAE default template argument at >= 3 elements.
//
// Flip to CORE once such a constraint is evaluated at >= 3 elements so the
// constructor resolves and get<0> reads the constructed value.

extern "C" void __CPROVER_assert(int, const char *);

template <bool, class T>
struct enable_if_
{
};
template <class T>
struct enable_if_<true, T>
{
  using type = T;
};
template <bool B, class T = bool>
using enable_if_t_ = typename enable_if_<B, T>::type;

template <class, class>
struct is_ctible
{
  static constexpr bool value = true;
};

template <bool...>
struct and_;
template <>
struct and_<>
{
  static constexpr bool value = true;
};
template <bool H, bool... T>
struct and_<H, T...>
{
  static constexpr bool value = H && and_<T...>::value;
};

template <unsigned long, typename _Head>
struct _Head_base
{
  _Head _M_head_impl;
  template <typename _UHead>
  _Head_base(_UHead __h) : _M_head_impl(__h)
  {
  }
};
template <unsigned long, typename...>
struct _Tuple_impl;
template <unsigned long _Idx, typename _Head, typename... _Tail>
struct _Tuple_impl<_Idx, _Head, _Tail...> : _Tuple_impl<_Idx + 1, _Tail...>,
                                            _Head_base<_Idx, _Head>
{
  template <typename _UHead, typename... _UTail>
  _Tuple_impl(_UHead __h, _UTail... __t)
    : _Tuple_impl<_Idx + 1, _Tail...>(__t...), _Head_base<_Idx, _Head>(__h)
  {
  }
};
template <unsigned long _Idx, typename _Head>
struct _Tuple_impl<_Idx, _Head> : _Head_base<_Idx, _Head>
{
  template <typename _UHead>
  _Tuple_impl(_UHead __h) : _Head_base<_Idx, _Head>(__h)
  {
  }
};

template <typename... _Elements>
struct _TupleConstraints
{
  template <typename... _UElements>
  static constexpr bool ic()
  {
    return and_<is_ctible<_Elements, _UElements>::value...>::value;
  }
};

template <typename... _Elements>
struct tuple : _Tuple_impl<0, _Elements...>
{
  template <
    typename... _UElements,
    enable_if_t_<_TupleConstraints<_Elements...>::template ic<_UElements...>()> =
      true>
  tuple(_UElements... __e) : _Tuple_impl<0, _Elements...>(__e...)
  {
  }
};

template <unsigned long __i, typename _Head, typename... _Tail>
_Head __get_helper(_Tuple_impl<__i, _Head, _Tail...> &__t)
{
  return static_cast<_Head_base<__i, _Head> &>(__t)._M_head_impl;
}
template <int __i, typename... _E>
auto get(tuple<_E...> &__t)
{
  return __get_helper<__i>(__t);
}
template <typename... _E>
tuple<_E...> make_tuple(_E... __a)
{
  return tuple<_E...>(__a...);
}

int main()
{
  auto t = make_tuple(1, 2.0, 3.0f);
  __CPROVER_assert(get<0>(t) == 1, "g0");
  return 0;
}
