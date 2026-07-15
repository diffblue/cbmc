// N5008 [temp.inst]/5 + [expr.const]: eager instantiation of a constexpr
// function specialization is required only when it must yield a CONSTANT
// now.  A void-returning constexpr function never produces such a value,
// so it must be deferred like a non-constexpr member -- not eagerly
// converted nested in the referencing body's degraded context, before the
// deferred body pack-expander runs.
//
// This is the C++20 allocator_traits::construct shape: a void constexpr
// member function template forwarding a pack into std::construct_at.  Was
// KNOWNBUG: forcing it eager resolved the still-packed construct_at call
// and dropped the wrapper's body (so the constructed object kept garbage);
// deferring lets prepare_deferred_method_body expand the new-initializer
// pack first.
extern "C" void __CPROVER_assert(int, const char *);

template <typename T>
struct remove_reference
{
  typedef T type;
};
template <typename T>
struct remove_reference<T &>
{
  typedef T type;
};
template <typename T>
struct remove_reference<T &&>
{
  typedef T type;
};
template <typename _Tp>
constexpr _Tp &&forward(typename remove_reference<_Tp>::type &__t) noexcept
{
  return static_cast<_Tp &&>(__t);
}
template <typename _Tp>
constexpr _Tp &&forward(typename remove_reference<_Tp>::type &&__t) noexcept
{
  return static_cast<_Tp &&>(__t);
}

void *operator new(unsigned long, void *p)
{
  return p;
}

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

// plain-return construct_at (the decltype-SFINAE-return flavour is a
// separate KNOWNBUG: cpp11_construct_at_decltype_return)
template <typename _Tp, typename... _Args>
_Tp *construct_at(_Tp *__location, _Args &&...__args)
{
  return ::new((void *)__location) _Tp(forward<_Args>(__args)...);
}

// the allocator_traits shape: a VOID CONSTEXPR member function template
struct wrapper
{
  template <typename _Up, typename... _Args>
  static constexpr void cw(_Up *__p, _Args &&...__args)
  {
    construct_at(__p, forward<_Args>(__args)...);
  }
};

int main()
{
  pair<const int, int> p;
  int x = 4;
  tuple<int &&> t1(static_cast<int &&>(x));
  tuple<> t2;
  wrapper::cw(&p, pc_t{}, t1, t2);
  __CPROVER_assert(
    p.first == 4 && p.second == 1, "void constexpr wrapper deferred");
  return 0;
}
