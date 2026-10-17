// N5008 [class.base.init]/9, /13: a constructor initializes the bases and
// members its mem-initializer-list does not name -- also each
// specialization of a constructor template -- and installs the virtual
// pointers
extern "C" void __CPROVER_assert(bool, const char *);
struct leaf
{
  int value;
  leaf() : value(7)
  {
  }
};
struct impl : leaf
{
  template <class U>
  impl(U)
  {
  }
  impl() = default;
};
struct B
{
  virtual int f() const
  {
    return 1;
  }
};
struct D : B
{
  int k = 5;
  template <class U>
  D(U)
  {
  }
  int f() const override
  {
    return 2;
  }
};
// libc++'s __tuple_impl: pack-expanded base initializers, the others
// value-initialized
template <int I, class T>
struct element
{
  T value;
  element() : value()
  {
  }
  template <class V>
  explicit element(V v) : value(v)
  {
  }
};
template <int... I>
struct idx
{
};
template <class... T>
struct types
{
};
template <class...>
struct tuple_impl;
template <int... I, class... T>
struct tuple_impl<idx<I...>, T...> : element<I, T>...
{
  template <int... U, class... TU, int... L, class... TL, class... A>
  tuple_impl(idx<U...>, types<TU...>, idx<L...>, types<TL...>, A... a)
    : element<U, TU>(a)..., element<L, TL>()...
  {
  }
};
int main()
{
  impl d;
  __CPROVER_assert(d.value == 7, "non-template constructor");
  impl t(1);
  __CPROVER_assert(t.value == 7, "constructor template");
  D v(1);
  const B &b = v;
  __CPROVER_assert(b.f() == 2 && v.k == 5, "vtable pointer and NSDMI");
  tuple_impl<idx<0, 1>, int, long> e(
    idx<0, 1>(), types<int, long>(), idx<>(), types<>(), 3, 4L);
  __CPROVER_assert(
    static_cast<element<1, long> &>(e).value == 4, "pack-expanded bases");
  tuple_impl<idx<0, 1>, int, long> f(
    idx<0>(), types<int>(), idx<1>(), types<long>(), 3);
  __CPROVER_assert(
    static_cast<element<0, int> &>(f).value == 3 &&
      static_cast<element<1, long> &>(f).value == 0,
    "value-initialized base");
  __CPROVER_assert(t.value == 8, "WRONG (must FAIL)");
}
