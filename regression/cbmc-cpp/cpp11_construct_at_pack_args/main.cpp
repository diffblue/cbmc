// N5008 [temp.variadic]/5 + [expr.new]: a pack expansion in a
// new-initializer's expression-list inside a FREE function template --
// `::new((void*)__location) _Tp(forward<_Args>(__args)...)`, the exact
// body of C++20 std::construct_at ([specialized.construct]) -- must
// replicate the pattern per pack element and select _Tp's constructor
// from the expanded arguments.
//
// KNOWNBUG: with TWO or more forwarded arguments constructing a
// class-template instance, the instantiated construct_at body fails to
// convert ("no body for callee construct_at") and the constructed
// object keeps its previous (or garbage) value.  One forwarded argument
// works; the member-function-template flavour of the same body
// (__new_allocator::construct) was fixed earlier and is covered by
// cpp11_pack_expansion_new_init.  This free-function flavour is the
// remaining front-end blocker of cpp20_map_basic: the C++20 headers
// route std::map's node construction through constexpr
// allocator_traits::construct -> std::construct_at, so the inserted
// pair's key is never written (the node keeps malloc garbage) and the
// unbounded read-back diverges walking a nondet-shaped tree.
//
// g++/clang++ runtime-verified (assertion holds).
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

// the C++20 std::construct_at body shape, minus constexpr and the
// decltype-SFINAE return type (neither is needed to reproduce)
template <typename _Tp, typename... _Args>
_Tp *construct_at(_Tp *__location, _Args &&...__args)
{
  return ::new((void *)__location) _Tp(forward<_Args>(__args)...);
}

template <typename T>
struct wrap
{
  T a;
  T b;
  wrap() : a(), b()
  {
  }
  wrap(T x, T y) : a(x), b(y)
  {
  }
};

int main()
{
  wrap<int> w;
  construct_at(&w, 4, 1);
  __CPROVER_assert(w.a == 4 && w.b == 1, "two forwarded args construct");
  return 0;
}
