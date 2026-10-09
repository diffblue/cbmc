// N5008 [temp.variadic]/5: a pack expansion may appear in the
// expression-list of a new-initializer --
// `::new((void*)__p) _Up(forward<_Args>(__args)...)` -- the
// __new_allocator::construct shape behind every node-based standard
// container.  Also [temp.inst]/2: instantiating a class template does not
// instantiate its member templates; the member template's body (with its
// own pack expansions) must survive the class instantiation intact.
//
// Was KNOWNBUG (three defects, all needed for this test):
// * the parser dropped the `...` in a new-initializer's expression-list
//   (rAllocateInitializer had a literal TODO), so the pattern could never
//   be expanded;
// * template_mapt::expand_call_argument_packs recursed into nested member
//   TEMPLATE declarations while instantiating the enclosing class,
//   expanding (and consuming) their pack expansions against the class
//   instantiation's unrelated pack sizes;
// * the deduction convertibility pre-filter mispaired the implicit object
//   argument (see cpp11_member_template_object_arg).
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

// __new_allocator-like class template with the member construct template
template <typename _Tp>
struct new_allocator
{
  template <typename _Up, typename... _Args>
  void construct(_Up *__p, _Args &&...__args)
  {
    ::new((void *)__p) _Up(forward<_Args>(__args)...);
  }
};

template <typename _Tp>
struct allocator : public new_allocator<_Tp>
{
};

struct node
{
  int c;
  pair<const int, int> val;
};

// allocator_traits-like static dispatcher
template <typename _Alloc>
struct alloc_traits
{
  template <typename _Up, typename... _Args>
  static void construct(_Alloc &__a, _Up *__p, _Args &&...__args)
  {
    __a.construct(__p, forward<_Args>(__args)...);
  }
};

int main()
{
  allocator<node> a;
  node n;
  int x = 4;
  tuple<int &&> t1(static_cast<int &&>(x));
  tuple<> t2;
  alloc_traits<allocator<node>>::construct(a, &n.val, pc_t{}, t1, t2);
  __CPROVER_assert(n.val.first == 4, "first from forwarded tuple");
  __CPROVER_assert(n.val.second == 1, "second from pack arity");
  return 0;
}
