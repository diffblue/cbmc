// N5008 [namespace.udecl]/1, [class.inhctor.init]/1: a constructor
// template inherited by `using B::B' is a member of B, so its default
// template arguments are evaluated with B's template parameters bound
// ([temp.inst]/1); they were looked up with the derived class's.  libc++'s
// __bind_back_t inherits __perfect_forward_impl's constructor this way.
extern "C" void __CPROVER_assert(bool, const char *);
template <bool B, class T = void>
struct enable_if
{
};
template <class T>
struct enable_if<true, T>
{
  using type = T;
};
template <class... T>
struct count
{
  static constexpr int value = sizeof...(T);
};
template <class... B>
struct base
{
  int n;
  template <
    class... A,
    class =
      typename enable_if<count<B..., A...>::value == sizeof...(B) + 2>::type>
  base(A...) : n(sizeof...(B))
  {
  }
};
template <class X, class Y>
struct derived : base<X, Y>
{
  using base<X, Y>::base;
};
template <class... A>
using base_of = base<A...>;
struct three : base_of<int, char, long>
{
  using base_of<int, char, long>::base;
};

int main()
{
  derived<int, char> d(1, 2);
  three t(1, 2);
  __CPROVER_assert(d.n == 2, "inherited");
  __CPROVER_assert(t.n == 3, "inherited through an alias");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
