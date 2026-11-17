// N5008 [class.base.init]/7: a mem-initializer naming a POD base class with an
// expression-list copy-initializes the base subobject.  In a constructor
// TEMPLATE (whose body is type-checked directly, not through the class's
// member-initialization normalisation) the resolver's synthesized POD
// "constructor" reached the base-constructor-call lowering and aborted the
// front end (to_pointer_type precondition) -- libstdc++'s
// `_Hashtable_ebo_helper(_OtherTp &&tp) : _Tp(std::forward<_OtherTp>(tp))'
// once is_empty selected the empty-base-optimisation specialization.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct remove_reference
{
  typedef T type;
};
template <class T>
struct remove_reference<T &>
{
  typedef T type;
};
template <class T>
struct remove_reference<T &&>
{
  typedef T type;
};
template <class T>
constexpr T &&forward(typename remove_reference<T>::type &t) noexcept
{
  return static_cast<T &&>(t);
}
struct Hash
{
  unsigned k;
  unsigned operator()(unsigned x) const
  {
    return x + k;
  }
};
template <class T>
struct D3 : T
{
  template <class O>
  D3(O &&h) : T(forward<O>(h))
  {
  }
};
template <int N, class T, bool E = __is_empty(T)>
struct ebo;
template <int N, class T>
struct ebo<N, T, true> : private T
{
  ebo() noexcept(noexcept(T())) : T()
  {
  }
  template <class O>
  ebo(O &&tp) : T(forward<O>(tp))
  {
  }
  const T &cget() const
  {
    return static_cast<const T &>(*this);
  }
};
struct Empty
{
  unsigned operator()(unsigned x) const
  {
    return x + 1;
  }
};
struct Table : ebo<1, Empty>
{
  Table() = default;
  Table(const ::Empty &h) : ebo<1, ::Empty>(h)
  {
  }
  unsigned apply(unsigned x) const
  {
    return this->cget()(x);
  }
};
int main()
{
  Hash h{5};
  D3<Hash> d3(h);
  __CPROVER_assert(d3(1) == 6, "POD base from a forwarding constructor");
  Table t;
  __CPROVER_assert(t.apply(1) == 2, "empty base, default");
  Empty e;
  Table t2(e);
  __CPROVER_assert(t2.apply(2) == 3, "empty base, forwarding constructor");
  __CPROVER_assert(d3(1) == 7, "WRONG (must FAIL)");
}
