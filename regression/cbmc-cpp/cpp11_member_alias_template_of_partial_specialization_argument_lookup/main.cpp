extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct al
{
  typedef T value_type;
};
template <class A>
struct at;
// a partial specialization with a member alias template (libstdc++'s
// allocator_traits<allocator<_Tp>>::rebind_alloc)
template <class T>
struct at<al<T>>
{
  template <class U>
  using rebind_alloc = al<U>;
};
// [basic.lookup.unqual]/1, [temp.arg.general]: the template argument vt of
// `at<al<int>>::rebind_alloc<vt>' is looked up from its point of use, where
// it is the local typedef (path::generic_string's
// `rebind_alloc<value_type>')
int f()
{
  typedef char vt;
  at<al<int>>::rebind_alloc<vt> x;
  return sizeof(decltype(x)::value_type);
}
struct P
{
  typedef short value_type;
  template <class A>
  int g() const
  {
    using A2 = typename at<A>::template rebind_alloc<value_type>;
    return sizeof(typename A2::value_type);
  }
};
int main()
{
  __CPROVER_assert(f() == 1, "local typedef");
  P p;
  __CPROVER_assert(p.g<al<int>>() == sizeof(short), "member typedef");
  __CPROVER_assert(f() != 1, "WRONG (must FAIL)");
}
