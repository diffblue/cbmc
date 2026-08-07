// N5008 [temp.deduct.type]/8: a deduced template-template-parameter
// used as a qualified-name SCOPE with arguments
// (`_Alloc<_Tp, _Args...>::template rebind<_Up>`, libc++
// __allocator_traits_rebind's partial-specialization body) names the
// TEMPLATE the bound instance was created from.  The scope walk
// previously failed to resolve the component and dropped the
// dependent typedef (std::set's __node_allocator chain).
extern "C" void __CPROVER_assert(bool, const char *);
template <class _Tp, class _Up, bool = true> struct R
{
};
template <template <class, class...> class _Alloc, class _Tp, class... _Args,
          class _Up>
struct R<_Alloc<_Tp, _Args...>, _Up, true>
{
  typedef typename _Alloc<_Tp, _Args...>::template rebind<_Up> type;
};
template <class T> struct allocator
{
  T v;
  template <class U> struct rebind
  {
    typedef allocator<U> other;
  };
};
template <class T> struct node
{
  T value;
};
typedef R<allocator<int>, node<char>>::type RB;
typedef RB::other NA;
NA na;
int main()
{
  __CPROVER_assert(sizeof(na.v.value) == 1, "rebound");
  return 0;
}
