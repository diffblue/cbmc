// N5008 [temp.deduct.type]/8: a deduced template-template-parameter
// binding (the argument INSTANCE) substituted textually into a
// qualified name makes the scope walk see the instance's TAG as a
// "template name" (`tag-allocator<int>` with new arguments).  The
// libc++ __allocator_traits_rebind chain through allocator_traits'
// member alias rebind_alloc; previously "template scope
// 'tag-allocator<signed_int>' not found" dropped std::set's
// __node_allocator typedef.  Strictified from the cx3 cvise harvest
// (907 bytes, g++-baseline-gated).
extern "C" void __CPROVER_assert(bool, const char *);
template <class, class> struct __allocator_traits_rebind;
template <template <class...> class _Alloc, class _Tp, class... _Args,
          class _Up>
struct __allocator_traits_rebind<_Alloc<_Tp, _Args...>, _Up> {
  using type = typename _Alloc<_Tp>::template rebind<_Up>;
};
template <class _Alloc, class _Tp>
using __allocator_traits_rebind_t =
    typename __allocator_traits_rebind<_Alloc, _Tp>::type;
template <class _Alloc> struct allocator_traits {
  template <class _Tp>
  using rebind_alloc = __allocator_traits_rebind_t<_Alloc, _Tp>;
};
template <class _Traits, class _Tp>
using __rebind_alloc = typename _Traits::template rebind_alloc<_Tp>;
template <class> struct allocator {
  template <class> struct rebind;
};
template <class> struct __tree
{
  typedef __rebind_alloc<allocator_traits<allocator<int>>, int>
    __node_allocator;
  allocator_traits<__node_allocator> __node_traits;
  int ok;
};
__tree<int> __base;
int main()
{
  __base.ok = 1;
  __CPROVER_assert(__base.ok == 1, "chain converts");
  return 0;
}
