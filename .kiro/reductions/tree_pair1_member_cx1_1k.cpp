template <class> using __type_identity_t = int;
template <class, class> struct __allocator_traits_rebind;
template <template <class...> class _Alloc, class _Tp, class... _Args,
          class _Up>
struct __allocator_traits_rebind<_Alloc<_Tp, _Args...>, _Up> {
  using type = _Alloc<_Tp>::template rebind<_Up>;
};
template <class _Alloc, class _Tp>
using __allocator_traits_rebind_t =
    __allocator_traits_rebind<_Alloc, _Tp>::type;
template <class> struct allocator {
  template <class> struct rebind;
};
struct allocator_traits {
  template <class _Tp>
  using rebind_alloc = __allocator_traits_rebind_t<allocator<int>, _Tp>;
};
template <class _Traits, class _Tp>
using __rebind_alloc = _Traits::template rebind_alloc<_Tp>;
template <class> struct __compressed_pair {};
template <class> struct __tree {
  __compressed_pair<__rebind_alloc<allocator_traits, int>> __pair1_;
  __tree();
};
template <class _Allocator> __tree<_Allocator>::__tree() : __pair1_() {}
typedef __tree<__type_identity_t<int>>;
int main() {}
