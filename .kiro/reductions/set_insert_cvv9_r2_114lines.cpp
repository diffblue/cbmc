template <class> struct pointer_traits;
template <class _Tp> struct pointer_traits<_Tp *> {
  typedef _Tp element_type;
  template <class _Up> using rebind = _Up *;
};
template <class _From, class _To>
using __rebind_pointer_t = pointer_traits<_From>::template rebind<_To>;
template <class... _Args> void *__libcpp_operator_new(_Args... __args) {
  return __builtin_operator_new(__args...);
}
long __libcpp_allocate___size;
struct less {
  void operator()(int &__x, int) { __x; }
};
template <class _Alloc, class _RawAlloc = _Alloc> struct __pointer {
  using type = _RawAlloc::pointer;
};
template <class _Alloc> struct __size_type {
  using type = _Alloc::size_type;
};
template <class, class> struct __tree_node {
  int __value_;
};
template <class _Tp> struct __allocator_traits_rebind {
  using type = _Tp::template rebind<__tree_node<int, void *>>::other;
};
template <class _Alloc, class>
using __allocator_traits_rebind_t = __allocator_traits_rebind<_Alloc>::type;
template <class _Alloc> struct allocator_traits {
  using allocator_type = _Alloc;
  using pointer = __pointer<allocator_type>::type;
  template <class _Tp>
  using rebind_alloc = __allocator_traits_rebind_t<allocator_type, _Tp>;
  static pointer allocate() {
    typename __size_type<allocator_type>::type __n;
    allocator_type __a;
    return __a.allocate(__n);
  }
};
template <class _Traits, class _Tp>
using __rebind_alloc = _Traits::template rebind_alloc<_Tp>;
template <class _Tp> struct allocator {
  typedef long size_type;
  _Tp *allocate(long) {
    void *__trans_tmp_5 = __libcpp_operator_new(__libcpp_allocate___size);
    return static_cast<_Tp *>(__trans_tmp_5);
  }
  typedef _Tp *pointer;
  template <class _Up> struct rebind {
    typedef allocator<_Up> other;
  };
};
template <class _Tp> struct __compressed_pair_elem {
  using const_reference = _Tp;
  template <class _Up> __compressed_pair_elem(_Up __u) : __value_(__u) {}
  _Tp __value_;
};
template <class _T2>
struct __compressed_pair : __compressed_pair_elem<__tree_node<int, void *> *>,
                           __compressed_pair_elem<_T2> {
  template <class _U1, class _U2>
  __compressed_pair(_U1 __t1, _U2 __t2)
      : __compressed_pair_elem(__t1), __compressed_pair_elem<_T2>(__t2) {}
  __compressed_pair_elem<__tree_node<int, void *> *>::const_reference first() {
    return __value_;
  }
};
struct __tree_node_destructor {
  typedef allocator_traits<allocator<__tree_node<int, void *>>>::pointer
      pointer;
  __tree_node_destructor(allocator<__tree_node<int, void *>>) {}
};
typedef __pointer<__tree_node_destructor>::type pointer;
template <bool> using _GoodRValRefType = __tree_node_destructor;
struct unique_ptr {
  __compressed_pair<__tree_node_destructor> __ptr_;
  template <bool _Dummy = true>
  unique_ptr(pointer __p, _GoodRValRefType<_Dummy> __d) : __ptr_(__p, __d) {}
  pointer get() { return __ptr_.first(); }
};
void *__left_;
template <class _NodePtr, class = pointer_traits<_NodePtr>::element_type>
struct __tree_node_types;
template <class _NodePtr, class _Tp, class _VoidPtr>
struct __tree_node_types<_NodePtr, __tree_node<_Tp, _VoidPtr>> {
  typedef _NodePtr __node_pointer;
};
unique_ptr __construct_node() {
  __rebind_alloc<
      allocator_traits<allocator<int>>,
      __tree_node_types<__rebind_pointer_t<void *, __tree_node<int, void>>>>
      __na;
  unique_ptr __h(
      allocator_traits<
          __rebind_alloc<allocator_traits<allocator<int>>,
                         __tree_node_types<__rebind_pointer_t<
                             void *, __tree_node<int, void>>>>>::allocate(),
      __na);
  return __h;
}
unique_ptr __insert_unique___h = __construct_node();
__tree_node<int, void *> *__insert_unique___trans_tmp_2 =
    __insert_unique___h.get();
int count___k;
int main() {
  __left_ = __insert_unique___trans_tmp_2;
  less __trans_tmp_4;
  __trans_tmp_4(
      static_cast<__tree_node_types<
          __rebind_pointer_t<void *, __tree_node<int, void>>>::__node_pointer>(
          __left_)
          ->__value_,
      count___k);
}
