// cvise reduction (ASan/UBSan/valgrind-clean; interestingness also
// required all CBMC pointer checks green, so the failure is purely a
// VALUE loss) of cpp20_map_basic's remaining false positive.
//
// The essential ingredient is libstdc++'s piecewise pair construction
// (gcc-13 <tuple>/<bits/stl_pair.h> shapes): the delegating converting
// constructor pair(piecewise_construct_t, tuple<_Args1...>,
// tuple<_Args2...>) delegates to the _Index_tuple-tag constructor
// whose mem-initializer expands `first(get<_Indexes1>(__tuple1)...)`
// (N5008 [class.base.init], [temp.variadic]).  Under CBMC the value
// written through this chain is lost: the key read back from the node
// is 0 instead of 1, and the reference returned by operator[] points
// at storage offset 12 instead of offset 4 of pair<const int,int>.
// Replacing the piecewise construction with a direct pair(k, 0)
// construction makes the identical program verify.
//
// KNOWNBUG: the assertion must hold.  g++ verifies at runtime
// (clang++ lacks the GCC __integer_pack builtin used by the gcc
// libstdc++ shape this reproduces).
namespace std {
template <unsigned long, typename> struct tuple_element;
template <long __i, typename _Tp>
using __tuple_element_t = tuple_element<__i, _Tp>::type;
template <unsigned long...> struct _Index_tuple {};
template <int _Num> struct _Build_index_tuple {
  using __type = _Index_tuple<__integer_pack(_Num)...>;
};
template <long, typename...> struct _Nth_type;
template <typename _Tp0, typename... _Rest>
struct _Nth_type<0, _Tp0, _Rest...> {
  using type = _Tp0;
};
int piecewise_construct;
template <typename...> class tuple;
template <typename, typename _T2> struct pair {
  int first;
  _T2 second;
  template <typename... _Args1, typename... _Args2>
  pair(int, tuple<_Args1...> __first, tuple<_Args2...> __second)
      : pair(__first, __second,
             typename _Build_index_tuple<sizeof...(_Args1)>::__type(),
             typename _Build_index_tuple<sizeof...(_Args2)>::__type()) {}
  template <typename... _Args1, unsigned long... _Indexes1, typename... _Args2>
  pair(tuple<_Args1...> __tuple1, tuple<_Args2...>, _Index_tuple<_Indexes1...>,
       _Index_tuple<>)
      : first(get<_Indexes1>(__tuple1)...) {}
  pair(int, _T2 __y) : second(__y) {}
};
struct _Head_base {
  static int _M_head(_Head_base __b) { return __b._M_head_impl; }
  int _M_head_impl;
};
template <unsigned long, typename...> struct _Tuple_impl;
template <unsigned long _Idx, typename _Head>
struct _Tuple_impl<_Idx, _Head> : _Head_base {
  template <typename _UHead> _Tuple_impl(_UHead __head) : _Head_base(__head) {}
};
template <typename... _Elements> struct tuple : _Tuple_impl<0, _Elements...> {};
template <> struct tuple<> {};
template <unsigned long __i, typename... _Types>
struct tuple_element<__i, tuple<_Types...>> {
  using type = _Nth_type<__i, _Types...>::type;
};
template <unsigned long __i, typename _Head>
_Head __get_helper(_Tuple_impl<__i, _Head> &__t) {
  return _Tuple_impl<__i, _Head>::_M_head(__t);
}
template <int __i, typename... _Elements>
__tuple_element_t<__i, tuple<_Elements...>> get(tuple<_Elements...> __t) {
  return __get_helper(__t);
}
template <typename... _Elements>
tuple<_Elements...> forward_as_tuple(_Elements... __args) {
  return tuple<_Elements...>(__args...);
}
} // namespace std
void *operator new(unsigned long, void *__p) { return __p; }
namespace std {
template <typename _Tp, typename... _Args>
void construct_at(_Tp *__location, _Args... __args) {
  new (__location) _Tp(__args...);
}
template <typename _Tp> struct __new_allocator {
  _Tp *allocate(long) { return static_cast<_Tp *>(operator new(sizeof(_Tp))); }
};
template <typename> struct allocator_traits;
template <typename _Tp> struct allocator_traits<__new_allocator<_Tp>> {
  using allocator_type = __new_allocator<_Tp>;
  template <typename _Up> using rebind_alloc = __new_allocator<_Up>;
  static _Tp *allocate(allocator_type __a, long __n) {
    return __a.allocate(__n);
  }
  template <typename _Up, typename... _Args>
  static void construct(allocator_type, _Up __p, _Args... __args) {
    construct_at(__p, __args...);
  }
};
} // namespace std
template <typename _Alloc>
struct __alloc_traits : std::allocator_traits<_Alloc> {
  template <typename _Tp> struct rebind {
    typedef std::allocator_traits<_Alloc>::template rebind_alloc<_Tp> other;
  };
};
struct __aligned_membuf {
  char _M_storage[sizeof(std::pair<int, int>)];
};
namespace std {
struct _Rb_tree_node_base {
  typedef _Rb_tree_node_base *_Base_ptr;
  _Base_ptr _M_parent;
};
struct _Rb_tree_node : _Rb_tree_node_base {
  __aligned_membuf _M_storage;
  pair<const int, int> *_M_valptr() {
    void *__trans_tmp_16(&_M_storage);
    return static_cast<pair<const int, int> *>(__trans_tmp_16);
  }
};
typedef _Rb_tree_node_base::_Base_ptr _Base_ptr;
struct _Rb_tree_iterator {
  _Rb_tree_iterator(_Base_ptr __x) : _M_node(__x) {}
  pair<const int, int> &operator*() {
    return *static_cast<_Rb_tree_node *>(_M_node)->_M_valptr();
  }
  _Base_ptr _M_node;
};
typedef __alloc_traits<__new_allocator<pair<int, int>>>::rebind<
    _Rb_tree_node>::other _Node_allocator;
typedef __alloc_traits<_Node_allocator> _Alloc_traits;
struct _Rb_tree_const_iterator {
  _Rb_tree_const_iterator(_Rb_tree_iterator) {}
};
typedef _Rb_tree_node *_Link_type;
_Rb_tree_node_base _M_header;
_Rb_tree_iterator _M_lower_bound(_Link_type __x, _Base_ptr __y) {
  while (__x) {
    __y = __x;
    __x = 0;
  }
  return __y;
}
pair<_Base_ptr, _Base_ptr> _M_get_insert_unique_pos(int __k) {
  _Base_ptr __trans_tmp_13 = &_M_header;
  if (__k)
    return pair<_Base_ptr, _Base_ptr>(0, __trans_tmp_13);
  return pair<_Base_ptr, _Base_ptr>(0, 0);
}
template <typename... _Args> _Link_type _M_create_node(_Args... __args) {
  _Node_allocator __a;
  _Link_type __n = _Alloc_traits::allocate(__a, 1);
  pair<const int, int> *__vp = __n->_M_valptr();
  _Alloc_traits::construct(__a, __vp, __args...);
  return __n;
}
_Rb_tree_iterator end() { return &_M_header; }
_Rb_tree_iterator lower_bound() {
  return _M_lower_bound(static_cast<_Link_type>(_M_header._M_parent),
                        &_M_header);
}
struct {
  template <typename... _Args>
  auto _M_emplace_hint_unique(_Rb_tree_const_iterator,
                              _Args... __args) -> _Rb_tree_iterator {
    _Link_type __node = _M_create_node(__args...);
    _Rb_tree_node __x = *__node;
    pair<const int, int> __pk = *__x._M_valptr();
    auto __res = _M_get_insert_unique_pos(__pk.first);
    _Rb_tree_node_base &__header(_M_header);
    if (__res.second)
      __header._M_parent = __node;
    return __node;
  }
} _M_t;
struct map {
  int &operator[](int __k) {
    _Rb_tree_iterator __i = lower_bound();
    if (__i._M_node == end()._M_node) {
      tuple<int> __t1 = forward_as_tuple(__k);
      __i = _M_t._M_emplace_hint_unique(__i, piecewise_construct, __t1,
                                        tuple<>());
    }
    return (*__i).second;
  }
};
} // namespace std
int main() {
  std::map m;
  m[1] = 2;
  __CPROVER_assert(m[1], "value survives piecewise construction");
}
