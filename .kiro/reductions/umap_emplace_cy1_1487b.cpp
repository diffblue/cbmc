template <int __v> struct integral_constant {
  static constexpr int value = __v;
};
template <bool __v> using __bool_constant = integral_constant<__v>;
template <typename> struct pair {
  template <typename _U1, typename _U2> pair(_U1, _U2) {}
};
template <int, int _Constant_iterators, int> struct _Hashtable_traits {
  using __constant_iterators = __bool_constant<_Constant_iterators>;
};
struct _Insert_base {
  using iterator = int;
};
template <typename, typename _Traits,
          bool = _Traits::__constant_iterators::value>
struct _Insert;
template <typename _Key, typename _Traits>
struct _Insert<_Key, _Traits> : _Insert_base {};
template <typename, typename> using __cache_default = __bool_constant<!bool()>;
template <typename>
struct _Hashtable : _Insert<int, _Hashtable_traits<1, 0, 1>> {
  long _M_element_count;
  long size() { return _M_element_count; }
  auto _M_emplace() -> pair<iterator> {
    int __trans_tmp_3;
    ++_M_element_count;
    return {__trans_tmp_3, true};
  }
  void emplace() { _M_emplace(); }
};
template <bool _Cache>
using __umap_traits = _Hashtable_traits<_Cache, false, true>;
template <typename _Key, typename _Hash,
          typename _Tr = __umap_traits<__cache_default<_Key, _Hash>::value>>
using __umap_hashtable = _Hashtable<_Tr>;
__umap_hashtable<int, int> _M_h;
long main___trans_tmp_2;
int main() {
  _M_h.emplace();
  main___trans_tmp_2 = _M_h.size();
  __CPROVER_assert(main___trans_tmp_2, "emplace with mixed value categories");
}
