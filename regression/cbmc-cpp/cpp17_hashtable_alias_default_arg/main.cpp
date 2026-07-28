// Header-free mimic of libstdc++ unordered_map (cvise-reduced from
// cpp17_umap_emplace_mixed_categories, valgrind-gated to exclude UB).
// The hashtable is reached through an alias template whose default
// argument computes a bool NTTP (__cache_default<...>::value); the
// emplace() increment on the instance never lands: b.size() stays
// unconstrained and the assertion wrongly fails.  g++/clang++ run
// clean (assert holds at runtime).
extern "C" void __CPROVER_assert(bool, const char *);

template <int __v> struct integral_constant {
  static constexpr int value = __v;
};
template <bool __v> using __bool_constant = integral_constant<__v>;
struct pair {
  pair() {}
};
template <typename, typename> using __cache_default = __bool_constant<!bool()>;
template <typename> struct _Hashtable {
  long _M_element_count = 0;
  long size() { return _M_element_count; }
  pair __trans_tmp_3;
  void emplace() { ++_M_element_count; }
};
template <bool> using __umap_traits = int;
template <typename _Key, typename _Hash,
          typename _Tr = __umap_traits<__cache_default<_Key, _Hash>::value>>
using __umap_hashtable = _Hashtable<_Tr>;
struct unordered_map {
  __umap_hashtable<int, int> _M_h;
  long size() { return _M_h.size(); }
  void emplace() { _M_h.emplace(); }
};
int main() {
  unordered_map b;
  b.emplace();
  __CPROVER_assert(b.size(), "emplace with mixed value categories");
}
