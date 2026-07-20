extern "C" void __CPROVER_assert(bool, const char *);

// Reduced (cvise, clang-gated, 23 lines) from dog-fooding
// src/goto-programs/remove_const_function_pointers.cpp -- the shape of
// libstdc++'s unordered_set: the member insert's return type names an
// alias template (__uset_hashtable) whose DEFAULT argument evaluates
// __cache_default<...>::value, a static inherited through a decltype
// base chain (__not_ : __bool_constant<__and_<>::value>, __and_ :
// decltype(integral_constant<false> object)).  CBMC fails to evaluate
// the default, the member's type does not form, and the call resolves
// against only the free std::insert template: "found no match for
// symbol 'insert'".  BOTH the std namespace and the free insert are
// load-bearing (removing either makes it pass), pointing at the
// std-scope resolution/leniency paths.
// g++/clang++ accept (-std=c++17, no warnings) and verify at runtime.

namespace std {
template <int __v> struct integral_constant {
  static constexpr int value = __v;
};
template <bool __v> using __bool_constant = integral_constant<__v>;
integral_constant<false> __trans_tmp_1;
template <typename...> struct __and_ : decltype(__trans_tmp_1) {};
template <typename> struct __not_ : __bool_constant<__and_<>::value> {};
template <typename T1> struct pair {
  T1 first;
};
template <typename, typename> using __cache_default = __not_<int>;
template <bool> using __uset_traits = int;
template <typename _Value, typename _Hash,
          typename = __uset_traits<__cache_default<_Value, _Hash>::value>>
using __uset_hashtable = int;
template <typename> void insert();
struct unordered_set {
  pair<__uset_hashtable<int, int>> insert()
  {
    return {42};
  }
};
} // namespace std

int main() {
  std::unordered_set resolved_functions;
  std::pair<int> r = resolved_functions.insert();
  __CPROVER_assert(r.first == 42, "member insert resolved");
  return 0;
}
