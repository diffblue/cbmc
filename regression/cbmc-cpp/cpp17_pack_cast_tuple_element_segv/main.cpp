// Header-free reproducer cvise-reduced from
// cpp17_abstract_environment_tu (CBMC dog-food TU): a functional cast
// to a dependent tuple_element-style member type with a two-element
// argument pack, `typename get_typet<I, ...>::type(ts...)`, SEGFAULTS
// the C++ front end during typechecking.  Same malformed-typecast
// family as cpp20_views_take_call_crash (there an invariant fires;
// here a raw segfault).  g++/clang++ accept and run clean.
extern "C" void __CPROVER_assert(bool, const char *);

template <unsigned long, typename> struct tuple_element;
template <long, typename...> struct _Nth_type;
template <typename _Tp0, typename _Tp1, typename... _Rest>
struct _Nth_type<1, _Tp0, _Tp1, _Rest...> {
  using type = _Tp1;
};
template <typename...> class tuple;
template <unsigned long __i, typename... _Types>
struct tuple_element<__i, tuple<_Types...>> {
  using type = typename _Nth_type<__i, _Types...>::type;
};
template <int I, typename... Ts> struct get_typet {
  typedef typename tuple_element<I, tuple<Ts...>>::type type;
};
struct d_leaft {
  template <class valueU> d_leaft(int, valueU v) : v() {}
  int v;
};
template <int I, typename... Ts> void make_shared_3(Ts... ts) {
  typename get_typet<I, int, d_leaft>::type(ts...);
}
int set_value___trans_tmp_1;
void set_value() { make_shared_3<1>(set_value___trans_tmp_1, 0); }

int main() {
  set_value();
  __CPROVER_assert(true, "functional cast to dependent tuple_element type");
  return 0;
}
