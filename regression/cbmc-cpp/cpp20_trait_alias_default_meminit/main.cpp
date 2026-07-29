// Root of the silent-statement-dropping family (gates
// cpp20_optional_base_alias_unknown, cpp20_ranges_basic_libcxx,
// cpp17_optional_requires_ctor_pair), header-free: when a class
// template's default argument computes a bool through an alias whose
// RHS is a clang builtin trait type (add_rref_t<T> =
// __add_rvalue_reference(T)), instantiating a class that names
// base<> through a member typedef and uses it as a mem-initializer-id
// fails ("symbol '__base' is unknown") and the enclosing conversion
// is dropped.  Without the alias in the default the same shape works.
// clang++/valgrind run clean (clang-only builtin; g++ n/a).

extern "C" void __CPROVER_assert(bool, const char *);
template <int v> struct integral_constant {
  static constexpr int value = v;
};
template <class T> using add_rref_t = __add_rvalue_reference(T);
template <bool = integral_constant<__is_trivially_constructible(
              add_rref_t<int>)>::value>
struct base {};
template <class T> struct opt : base<> {
  using __base = base<>;
  int x;
  opt() : __base(), x(1) {}
};
int main() {
  opt<int> o;
  __CPROVER_assert(o.x == 1, "member typedef mem-init survives");
  return 0;
}
