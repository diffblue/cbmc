// Regression for [temp.var] variable templates whose initializer body
// fails to typecheck due to unmodeled libstdc++ helpers.
//
// Mirrors the libstdc++ pattern that triggered dog-food failures:
//
//   namespace std {
//     // class template with chained __and_ / __is_destructible_safe
//     // bases that CBMC's typechecker can't always evaluate.
//     template<typename T>
//       struct is_trivially_destructible : ... { };
//
//     // variable template body uses ::value of the class template.
//     template<typename T>
//       inline constexpr bool is_trivially_destructible_v =
//         is_trivially_destructible<T>::value;
//   }
//
// When the body's type-check throws (CBMC's modelling of
// `__is_destructible_safe<T>` doesn't fully evaluate for non-trivial
// class types like `basic_string`), `convert_initializer` used to
// leave `symbol.value` as the partially-converted cpp_name.  The
// next time the variable template was used, its `is_macro` flag (from
// `inline constexpr`) caused the use site to copy `symbol.value`
// directly into the resolved expression, surfacing as
//   `invalid implicit conversion from '<<type:>>' to 'bool'`
// at any subsequent `implicit_typecast(_, bool)` site.
//
// The fix nils `symbol.value` when type-checking throws, so the use
// site falls back to a typed `symbol_exprt` and the conversion-to-bool
// becomes a no-op.

template <typename T>
struct unmodelled_helper
{
  // Body that depends on T in a way CBMC's typechecker can't evaluate
  // for some types (uses a builtin that's only modelled for scalars).
  static constexpr bool value = __is_trivially_destructible(T);
};

template <typename T>
inline constexpr bool helper_v = unmodelled_helper<T>::value;

// Use the variable template as a default arg of a non-type bool
// template parameter.
template <typename T, bool /*Has*/ = helper_v<T>>
struct payload
{
  T x;
};

struct trivial { int x; };
struct nontrivial
{
  int *p;
  ~nontrivial() { delete p; }
  nontrivial() : p(nullptr) {}
};

int main()
{
  payload<trivial> p1;
  payload<nontrivial> p2;
  (void)p1;
  (void)p2;
  return 0;
}
