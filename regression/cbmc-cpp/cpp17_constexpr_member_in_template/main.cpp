// Test that constexpr-eval of a template-class member function body
// with unqualified class-scope name references works.  Specifically,
// `gate<ic.get()>` requires evaluating `ic.get()` at compile time;
// the body of `get()` references the static `value` member without
// qualification, which must be resolved against `integral_constant`'s
// class scope, not against `main`'s scope.

template <typename _Tp, _Tp __v>
struct integral_constant
{
  static constexpr _Tp value = __v;
  using value_type = _Tp;
  constexpr value_type get() const { return value; }
};

template <bool B>
struct gate
{
  static constexpr bool value = B;
};

int main()
{
  constexpr integral_constant<bool, true> ic{};
  using G = gate<ic.get()>;
  __CPROVER_assert(G::value, "constexpr get() resolved in class scope");
  return 0;
}
