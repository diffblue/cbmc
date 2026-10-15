extern "C" void __CPROVER_assert(bool, const char *);
struct Plain
{
  static constexpr bool simple = true;
};
struct Templ
{
  // a variable template: `A::simple' without template arguments is not a
  // valid expression for A = Templ
  template <typename T>
  static constexpr bool simple = __is_same(T, int);
};
// [temp.constr.op]/3: a disjunction is satisfied if either operand is; an
// operand whose substitution fails is not satisfied
// ([temp.constr.atomic]/3), so the second operand decides -- libstdc++ 16's
// views::__adaptor::__adaptor_has_simple_extra_args
template <typename A, typename... Args>
concept has_simple = A::simple || A::template simple<Args...>;
template <typename A>
concept missing_or_true = A::nonexistent || true;
int main()
{
  __CPROVER_assert(has_simple<Plain, int>, "first operand");
  __CPROVER_assert(has_simple<Templ, int>, "second operand");
  __CPROVER_assert(!has_simple<Templ, long>, "neither");
  __CPROVER_assert(missing_or_true<Plain>, "failed first operand");
  __CPROVER_assert(!has_simple<Templ, int>, "WRONG (must FAIL)");
}
