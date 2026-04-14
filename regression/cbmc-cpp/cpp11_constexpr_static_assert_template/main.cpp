// Constexpr static member initializers referencing template
// metafunctions fail to evaluate as compile-time constants
// in static_assert. The template parameter substitution works
// (Abs<N> becomes Abs<1>) but the resulting Abs<1>::value
// expression is not evaluated to a constant during type-checking.
template<long long X>
struct Abs
{
  static const long long value = (X < 0 ? -X : X);
};

template<long long N>
struct S
{
  static constexpr long long v = Abs<N>::value;
};

static_assert(S<1>::v == 1, "constexpr static member in static_assert");
int main()
{
}
