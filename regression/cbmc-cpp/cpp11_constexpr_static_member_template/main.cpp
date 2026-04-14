// Static constexpr member initializers that reference template
// metafunctions with non-type template parameters fail: the
// template parameter is not substituted during instantiation
// when the member is declared constexpr (works with plain const).
template <long long X>
struct Abs { static const long long value = (X < 0 ? -X : X); };

template <long long N>
struct S {
  static constexpr long long v = Abs<N>::value;
};

int main()
{
  __CPROVER_assert(S<1>::v == 1, "constexpr static member");
}
