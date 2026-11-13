template <long N>
struct abs_val
{
  static constexpr long value = N < 0 ? -N : N;
};

template <long N>
struct doubled
{
  static constexpr long value = 2 * abs_val<N>::value;
};

long x = doubled<-3>::value;

int main()
{
  return 0;
}
