// Named concept declarations and usage

template<class T>
concept Integral = __is_integral(T);

template<class T>
concept SignedIntegral = Integral<T> && __is_signed(T);

template<Integral T>
T increment(T x) { return x + 1; }

// Concept used in requires clause
template<class T>
  requires SignedIntegral<T>
T negate(T x) { return -x; }

int main()
{
  __CPROVER_assert(increment(41) == 42, "increment");
  __CPROVER_assert(negate(42) == -42, "negate");
}
