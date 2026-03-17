template <long P, long Q>
struct gcd : gcd<Q, (P % Q)>
{
};

template <long P>
struct gcd<P, 0>
{
  static const long value = P;
};

// Just verify it compiles and the specialization is selected
long x = gcd<4, 0>::value;

int main()
{
  return 0;
}
