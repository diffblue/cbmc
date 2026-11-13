// Variable template partial specialization
template <int A, int B>
inline const int my_gcd = my_gcd<B, A % B>;

template <int A>
inline const int my_gcd<A, 0> = A;

template <int A, int B>
inline const int my_val = A + B;

template <int A>
inline const int my_val<A, 0> = A * 10;

static_assert(my_gcd<12, 8> == 4, "gcd(12,8)");
static_assert(my_gcd<7, 1> == 1, "gcd(7,1)");
static_assert(my_val<3, 0> == 30, "val(3,0)");
static_assert(my_val<2, 3> == 5, "val(2,3)");

int main()
{
  return 0;
}
