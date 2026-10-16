// N5008 [expr.prim.fold]/2, [temp.variadic]/5, [expr.type.conv]/2: in a fold
// over a type pack, the pattern `Args()' value-initializes a prvalue of
// each element type (libc++ 19's __promote, behind std::copysign and
// std::hermite in <cmath>)
extern "C" void __CPROVER_assert(bool, const char *);
template <class T, class U>
struct same
{
  static constexpr bool value = false;
};
template <class T>
struct same<T, T>
{
  static constexpr bool value = true;
};
template <class... Args>
class promote
{
  static float test(float);
  static double test(int);
  static double test(double);
  static long double test(long double);

public:
  using type = decltype((test(Args()) + ...));
};
template <class... Args>
struct sum
{
  using type = decltype((Args() + ...));
};
static_assert(same<promote<double, double>::type, double>::value, "");
static_assert(same<promote<float, int>::type, double>::value, "");
static_assert(same<promote<float>::type, float>::value, "");
static_assert(same<sum<char, char>::type, int>::value, "");
static_assert(same<sum<float, double>::type, double>::value, "");
template <class A, class B>
typename promote<A, B>::type copy_sign(A x, B y)
{
  return __builtin_copysign(x, y);
}
float copy_sign(float, float)
{
  return 1;
}
int main()
{
  __CPROVER_assert(copy_sign(3.0, -1.0) == -3.0, "the template is selected");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
