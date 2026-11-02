// N5008 [temp.alias]/2, [temp.variadic]/14, [expr.prim.fold]/3: a fold over
// an alias template's pack is expanded in the alias's specialization.  The
// math functions of Xcode 26's libc++ return `__promote_t<_A1, _A2>', defined
// as below.
extern "C" void __CPROVER_assert(bool, const char *);

template <class T, class U>
struct is_same
{
  static const bool value = false;
};
template <class T>
struct is_same<T, T>
{
  static const bool value = true;
};
template <bool B, class T = void>
struct enable_if
{
};
template <class T>
struct enable_if<true, T>
{
  using type = T;
};
template <class T>
struct is_arithmetic
{
  static const bool value = true;
};

float promote_impl(float);
double promote_impl(int);
double promote_impl(double);

template <class... A>
using promote_t =
  decltype((typename enable_if<(is_arithmetic<A>::value && ...)>::type)0, (promote_impl(A()) + ...));
template <class... A>
using sum_t = decltype((A() + ... + 0));

template <class A, class B>
promote_t<A, B> add(A x, B y)
{
  return x + y;
}

int main()
{
  static_assert(is_same<promote_t<double, double>, double>::value, "dd");
  static_assert(is_same<promote_t<int, float>, double>::value, "if");
  static_assert(is_same<promote_t<float, float>, float>::value, "ff");
  static_assert(is_same<promote_t<int, int, int>, double>::value, "iii");
  static_assert(is_same<sum_t<char, short>, int>::value, "binary fold");
  __CPROVER_assert(add(1, 0.5f) == 1.5, "promoted result");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
