// Clang's __is_trivially_equality_comparable(T): `a == b' on T is equivalent
// to comparing object representations.  libc++'s __constexpr_memchr (behind
// std::string_view::find) static_asserts it for char; the trait was unknown,
// so the function's body was dropped.
extern "C" void __CPROVER_assert(bool, const char *);

enum E
{
  e0
};
enum class F : char
{
  f0
};
struct S
{
  int x;
};

template <class T>
using remove_cv_t = __remove_cv(T);

template <class T, class U>
constexpr bool find_first(T *str, U value)
{
  static_assert(
    __is_trivially_equality_comparable(remove_cv_t<T>), "byte comparable");
  return *str == value;
}

#define CHECK(type, v)                                                         \
  __CPROVER_assert(__is_trivially_equality_comparable(type) == v, #type);

int main()
{
  CHECK(int, true)
  CHECK(bool, true)
  CHECK(const char, true)
  CHECK(volatile long, true)
  CHECK(int *, true)
  CHECK(void (*)(), true)
  CHECK(int S::*, true)
  CHECK(float, false)
  CHECK(double, false)
  CHECK(E, false)
  CHECK(F, false)
  CHECK(int[2], false)
  CHECK(int &, false)
  CHECK(void, false)
  CHECK(decltype(nullptr), false)
  CHECK(S, false)
  const char s[] = "x";
  __CPROVER_assert(find_first(s, 'x'), "function template body kept");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
