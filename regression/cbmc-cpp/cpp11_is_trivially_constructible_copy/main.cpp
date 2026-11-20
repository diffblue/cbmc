// N5008 [meta.unary.prop]: is_trivially_constructible<T, Args...> holds when
// the variable definition `T t(declval<Args>()...)' is well-formed and calls
// no non-trivial operation.  For the copy/move case ([class.copy.ctor]/11)
// that is a class with no user-provided copy/move constructor whose bases and
// members are trivially copyable.  __is_trivially_constructible(T, U) was an
// unconditional TRUE, so `struct NT { NT(const NT &); }' counted as trivially
// copy constructible -- libc++'s variant computed a trivial copy for a
// variant holding such a type.
extern "C" void __CPROVER_assert(bool, const char *);
#include <type_traits>

struct T
{
  int a;
  double b;
};
struct NT
{
  NT(const NT &);
};
struct Wrap
{
  NT n;
};
struct Conv
{
  Conv(int);
};

static_assert(std::is_trivially_copy_constructible<int>::value, "int");
static_assert(std::is_trivially_copy_constructible<T>::value, "T");
static_assert(std::is_trivially_move_constructible<T>::value, "T move");
static_assert(!std::is_trivially_copy_constructible<NT>::value, "NT");
static_assert(!std::is_trivially_copy_constructible<Wrap>::value, "Wrap");
static_assert(
  std::is_copy_constructible<NT>::value,
  "NT is copy constructible");
static_assert(
  !__is_trivially_constructible(Conv, int),
  "converting construction is a call");
static_assert(__is_trivially_constructible(int, int), "scalar from scalar");
static_assert(__is_trivially_constructible(T, const T &), "builtin copy");
static_assert(!__is_trivially_constructible(NT, const NT &), "builtin copy NT");

int main()
{
  __CPROVER_assert(std::is_trivially_copy_constructible<T>::value, "run time");
  __CPROVER_assert(
    std::is_trivially_copy_constructible<NT>::value, "WRONG (must FAIL)");
}
