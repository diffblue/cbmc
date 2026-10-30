// N5008 [except.spec]/6: an implicitly-declared constructor, or one
// defaulted on its first declaration, is potentially-throwing if and only
// if the initialization of a potentially constructed subobject (a base, a
// virtual base, a member or an array element), or for a default
// constructor a default member initializer, is potentially-throwing.
// [meta.unary.prop] Table 54: is_nothrow_constructible<T, Args...> holds
// if is_constructible<T, Args...> does and `T t(declval<Args>()...);' is
// known not to throw.
#include <type_traits>
extern "C" void __CPROVER_assert(bool, const char *);

struct Throws
{
  Throws()
  {
  }
  Throws(const Throws &)
  {
  }
};
struct Quiet
{
  Quiet() noexcept
  {
  }
  Quiet(const Quiet &) noexcept
  {
  }
};
struct FromBase : Throws
{
};
struct Defaulted
{
  Defaulted() = default;
  Defaulted(const Defaulted &) = default;
  Quiet q;
  Throws t;
};
struct DefaultedQuiet
{
  DefaultedQuiet() = default;
  Quiet q;
};
int may_throw();
struct Nsdmi
{
  int i = may_throw();
};
struct NsdmiConstant
{
  int i = 3;
  Quiet q;
};
struct ArrayMember
{
  Throws a[2];
};
struct VirtualBase : virtual Throws
{
};
union U
{
  int i;
  float f;
};
struct ConversionThrows
{
  operator int()
  {
    return 1;
  }
};
struct ConversionQuiet
{
  operator int() noexcept
  {
    return 1;
  }
};

int main()
{
  __CPROVER_assert(
    !std::is_nothrow_default_constructible<FromBase>::value, "base default");
  __CPROVER_assert(
    !std::is_nothrow_copy_constructible<FromBase>::value, "base copy");
  __CPROVER_assert(
    !std::is_nothrow_default_constructible<Defaulted>::value,
    "defaulted default");
  __CPROVER_assert(
    !std::is_nothrow_copy_constructible<Defaulted>::value, "defaulted copy");
  __CPROVER_assert(
    std::is_nothrow_default_constructible<DefaultedQuiet>::value,
    "defaulted, non-throwing member");
  __CPROVER_assert(
    !std::is_nothrow_default_constructible<Nsdmi>::value,
    "default member initializer");
  __CPROVER_assert(
    std::is_nothrow_copy_constructible<Nsdmi>::value,
    "copy ignores the default member initializer");
  __CPROVER_assert(
    std::is_nothrow_default_constructible<NsdmiConstant>::value,
    "constant default member initializer");
  __CPROVER_assert(
    !std::is_nothrow_copy_constructible<ArrayMember>::value, "array member");
  __CPROVER_assert(
    !std::is_nothrow_default_constructible<VirtualBase>::value, "virtual base");
  __CPROVER_assert(std::is_nothrow_copy_constructible<U>::value, "union copy");
  __CPROVER_assert(
    std::is_nothrow_constructible<int, long>::value, "int from long");
  __CPROVER_assert(
    !std::is_nothrow_constructible<int, ConversionThrows>::value,
    "throwing conversion function");
  __CPROVER_assert(
    std::is_nothrow_constructible<int, ConversionQuiet>::value,
    "noexcept conversion function");
  __CPROVER_assert(
    !std::is_nothrow_constructible<int, Throws>::value, "not constructible");
  __CPROVER_assert(
    std::is_nothrow_constructible<const int &, int>::value, "reference");
  __CPROVER_assert(
    std::is_nothrow_default_constructible<VirtualBase>::value,
    "WRONG (must FAIL)");
  return 0;
}
