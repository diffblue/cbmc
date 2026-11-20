// Clang 20's builtin alias template `__builtin_common_type<BaseTemplate,
// HasTypeMember, HasNoTypeMember, Ts...>', the way libc++ 21's
// <__type_traits/common_type.h> implements std::common_type with it
// (N5008 [meta.trans.other]/3-5): HasTypeMember<C> for the common type C,
// HasNoTypeMember when there is none; BaseTemplate<D1, D2> (the
// user-specializable common_type_t) is used for arguments that are not
// their own decayed types and for the pairwise fold.  The builtin was
// unknown ("symbol '__builtin_common_type' is unknown"), so every libc++ 21
// program instantiating common_type (chrono::duration arithmetic, every
// container through allocator_traits) failed to type-check.  Also:
// [expr.cond]/7.2, the usual arithmetic conversions on the conditional
// operator's arithmetic operands (`b ? c : s' is an int, not a short).
extern "C" void __CPROVER_assert(bool, const char *);
namespace mystd
{
template <class T>
struct type_identity
{
  using type = T;
};
struct empty
{
};
template <class... Args>
struct common_type;
template <class... Args>
using common_type_t = typename common_type<Args...>::type;
template <class... Args>
struct common_type
  : __builtin_common_type<common_type_t, type_identity, empty, Args...>
{
};
template <class T, class U>
constexpr bool is_same_v = false;
template <class T>
constexpr bool is_same_v<T, T> = true;
template <class T, class = void>
struct has_type : empty
{
  static constexpr bool value = false;
};
template <class T>
struct has_type<T, decltype((void)sizeof(typename T::type))>
{
  static constexpr bool value = true;
};
} // namespace mystd
struct Base
{
};
struct Derived : Base
{
};
struct Unrelated
{
};
// user specialization honoured through the base template (/3.3.1, /3.4)
struct Meters
{
};
struct Feet
{
};
namespace mystd
{
template <>
struct common_type<Meters, Feet>
{
  using type = double;
};
} // namespace mystd
int main()
{
  using namespace mystd;
  __CPROVER_assert(is_same_v<common_type_t<int, long>, long>, "int, long");
  __CPROVER_assert(is_same_v<common_type_t<char, short>, int>, "promotion");
  __CPROVER_assert(is_same_v<common_type_t<int>, int>, "single");
  __CPROVER_assert(is_same_v<common_type_t<const int &, int>, int>, "decayed");
  __CPROVER_assert(
    is_same_v<common_type_t<int[3], int *>, int *>, "array decays");
  __CPROVER_assert(
    is_same_v<common_type_t<Derived, Base>, Base>, "derived to base");
  __CPROVER_assert(is_same_v<common_type_t<int, short, long>, long>, "three");
  __CPROVER_assert(
    is_same_v<common_type_t<Meters, Feet>, double>, "user specialization");
  __CPROVER_assert(
    is_same_v<common_type_t<const Meters &, Feet>, double>,
    "user specialization via decay");
  __CPROVER_assert(
    is_same_v<common_type_t<Meters, Feet, float>, double>,
    "user specialization in fold");
  __CPROVER_assert(
    !has_type<common_type<Base, Unrelated>>::value, "no common type");
  __CPROVER_assert(!has_type<common_type<>>::value, "empty");
  __CPROVER_assert(
    is_same_v<common_type_t<int *, const int *>, const int *>,
    "pointer qualification");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
