// N5008 [meta.unary.prop]: is_trivially_assignable<T, U> is true when the
// assignment `declval<T>() = declval<U>()' is well-formed and calls no
// operation that is not trivial ([class.copy.assign]/9: the copy/move
// assignment operator is not user-provided, the class has no virtual
// functions or virtual bases and every subobject's is trivial).
// `__is_trivially_assignable' and `__is_nothrow_assignable' were
// unconditionally true (as `__is_trivially_constructible' had been).
extern "C" void __CPROVER_assert(bool, const char *);
template <class T, class U>
struct is_assignable
{
  static constexpr bool value = __is_assignable(T, U);
};
template <class T, class U>
struct is_trivially_assignable
{
  static constexpr bool value = __is_trivially_assignable(T, U);
};
template <class T, class U>
struct is_nothrow_assignable
{
  static constexpr bool value = __is_nothrow_assignable(T, U);
};
struct Triv
{
  int a;
};
struct UserAssign
{
  int a;
  UserAssign &operator=(const UserAssign &)
  {
    return *this;
  }
};
struct Virt
{
  virtual void f();
};
struct FromInt
{
  FromInt &operator=(int);
};
struct Member
{
  UserAssign m;
};
static_assert(
  is_trivially_assignable<Triv &, const Triv &>::value,
  "Triv copy");
static_assert(is_trivially_assignable<Triv &, Triv &&>::value, "Triv move");
static_assert(is_trivially_assignable<int &, int>::value, "int");
static_assert(is_trivially_assignable<int &, double>::value, "int from double");
static_assert(
  !is_trivially_assignable<UserAssign &, const UserAssign &>::value,
  "user-provided");
static_assert(!is_trivially_assignable<Virt &, const Virt &>::value, "virtual");
static_assert(
  !is_trivially_assignable<Member &, const Member &>::value,
  "member with user-provided");
static_assert(
  is_assignable<FromInt &, int>::value &&
    !is_trivially_assignable<FromInt &, int>::value,
  "converting operator=");
static_assert(!is_trivially_assignable<const int &, int>::value, "const dest");
static_assert(
  is_nothrow_assignable<Triv &, const Triv &>::value &&
    !is_nothrow_assignable<const int &, int>::value,
  "nothrow follows assignability");
int main()
{
  __CPROVER_assert(
    is_trivially_assignable<Triv &, const Triv &>::value &&
      !is_trivially_assignable<UserAssign &, const UserAssign &>::value,
    "traits");
  __CPROVER_assert(
    is_trivially_assignable<UserAssign &, const UserAssign &>::value,
    "WRONG (must FAIL)");
}
