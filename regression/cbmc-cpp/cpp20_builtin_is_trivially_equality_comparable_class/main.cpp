// Clang's __is_trivially_equality_comparable(T) (an extension; libc++ uses it
// to replace comparisons by memcmp/memchr): true for a class whose
// operator== is defaulted ([class.eq]/3: it compares the subobjects in
// order; [class.compare.default]/4: a defaulted operator<=> declares one)
// when every subobject is itself trivially equality comparable and the
// class has no padding, so equal values have equal object representations.
#include <compare>

extern "C" void __CPROVER_assert(bool, const char *);

struct D
{
  int x;
  int y;
  bool operator==(const D &) const = default;
};
struct Padded
{
  char c;
  int i;
  bool operator==(const Padded &) const = default;
};
struct NoEquality
{
  int x;
};
struct UserEquality
{
  int x;
  bool operator==(const UserEquality &o) const
  {
    return x == o.x;
  }
};
struct FloatMember
{
  float f;
  bool operator==(const FloatMember &) const = default;
};
struct Nested
{
  D d;
  bool operator==(const Nested &) const = default;
};
struct FriendForm
{
  int x;
  friend bool operator==(const FriendForm &, const FriendForm &) = default;
};
struct Derived : D
{
  int z;
  bool operator==(const Derived &) const = default;
};
struct ByValue
{
  int x;
  friend bool operator==(ByValue, ByValue) = default;
};
struct Spaceship
{
  int x;
  auto operator<=>(const Spaceship &) const = default;
};
struct NestedNoEquality
{
  NoEquality n;
  bool operator==(const NestedNoEquality &) const = delete;
};

static_assert(__is_trivially_equality_comparable(D), "defaulted, no padding");
static_assert(__is_trivially_equality_comparable(Nested), "nested");
static_assert(!__is_trivially_equality_comparable(Padded), "padding");
static_assert(!__is_trivially_equality_comparable(NoEquality), "no operator==");
static_assert(
  !__is_trivially_equality_comparable(UserEquality),
  "user-provided");
static_assert(!__is_trivially_equality_comparable(FloatMember), "float");
static_assert(__is_trivially_equality_comparable(FriendForm), "friend");
static_assert(__is_trivially_equality_comparable(Derived), "base");
static_assert(!__is_trivially_equality_comparable(NestedNoEquality), "deleted");
static_assert(__is_trivially_equality_comparable(ByValue), "by value");
static_assert(__is_trivially_equality_comparable(Spaceship), "from <=>");

int main()
{
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
