// Clang's __is_trivially_equality_comparable(T) (an extension; libc++ uses it
// to replace comparisons by memcmp/memchr): true for a class whose
// operator== is defaulted ([class.compare.default]/3: it compares the
// subobjects in order) when every subobject is itself trivially equality
// comparable and the class has no padding, so equal values have equal
// object representations.  CBMC answers false for every class.
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

static_assert(__is_trivially_equality_comparable(D), "defaulted, no padding");
static_assert(__is_trivially_equality_comparable(Nested), "nested");
static_assert(!__is_trivially_equality_comparable(Padded), "padding");
static_assert(!__is_trivially_equality_comparable(NoEquality), "no operator==");
static_assert(
  !__is_trivially_equality_comparable(UserEquality),
  "user-provided");
static_assert(!__is_trivially_equality_comparable(FloatMember), "float");

int main()
{
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
