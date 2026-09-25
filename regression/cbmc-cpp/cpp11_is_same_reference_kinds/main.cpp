// N5008 [dcl.ref]: `T &' and `T &&' are distinct types.  The front end
// models both as pointer types with `#reference' set, and an rvalue reference
// additionally with `#rvalue_reference'; irept::operator== ignores such
// comments, so __is_same (and std::is_same through it) reported
// is_same<int &&, int &> TRUE.  libc++'s iter_rvalue_reference_t /
// __indirectly_readable_impl checks hinge on exactly this distinction.
#include <type_traits>
extern "C" void __CPROVER_assert(bool, const char *);

static_assert(!__is_same(int &&, int &), "rvalue vs lvalue reference");
static_assert(!__is_same(int &, int &&), "lvalue vs rvalue reference");
static_assert(__is_same(int &&, int &&), "rvalue reference same");
static_assert(__is_same(int &, int &), "lvalue reference same");
static_assert(!__is_same(int &, int), "reference vs object");
static_assert(!__is_same(const int &, int &), "const reference vs reference");
static_assert(!std::is_same<int &&, int &>::value, "std::is_same");
static_assert(std::is_same<int &&, int &&>::value, "std::is_same same");
static_assert(!std::is_same<int (&)[3], int (&&)[3]>::value, "array refs");

template <class T>
int kind(T &&)
{
  return std::is_same<T &&, int &>::value    ? 1
         : std::is_same<T &&, int &&>::value ? 2
                                             : 0;
}

int main()
{
  int x = 0;
  __CPROVER_assert(kind(x) == 1 && kind(0) == 2, "forwarding reference kinds");
  __CPROVER_assert(kind(x) == 2, "WRONG (must FAIL)");
}
