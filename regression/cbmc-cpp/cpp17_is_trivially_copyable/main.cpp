// N5008 [basic.types.general]/9: scalar types, trivially copyable class
// types, arrays of such and cv-qualified versions are trivially copyable;
// [class.prop]/1: a trivially copyable class has only trivial (implicitly
// declared, not user-provided) copy/move constructors and assignment
// operators, a trivial destructor, no virtual functions or bases, and bases
// and members of trivially copyable type; /2 + [class.default.ctor]/3: a
// trivial class is trivially copyable with a trivial default constructor
// (no user-provided one, no default member initializers).  The builtins
// __is_trivially_copyable and __is_trivial -- behind std::is_trivially_
// copyable and std::is_trivial -- were an unconditional FALSE, so
// is_trivially_copyable<int> was false and libc++'s variant<int, double>
// computed a non-trivial copy.
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
struct D
{
  ~D();
};
struct V
{
  virtual void f();
};
struct A
{
  NT n;
};
struct M
{
  int m;
  T t;
  int arr[3];
};
struct Def
{
  int x = 5;
};
struct UD
{
  UD();
};
struct AsgnOp
{
  AsgnOp &operator=(const AsgnOp &);
};
enum E
{
  e1
};
union U
{
  int i;
  float f;
};
static_assert(__is_trivially_copyable(int), "int");
static_assert(__is_trivially_copyable(double), "double");
static_assert(__is_trivially_copyable(int *), "pointer");
static_assert(__is_trivially_copyable(E), "enum");
static_assert(__is_trivially_copyable(int[4]), "array");
static_assert(__is_trivially_copyable(const int), "const int");
static_assert(__is_trivially_copyable(T), "T");
static_assert(__is_trivially_copyable(M), "M members");
static_assert(__is_trivially_copyable(U), "union");
static_assert(__is_trivially_copyable(Def), "Def: NSDMI ok for copyable");
static_assert(
  __is_trivially_copyable(UD),
  "UD: user default ctor ok for copyable");
static_assert(!__is_trivially_copyable(NT), "NT");
static_assert(!__is_trivially_copyable(D), "D dtor");
static_assert(!__is_trivially_copyable(V), "V virtual");
static_assert(!__is_trivially_copyable(A), "A member");
static_assert(!__is_trivially_copyable(AsgnOp), "AsgnOp");
static_assert(!__is_trivially_copyable(int &), "reference");
static_assert(__is_trivial(int), "trivial int");
static_assert(__is_trivial(T), "trivial T");
static_assert(!__is_trivial(Def), "Def not trivial");
static_assert(!__is_trivial(UD), "UD not trivial");
static_assert(
  std::is_trivially_copyable_v<int> && std::is_trivially_copyable<T>::value &&
    !std::is_trivially_copyable_v<NT>,
  "std");
static_assert(std::is_trivial_v<T> && !std::is_trivial_v<Def>, "std trivial");
int main()
{
  __CPROVER_assert(std::is_trivially_copyable<T>::value, "run time read");
  __CPROVER_assert(std::is_trivially_copyable<NT>::value, "WRONG (must FAIL)");
}
