extern "C" void __CPROVER_assert(bool, const char *);
#include <cstddef>
#include <cstdint>
// N5008 [class.mem]: member typedefs/alias-declarations, static data members
// and member functions are members but not subobjects -- they occupy no
// storage.  The layout laid them out as data (a member typedef `using
// value_type = T;' as a T-sized member, a static as its type), misplacing
// what follows and adding padding (user Issues 5 and 7: a bit-field struct
// with a static member was 4 bytes instead of 2, an attributed class
// template with a member alias 30 instead of 16).
enum class RS : uint8_t { N, S };
struct H1 { static constexpr uint8_t kSize = 2; uint8_t a : 3; RS r : 1; uint8_t b : 4; uint8_t c : 6; uint8_t d : 2; };
struct H2 { using self = H2; uint8_t a : 3; RS r : 1; uint8_t b : 4; uint8_t c : 8; };
struct H3 { uint8_t a : 3; RS r : 1; uint8_t b : 4; uint8_t c : 8; static uint32_t counter; uint8_t size() const { return 2; } };
uint32_t H3::counter = 0;
struct H4 { static int x; char c; };
struct H5 { typedef long big; char c; };
struct H6 { char c; static long double ld; alignas(1) char d; };
struct B1 { long l; short s; };
struct H7 : B1 { using vt = unsigned long; signed char c; }; // offsetof must skip the alias
union U1 { typedef unsigned long td; signed char m : 3; } __attribute__((packed));
union U2 { short m; using vt = float; static double sd; int f() const { return 0; } };
template <typename T> struct G
{
  static_assert(sizeof(T) <= 16, "fits");
  using value_type = T;
  T v[16 / sizeof(T)];
  constexpr G() : v{} {}
  static constexpr std::size_t lanes() { return 16 / sizeof(T); }
  T sum() const { T s = 0; for(std::size_t i = 0; i < lanes(); ++i) s += v[i]; return s; }
} __attribute__((packed, aligned(16)));
template <typename T> struct K { using value_type = T; T lo; T hi; } __attribute__((aligned(16)));
using lreg_t = G<uint16_t>;
struct Regs { lreg_t a; G<uint8_t> b; uint8_t flags; };
int main()
{
  __CPROVER_assert(sizeof(H1) == 2, "bit-field struct with a static constexpr member");
  __CPROVER_assert(sizeof(H2) == 2, "bit-field struct with a member alias");
  __CPROVER_assert(sizeof(H3) == 2, "bit-field struct with a static member and a method");
  __CPROVER_assert(sizeof(H4) == 1, "static data member takes no storage");
  __CPROVER_assert(sizeof(H5) == 1, "member typedef takes no storage");
  __CPROVER_assert(sizeof(H6) == 2 && alignof(H6) == 1, "a static member's type does not align the class");
  __CPROVER_assert(sizeof(H7) == 24 && offsetof(H7, c) == 16, "offsetof skips the member alias");
  __CPROVER_assert(sizeof(U1) == 1 && alignof(U1) == 1, "union: a member typedef does not size it");
  __CPROVER_assert(sizeof(U2) == 2 && alignof(U2) == 2, "union: alias, static member and method take no storage");
  __CPROVER_assert(sizeof(G<uint16_t>) == 16 && alignof(G<uint16_t>) == 16, "attributed class template with a member alias");
  __CPROVER_assert(sizeof(lreg_t) == 16, "alias of the instance");
  __CPROVER_assert(sizeof(K<uint16_t>) == 16 && alignof(K<uint16_t>) == 16, "aligned class template with a member alias");
  __CPROVER_assert(sizeof(Regs) == 48 && offsetof(Regs, b) == 16 && offsetof(Regs, flags) == 32, "instances as members");
  lreg_t x;
  x.v[0] = 3; x.v[7] = 4;
  __CPROVER_assert(x.sum() == 7 && lreg_t::lanes() == 8, "values");
  H3 h{}; h.r = RS::S; h.c = 200;
  __CPROVER_assert(h.r == RS::S && h.c == 200 && h.size() == 2, "bit-field values");
  return 0;
}
