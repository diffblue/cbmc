extern "C" void __CPROVER_assert(bool, const char *);
#include <cstdint>
template <class T>
struct G
{
  T lo;
  T hi;
} __attribute__((packed, aligned(16)));
using lreg_t = G<uint16_t>;
typedef G<uint32_t> wreg_t;
struct H
{
  uint16_t a;
  uint16_t b;
} __attribute__((packed, aligned(16)));
struct F1
{
  lreg_t regs[4];
  uint8_t tag;
};
struct F2
{
  uint8_t tag;
  wreg_t w;
};
struct F3
{
  uint8_t tag;
  lreg_t regs[2];
};
struct F4
{
  lreg_t regs[4];
  uint8_t tag;
  wreg_t w;
};
// GCC: as part of a typedef, aligned(n) can both increase and decrease the
// alignment of a non-class type (g++ also applies it in an alias-declaration,
// clang++ does not -- not tested)
typedef uint32_t __attribute__((aligned(8))) u32a8;
struct P
{
  uint8_t a;
  u32a8 v;
};
// ... but is ignored for a class type outside its definition
template <class T>
struct Pk
{
  T lo;
  T hi;
} __attribute__((packed));
using pk_t = Pk<uint16_t> __attribute__((aligned(16)));
int main()
{
  __CPROVER_assert(
    alignof(G<uint16_t>) == 16 && alignof(H) == 16,
    "alignof packed, aligned(16)");
  __CPROVER_assert(
    sizeof(F1) == 80, "F1: array of aligned instances then a byte");
  __CPROVER_assert(
    sizeof(F2) == 32,
    "F2: byte then typedef'd aligned instance (first use of the instance)");
  __CPROVER_assert(
    sizeof(F3) == 48, "F3: byte then array of aligned instances");
  __CPROVER_assert(sizeof(F4) == 96, "F4: all");
  __CPROVER_assert(
    alignof(u32a8) == 8 && sizeof(P) == 16, "aligned typedef of a scalar");
  __CPROVER_assert(
    sizeof(pk_t) == 4 && alignof(pk_t) == 1,
    "attribute on an alias of a class type is ignored");
  F4 f{};
  f.regs[2].hi = 7;
  f.w.lo = 9;
  f.tag = 3;
  __CPROVER_assert(f.regs[2].hi == 7 && f.w.lo == 9 && f.tag == 3, "values");
  return 0;
}
