extern "C" void __CPROVER_assert(bool, const char *);
#include <cstdint>
template <class T> struct G1 { T lo; T hi; } __attribute__((packed, aligned(16)));
template <class T, int N> struct G2 { T v[N]; } __attribute__((packed, aligned(16)));
template <class T> struct __attribute__((packed, aligned(16))) G3 { T lo; T hi; };
template <class T> struct alignas(16) G4 { T lo; T hi; };
template <class T> struct G5 { T lo; uint8_t tag; } __attribute__((packed, aligned(8)));
template <class T> struct G6 { T lo; T hi; } __attribute__((aligned(16)));
template <class T> struct G7 { G1<T> a; uint8_t b; } __attribute__((packed, aligned(16)));
struct W { G1<uint16_t> g; uint8_t b; };
template <class T> struct G8 { T lo; T hi; } __attribute__((__packed__, __aligned__(16)));
typedef G1<uint32_t> g1u32_t;
using lreg_t = G1<uint16_t>;
int main()
{
  __CPROVER_assert(sizeof(G1<uint16_t>) == 16, "G1<u16> 16 bytes");
  __CPROVER_assert(sizeof(G1<uint64_t>) == 16, "G1<u64> 16 bytes");
  __CPROVER_assert(sizeof(G2<uint16_t, 3>) == 16, "G2<u16,3> 16 bytes");
  __CPROVER_assert(sizeof(G2<uint32_t, 5>) == 32, "G2<u32,5> 32 bytes");
  __CPROVER_assert(sizeof(G3<uint16_t>) == 16, "G3 attribute before body: 16 bytes");
  __CPROVER_assert(sizeof(G4<uint16_t>) == 16, "G4 alignas: 16 bytes");
  __CPROVER_assert(sizeof(G5<uint32_t>) == 8, "G5 packed aligned 8: 8 bytes");
  __CPROVER_assert(sizeof(G6<uint16_t>) == 16, "G6 aligned only: 16 bytes");
  __CPROVER_assert(sizeof(G7<uint16_t>) == 32, "G7 nested: 32 bytes");
  __CPROVER_assert(sizeof(W) == 32, "W containing an aligned template instance: 32 bytes");
  __CPROVER_assert(sizeof(G8<uint16_t>) == 16, "G8 __packed__ __aligned__: 16 bytes");
  __CPROVER_assert(sizeof(g1u32_t) == 16 && sizeof(lreg_t) == 16, "typedef/alias of the instance");
  G1<uint16_t> g{1, 2};
  __CPROVER_assert(g.lo + g.hi == 3, "values");
  return 0;
}
