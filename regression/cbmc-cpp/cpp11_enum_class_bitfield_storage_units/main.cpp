extern "C" void __CPROVER_assert(bool, const char *);
#include <cstdint>
namespace isa {
enum class ReshapeStrategy : uint8_t;
enum class Mode : std::uint8_t { A, B, C, D };
enum class ReshapeStrategy : uint8_t { NONE = 0, SPLIT = 1 };
struct A { uint8_t a : 6; ReshapeStrategy r : 1; uint8_t b : 4; uint8_t c : 5; };
static_assert(sizeof(A) == 3, "A: unit padding, 3 bytes");
struct B { bool x : 1; ReshapeStrategy r : 1; uint8_t a : 6; Mode m : 2; bool y : 1; uint8_t z : 5; };
static_assert(sizeof(B) == 2, "B");
struct C { uint8_t a : 7; ReshapeStrategy r : 1; uint8_t b : 8; } __attribute__((packed));
static_assert(sizeof(C) == 2, "C");
class D { public: struct Inner { uint8_t a : 4; ReshapeStrategy r : 1; Mode m : 2; uint8_t b : 1; uint8_t c; }; };
static_assert(sizeof(D::Inner) == 2, "D");
union U { struct { uint8_t a : 5; ReshapeStrategy r : 1; uint8_t b : 2; uint8_t c; } s; uint16_t raw; };
static_assert(sizeof(U) == 2, "U");
struct E { ReshapeStrategy r : 1; uint8_t a : 7; uint8_t b; };
static_assert(sizeof(E) == 2, "E");
struct F { uint8_t a : 3; ReshapeStrategy r : 2; ReshapeStrategy s : 3; uint8_t b : 8; };
static_assert(sizeof(F) == 2, "F");
struct G { uint8_t a : 3; ReshapeStrategy r : 1; uint8_t b : 5; };
static_assert(sizeof(G) == 2, "G: straddle");
}
int main()
{
  isa::A a{}; a.r = isa::ReshapeStrategy::SPLIT; a.c = 17;
  __CPROVER_assert(a.r == isa::ReshapeStrategy::SPLIT && a.c == 17, "A values");
  isa::G g{}; g.b = 21; g.r = isa::ReshapeStrategy::SPLIT;
  __CPROVER_assert(g.b == 21 && g.a == 0, "G values");
  return 0;
}
