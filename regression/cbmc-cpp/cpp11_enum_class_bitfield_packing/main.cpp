#include <cstdint>
enum class ReshapeStrategy : uint8_t { NONE = 0, FLATTEN = 1, RESHAPE = 2 };
struct __attribute__((packed)) Hdr
{
  uint8_t opcode : 4;
  uint8_t flags : 3;
  ReshapeStrategy reshape_strategy : 1;
  uint8_t dtype : 4;
  uint8_t rank : 4;
};
static_assert(sizeof(Hdr) == 2, "");
struct Hdr2
{
  uint8_t opcode : 4;
  uint8_t flags : 3;
  ReshapeStrategy reshape_strategy : 1;
  uint8_t dtype : 4;
  uint8_t rank : 4;
};
static_assert(sizeof(Hdr2) == 2, "");
extern "C" void __CPROVER_assert(bool, const char *);
int main() { Hdr h; h.reshape_strategy = ReshapeStrategy::FLATTEN; h.rank = 9; __CPROVER_assert(h.reshape_strategy == ReshapeStrategy::FLATTEN && h.rank == 9, "bit-field values"); return 0; }
