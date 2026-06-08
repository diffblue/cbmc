// Buffer offset computed two ways: (rows*stride)*elt_size vs
// rows*(stride*elt_size). Common in driver code.
#include <stdint.h>
uint64_t opaque(uint64_t x) { return x; }
int main() {
  uint16_t rows, stride, elt;
  __CPROVER_assume(rows < 100 && stride > 0 && elt > 0 && elt <= 16);
  uint64_t off1 = opaque(opaque((uint64_t)rows * (uint64_t)stride) * (uint64_t)elt);
  uint64_t off2 = opaque((uint64_t)rows * opaque((uint64_t)stride * (uint64_t)elt));
  __CPROVER_assert(off1 == off2, "buffer offset associativity");
  return 0;
}
