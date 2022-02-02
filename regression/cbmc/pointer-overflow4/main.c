#include <stdint.h>

int main()
{
  int32_t i[5];
  // Offset 1 resulted in spuriously failing to detect an overflow in pointer
  // arithmetic in the next line for PTRDIFF_MAX * 4 + 4 = 0 in wrap-around
  // semantics. Any other offset would yield the expected failure.
  int32_t *p = &i[1];
  int32_t *q = p + PTRDIFF_MAX;
}
