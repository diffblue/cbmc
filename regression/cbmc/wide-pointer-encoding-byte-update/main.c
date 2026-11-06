#include <stddef.h>

// Exercises the wide pointer encoding's byte_update handling when the value
// written is a pointer (bv_pointerst::convert_byte_update "value is a pointer"
// branch): a pointer is stored into a plain byte buffer and read back.

int x;

void main()
{
  char buf[2 * sizeof(int *)] = {0};
  *(int **)(buf + sizeof(int *)) = &x;
  int *p = *(int **)(buf + sizeof(int *));
  __CPROVER_assert(p == &x, "byte_update with a pointer value");
}
