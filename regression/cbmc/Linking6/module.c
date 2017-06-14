#include <stdlib.h>

extern char buffer[];

static size_t _debug_tempBufferHead = ((size_t)(&buffer));

void set() {
  *(char *)_debug_tempBufferHead = 'a';
}
