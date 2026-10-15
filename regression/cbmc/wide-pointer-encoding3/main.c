// Test for issue #8103: integer-to-pointer casting
// (void*)addr where addr is constrained to be within a known object
// should read from that object
#include <stddef.h>
#include <stdint.h>

unsigned char buf[16];
size_t nondet_size_t(void);
uint64_t nondet_uint64_t(void);

void main()
{
  size_t index = nondet_size_t();
  __CPROVER_assume(index < 2);
  buf[index * 8] = 42;

  uint64_t rd = nondet_uint64_t();
  __CPROVER_assume(rd == (uint64_t)buf + index * 8);

  uint8_t *p = (uint8_t *)(void *)rd;
  __CPROVER_assert(*p == 42, "I2P dereference reads correct value");
}
