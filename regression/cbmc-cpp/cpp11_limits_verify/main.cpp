// Verify integer limit constants from <climits> and <cstdint>
#include <cassert>
#include <climits>
#include <cstdint>

int nondet_int();

int main()
{
  // Verify standard integer width relationships
  static_assert(CHAR_BIT == 8, "char is 8 bits");
  static_assert(sizeof(int) * CHAR_BIT >= 16, "int is at least 16 bits");
  static_assert(SHRT_MAX >= 32767, "short max is at least 32767");
  static_assert(INT_MAX >= 32767, "int max is at least 32767");

  // Verify fixed-width types
  static_assert(sizeof(int8_t) == 1, "int8_t is 1 byte");
  static_assert(sizeof(int16_t) == 2, "int16_t is 2 bytes");
  static_assert(sizeof(int32_t) == 4, "int32_t is 4 bytes");

  // Runtime: overflow detection
  int x = nondet_int();
  __CPROVER_assume(x >= 0 && x <= INT_MAX - 1);
  int y = x + 1;
  assert(y > x);

  return 0;
}
