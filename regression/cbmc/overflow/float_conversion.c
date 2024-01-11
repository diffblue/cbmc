#include <stdint.h>

int main()
{
  uint32_t u = 0xffffffffu;

  // since the double type seems to be implemented with a IEEE 754 binary64
  // format in CBMC, which has 53 bits of mantissa, double has enough bits to
  // represent the exact value of u, use, e.g., http://weitz.de/ieee/ to check;
  // therefore, C17, section 6.3.1.4, paragraph 2 says that this is
  // defined behavior and d should store the exact value that u stores
  double d = u;

  // defined behavior behavior as well, by C17 section 6.3.1.4, paragraph 1,
  // because the 'unsigned' type can represent the value; however,
  // cbmc --conversion-check used to complain
  u = (uint32_t)d;

  return 0;
}
