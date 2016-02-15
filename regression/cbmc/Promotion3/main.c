/* 6.3.1.1, 2:
 * The following may be used in an expression wherever an int or unsigned int
 * may be used:
 * — An object or expression with an integer type (other than int or unsigned
 * int) whose integer conversion rank is less than or equal to the rank of int
 * and unsigned int.
 * — A bit-field of type _Bool, int, signed int, or unsigned int.
 * If an int can represent all values of the original type (as restricted by the
 * width, for a bit-field), the value is converted to an int; otherwise, it is
 * converted to an unsigned int. These are called the integer promotions.58) All
 * other types are unchanged by the integer promotions.
 */

#include <assert.h>

union U0 {
  // int can represent all values
  unsigned f0 : 31;
};

union U1 {
  // int cannot represent all values
  unsigned f0 : 32;
};

int main()
{
  if(sizeof(int)!=4) return 0;

  union U0 u0 = {1};
  union U1 u1 = {1};
  int i = -1;

  assert(u0.f0 >= i);
  assert(!(u1.f0 >= i));

  return 0;
}
