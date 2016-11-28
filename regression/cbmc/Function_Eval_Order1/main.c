/* C99 6.5.2.2:10
 *
 * The order of evaluation of the function designator, the actual arguments, and
 * subexpressions within the actual arguments is unspecified, but there is a sequence point
 * before the actual call.
 */


#include <assert.h>

int f00 (void) {
  static int i = 0;

  return ++i;
}

int f01 (int x, int y) {
  return 3*x + y;
}

int main (void) {
  int z = f01(f00(),f00());

  assert(z == 5);

  return 1;
}
