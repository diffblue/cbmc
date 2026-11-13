#include <assert.h>

// Reading a member of a compound literal must still evaluate the side
// effects of the literal's other initializers.
struct S
{
  int a, b;
};

int n;
int g(void)
{
  return ++n;
}

int main(void)
{
  // C11 6.7.6.2p5: the size expression of a variable length array is
  // evaluated
  int a[(struct S){g(), 3}.b];
  assert(sizeof(a) == 3 * sizeof(int));
  assert(n == 1);

  int x = sizeof(int[(struct S){g(), 3}.b]);
  assert(x == 3 * sizeof(int));
  assert(n == 2);

  // the null-pointer-constant check simplifies the right-hand operand
  int *pointer = 0;
  int r = pointer == ((struct S){.a = 0, .b = ++n}).a;
  assert(r);
  assert(n == 3);

  return 0;
}
