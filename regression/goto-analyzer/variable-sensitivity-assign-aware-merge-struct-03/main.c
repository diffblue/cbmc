#include <assert.h>

struct inner
{
  int a;
  int b;
};

struct outer
{
  struct inner i;
  int z;
};

struct outer global;

void f00(void)
{
  global.i.a = 0;
}

int main(int argc, char **argv)
{
  global.i.a = 1;
  global.i.b = 1;
  global.z = 1;

  f00();

  assert(global.i.a == 0);
  assert(global.i.b == 1);
  assert(global.z == 1);

  // A second call site with differing values forces f00 to be analysed over
  // merged inputs, so the sibling fields global.i.b and global.z become
  // UNKNOWN at the function start. Without field-sensitive recursion the
  // whole-symbol clobber would lose them; the recursive descent keeps them.
  global.i.a = 2;
  global.i.b = 2;
  global.z = 2;

  f00();

  assert(global.i.a == 0);
  assert(global.i.b == 2);
  assert(global.z == 2);

  return 0;
}
