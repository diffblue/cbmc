#include <assert.h>

struct s
{
  int x;
  int y;
};

struct s global;
int alsoGlobal;

void f00(void)
{
  global.x = 0;
}

int main(int argc, char **argv)
{
  global.x = 1;
  global.y = 1;
  alsoGlobal = 1;

  f00();

  assert(global.x == 0);
  assert(global.y == 1);
  assert(alsoGlobal == 1);

  global.x = 2;
  global.y = 2;
  alsoGlobal = 2;

  f00();

  assert(global.x == 0);
  assert(global.y == 2);
  assert(alsoGlobal == 2);

  return 0;
}
