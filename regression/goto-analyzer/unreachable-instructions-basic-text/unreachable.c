#include <assert.h>

int not_called(int x)
{
  return x + x;
}

int dead_inside(int x)
{
  int y = x + x;
  goto end;
  ++y;
 end : return y;
}

int obviously_dead(int x)
{
  if (0)
  {
    x++;
  }
  return x;
}

int not_obviously_dead(int x)
{
  if (dead_inside(x) != x + x) {
    x++;
  }
  return obviously_dead(x);
}

int nondet_int(void);

int main(int argc, char **argv)
{
  int x = 23;

  assert(x == not_obviously_dead(x));

  return;
}
