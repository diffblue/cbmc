#include <assert.h>

void f(int, char, float);

int main()
{
  int x;
  char c;
  float a;

  x = 3;
  c = 'a';
  a = 2.7;

  f(x, c, a);
}

