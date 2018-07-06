#include <stdio.h>

int a = 2; // unused
char b;
unsigned long int c;
unsigned char d; // write only
int e = 9;       // used in return statement

int usedi = 100;

struct
{
  int data;
} s_unused, s_writeonly, s_used;

unsigned long int f()
{
  usedi = usedi + 1;
  unsigned long int *p_f = &c; // uses as read
  return *p_f;
}

int *g()
{
  usedi = usedi + 2;
  return &e; // uses e, but return value of g is used in write only
}

int h()
{
  return s_used.data;
}

unsigned long int i()
{
  return c = d + e;
}

int main()
{
  int p_a = 5; // unused
  unsigned long int p_b = f();
  int *p_c = g(); // unused
  int p_d = 6;
  int p_e = 7;
  int p_f = 8;
  int *p_g = g();
  i();

  s_used.data = 0;
  s_writeonly = s_used;

  d = p_b + 9;
  printf("%d\n", p_d);
  printf("%p\n", &p_e);
  printf("%d\n", s_used.data);
  printf("%d\n", *p_g);
  printf("%d\n", h());
  if(p_f)
  {
    return 0;
  }
  else
  {
    return 1;
  }
}
