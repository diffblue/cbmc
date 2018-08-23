#include <stdio.h>

typedef void (*void_fp)(void);

struct ops
{
  void_fp a;
  void_fp b;
};

void f0(void)
{
  printf("%i\n", 0);
}
void f1(void)
{
  printf("%i\n", 1);
}
void f2(void)
{
  printf("%i\n", 2);
}
void f3(void)
{
  void_fp a = f0;
  printf("%i\n", 3);
}
void f4(void)
{
  printf("%i\n", 5);
}
void f5(void)
{
  f4();
}
void f6(void)
{
  f5();
}

const void_fp fp_tbl[] = {f2, NULL, f1};

void func()
{
  fp_tbl[0]();
  fp_tbl[1]();
}

int main()
{
  struct ops o;

  o.a = f4;
  o.b = f5;

  func();

  o.a();

  return 0;
}
