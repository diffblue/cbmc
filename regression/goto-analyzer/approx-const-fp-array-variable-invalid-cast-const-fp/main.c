#include <stdio.h>

int f1 (void)
{
  printf("%i\n", 1);
  return 1;
}
int f2 (void)
{
  printf("%i\n", 2);
  return 2;
}
int f3 (void)
{
  printf("%i\n", 3);
  return 3;
}
int f4 (void)
{
  printf("%i\n", 4);
  return 4;
}
int f5 (void)
{
  printf("%i\n", 5);
  return 5;
}
int f6 (void)
{
  printf("%i\n", 6);
  return 6;
}
int f7 (void)
{
  printf("%i\n", 7);
  return 7;
}
int f8 (void)
{
  printf("%i\n", 8);
  return 8;
}
int f9 (void)
{
  printf("%i\n", 9);
  return 9;
}

typedef void(*void_fp)(void);
typedef int(*int_fp)(void);

// There is a basic check that excludes all functions that aren't used anywhere
// This ensures that check can't work in this example
const int_fp fp_all[] = {f1, f2 ,f3, f4, f5 ,f6, f7, f8, f9};

void(* const fp_tbl[3])(void) =
{
  (void(*)())f2,
  (void(*)())f3,
  (void(*)())f4,
};


void func(int i)
{
  const void_fp fp = fp_tbl[i];
  fp();
}

int main()
{
  for(int i=0;i<3;i++)
  {
    func(i);
  }
  return 0;
}
