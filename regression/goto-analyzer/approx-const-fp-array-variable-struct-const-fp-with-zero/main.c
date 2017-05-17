#include <stdio.h>

void f1 (void) { printf("%i\n", 1); }
void f2 (void) { printf("%i\n", 2); }
void f3 (void) { printf("%i\n", 3); }
void f4 (void) { printf("%i\n", 4); }
void f5 (void) { printf("%i\n", 5); }
void f6 (void) { printf("%i\n", 6); }
void f7 (void) { printf("%i\n", 7); }
void f8 (void) { printf("%i\n", 8); }
void f9 (void) { printf("%i\n", 9); }

typedef void(*void_fp)(void);

struct action
{
  int x;
  void_fp fun;
};

// Array with an empty final element
const struct action fp_tbl[5] = {{1, f2}, {2, f3} ,{3, f4},};

// There is a basic check that excludes all functions that aren't used anywhere
// This ensures that check can't work in this example
const void_fp fp_all[] = {f1, f2 ,f3, f4, f5 ,f6, f7, f8, f9};

void func(int i)
{
  const void_fp fp = fp_tbl[i].fun;
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
