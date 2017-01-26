#include <stdio.h>

void f1 (void) { printf("%i", 1); }
void f2 (void) { printf("%i", 2); }
void f3 (void) { printf("%i", 3); }
void f4 (void) { printf("%i", 4); }
void f5 (void) { printf("%i", 5); }
void f6 (void) { printf("%i", 6); }
void f7 (void) { printf("%i", 7); }
void f8 (void) { printf("%i", 8); }
void f9 (void) { printf("%i", 9); }

typedef void(*void_fp)(void);

// There is a basic check that excludes all functions that aren't used anywhere
// This ensures that check can't work in this example
const void_fp fp_all[] = {f1, f2 ,f3, f4, f5 ,f6, f7, f8, f9};

void func()
{
  void_fp fp = f2;
  void_fp fp2 = fp;
  fp2();
}

void main()
{
  func();
}
