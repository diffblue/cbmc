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

// There is a basic check that excludes all functions that aren't used anywhere
// This ensures that check can't work in this example
const void_fp fp_all[] = {f1, f2 ,f3, f4, f5 ,f6, f7, f8, f9};

const int const_number=4;

void func()
{
  // Here we 'lose' const-ness except it is a copy so we shouldn't care
  int non_const_number=const_number;
  const void_fp fp = f2;


  // Here also we lose const-ness except it is a copy of pointer so we
  // shouldn't care
  const void_fp * const p2fp = &f2;
  const void_fp * p2fp_non_const = &p2fp;

  fp();
}

int main()
{
  func();

  return 0;
}
