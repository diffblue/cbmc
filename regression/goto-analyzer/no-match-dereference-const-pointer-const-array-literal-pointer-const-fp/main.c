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

typedef struct fp_container
{
  int x;
  const void_fp* const fp_tbl[3];
} fp_container;



void func()
{
  void_fp f2meta = &f2;
  void_fp f3meta = &f3;
  void_fp f4meta = &f4;

  void_fp f5meta = &f5;
  void_fp f6meta = &f6;
  void_fp f7meta = &f7;

  const fp_container container = { .x = 4, .fp_tbl = {&f2meta ,&f3meta, &f4meta} };
  const fp_container container2 = { .x = 5, .fp_tbl = {&f5meta ,&f6meta, &f7meta} };

  f3meta = &f5;
  // Illegal:
  // container.fp_tbl = alternatate_fp_tbl;
  // container.fp_tbl[1] = f4;
  const fp_container * const container_ptr=&container;
  //container_ptr=&container2;
  (*container_ptr->fp_tbl[1])();
}

int main()
{
  func();
}
