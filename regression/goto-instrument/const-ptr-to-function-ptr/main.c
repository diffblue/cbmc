#include <stdio.h>

void f1(void)
{
  printf("1\n");
}
void f2(void)
{
  printf("2\n");
}
void f3(void)
{
  printf("3\n");
}

typedef void (*func_ptr)(void);

// Ensure all functions are referenced so the basic exclusion check can't
// eliminate them
const func_ptr fp_all[] = {f1, f2, f3};

// const pointer to struct with function pointer member
struct ops
{
  func_ptr handler;
  int id;
};

void test_const_ptr_to_struct(void)
{
  struct ops s = {f2, 10};
  const struct ops *const ptr = &s;
  ptr->handler(); // Should resolve to f2
}

int main(void)
{
  test_const_ptr_to_struct();
  return 0;
}
