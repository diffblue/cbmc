#include <stdio.h>

void handler_a(void)
{
  printf("A\n");
}
void handler_b(void)
{
  printf("B\n");
}
void handler_c(void)
{
  printf("C\n");
}

typedef void (*handler_func)(void);

// There is a basic check that excludes all functions that aren't used anywhere
// This ensures that check can't work in this example
const handler_func fp_all[] = {handler_a, handler_b, handler_c};

// const struct with function pointer member: the member is treated as const
// because the struct is const
struct handler_ops
{
  handler_func on_event;
  int priority;
};

void test_const_struct(void)
{
  const struct handler_ops ops = {handler_b, 10};
  ops.on_event(); // Should resolve to handler_b
}

int main(void)
{
  test_const_struct();
  return 0;
}
