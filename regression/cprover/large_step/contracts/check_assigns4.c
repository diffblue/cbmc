struct S
{
  int x, y;
} global;

void my_function1(void)
  // clang-format off
  __CPROVER_assigns(global) // passes
// clang-format on
{
  global.x = 10;
  global.y = 10;
}

void my_function2(void)
  // clang-format off
  __CPROVER_assigns(global.x) // passes
// clang-format on
{
  global.x = 10;
}

void my_function3(void)
  // clang-format off
  __CPROVER_assigns(global.y) // passes
// clang-format on
{
  global.y = 10;
}

void my_function4(void)
  // clang-format off
  __CPROVER_assigns(global.y) // fails
// clang-format on
{
  global.x = 10;
}
