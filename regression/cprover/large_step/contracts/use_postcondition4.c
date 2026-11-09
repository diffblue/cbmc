int global1, global2;

void callee()
  // clang-format off
  __CPROVER_ensures(global2 == __CPROVER_old(global1))
  __CPROVER_assigns(global1, global2)
// clang-format on
{
  global2 = global1;
  global1 = 20;
}

int main()
{
  global1 = 123;
  callee();
  __CPROVER_assert(global2 == 123, "property 1");
  return 0;
}
