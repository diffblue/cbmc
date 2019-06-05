static int myVal = 3;
static int myVal2 = 4;

void method1()
{
  __CPROVER_assert(myVal == 3, "method1 myVal");
  __CPROVER_assert(myVal2 == 4, "method1 myVal2");
}
