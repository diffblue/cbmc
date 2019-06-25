static int myVal = 3;
static int myVal2 = 4;

void method2()
{
  __CPROVER_assert(myVal == 3, "method2 myVal");
  __CPROVER_assert(myVal2 == 4, "method2 myVal2");
}
