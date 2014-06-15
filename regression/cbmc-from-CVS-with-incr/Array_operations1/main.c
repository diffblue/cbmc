void testA()
{
  char arrayA1[100], arrayA2[100];
  _Bool cmp;
  int index;
  
  cmp=__CPROVER_array_equal(arrayA1, arrayA2);

  __CPROVER_assume(index>=0 && index<100);
  __CPROVER_assume(cmp);

  __CPROVER_assert(arrayA1[index]==arrayA2[index], "testA arrays are equal");
}

void testB()
{
  char arrayB1[100], arrayB2[100];

  arrayB2[10]=11;  
  __CPROVER_array_copy(arrayB1, arrayB2);

  __CPROVER_assert(arrayB1[10]==11, "arrayB1[10] is OK");
}

void testC()
{
  char arrayC1[100];
  __CPROVER_array_set(arrayC1, 111);
  __CPROVER_assert(arrayC1[44]==111, "arrayC1[44] is OK");
}

int main()
{
  testA();
  testB();
  testC();
}
