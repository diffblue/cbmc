void test_equal()
{
  char array1[100], array2[100];
  _Bool cmp;
  int index;

  cmp = __CPROVER_array_equal(array1, array2);

  __CPROVER_assume(index >= 0 && index < 100);
  __CPROVER_assume(cmp);

  __CPROVER_assert(array1[index] == array2[index], "arrays are equal");
}

void test_copy()
{
  char array1[100], array2[100], array3[90];

  array2[10] = 11;
  array3[10] = 11;
  array2[99] = 42;
  __CPROVER_array_copy(array1, array2);

  __CPROVER_assert(array1[10] == 11, "array1[10] is OK");
  __CPROVER_assert(array1[99] == 42, "array1[99] is OK");

  __CPROVER_array_copy(array1, array3);
  __CPROVER_assert(array1[10] == 11, "array1[10] is OK");
  __CPROVER_assert(array1[99] == 42, "expected to fail");
}

void test_replace()
{
  char array1[100], array2[90];

  array1[99] = 42;
  array2[10] = 11;
  __CPROVER_array_replace(array1, array2);

  __CPROVER_assert(array1[10] == 11, "array1[10] is OK");
  __CPROVER_assert(array1[99] == 42, "array1[99] is OK");
}

void test_set()
{
  char array1[100];
  __CPROVER_array_set(array1, 111);
  __CPROVER_assert(array1[44] == 111, "array1[44] is OK");
}

int main()
{
  test_equal();
  test_copy();
  test_replace();
  test_set();
}
