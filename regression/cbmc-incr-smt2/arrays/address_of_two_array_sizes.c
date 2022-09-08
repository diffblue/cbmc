int main()
{
  int example_array1[10000];
  char example_array2[20000];
  void *foo;
  __CPROVER_bool choice = nondet___CPROVER_bool();
  if(choice)
    foo = example_array1;
  else
    foo = example_array2;
  __CPROVER_assert(
    foo != example_array1 || __CPROVER_OBJECT_SIZE(foo) == 40000,
    "Array condition 1");
  __CPROVER_assert(__CPROVER_OBJECT_SIZE(foo) == 40000, "Array condition 2");
  __CPROVER_assert(
    foo != example_array2 || __CPROVER_OBJECT_SIZE(foo) == 20000,
    "Array condition 3");
  __CPROVER_assert(__CPROVER_OBJECT_SIZE(foo) == 20000, "Array condition 4");
}
