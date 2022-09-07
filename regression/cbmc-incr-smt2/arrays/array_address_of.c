int main()
{
  int example_array1[10000];
  int example_array2[10000];
  int *foo;
  int choice;
  if(choice)
    foo = example_array1;
  else
    foo = example_array2;
  __CPROVER_assert(__CPROVER_OBJECT_SIZE(foo) == 40000, "Array condition 1");
  __CPROVER_assert(__CPROVER_OBJECT_SIZE(foo) == 40001, "Array condition 2");
}
