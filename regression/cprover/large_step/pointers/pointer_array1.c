int some_int = 123;
void *ptr_array[10] = {&some_int};

int main()
{
  __CPROVER_assert(ptr_array[0] == &some_int, "property 1");

  void **array_pointer = ptr_array;

  __CPROVER_assert(array_pointer[0] == &some_int, "property 2");
  __CPROVER_assert(*((int *)(array_pointer[0])) == 123, "property 3");
}
