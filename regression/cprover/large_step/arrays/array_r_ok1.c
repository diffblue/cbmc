int main()
{
  unsigned char array[10];
  __CPROVER_assert(__CPROVER_r_ok(array, 10), "property 1");
  unsigned char *array_ptr = array;
  __CPROVER_assert(__CPROVER_r_ok(array_ptr, 10), "property 2");
}
