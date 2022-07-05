int main()
{
  __CPROVER_bool bool_array[100];
  unsigned int index;
  __CPROVER_assume(index < 10000);
  bool_array[index] = 1;
  __CPROVER_assert(bool_array[index], "Array condition");
  __CPROVER_assert(!bool_array[index], "Array condition");
}
