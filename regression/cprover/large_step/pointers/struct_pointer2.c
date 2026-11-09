struct my_struct
{
  int data;
};

int main()
{
  struct my_struct my_struct;
  struct my_struct *my_struct_ptr = &my_struct;

  my_struct_ptr->data = 123;
  __CPROVER_assert(my_struct.data == 123, "property 1"); // should pass

  return 0;
}
