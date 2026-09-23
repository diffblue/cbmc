struct my_struct
{
  int data;
};

int main()
{
  struct my_struct *my_struct_ptr; // not constrained
  // __CPROVER_assume(!__CPROVER_same_object(my_struct_ptr, &my_struct_ptr));
  my_struct_ptr->data = 123;
  int my_struct_data = my_struct_ptr->data;
  __CPROVER_assert(my_struct_data == 123, "property 1"); // should pass
  return 0;
}
