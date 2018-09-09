struct S
{
  const int field;
};

int main()
{
  struct S *const_struct_ptr;

  // should fail, as field is const
  const_struct_ptr->field = 123;
}
