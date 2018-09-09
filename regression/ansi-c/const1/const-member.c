struct S
{
  int field;
};

int main()
{
  const struct S *const_struct_ptr;

  // should fail, as struct is const
  const_struct_ptr->field = 123;
}
