struct my_struct
{
  int x, y;
} S = {1, 2};

int main()
{
  int *p = &S.y;
  int my_struct_data = *p;
  __CPROVER_assert(my_struct_data == 2, "property 1"); // should pass
  return 0;
}
