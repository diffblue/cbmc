struct A
{
  int a;
  int b;
  union
  {
    int x;
  } u;
};

int main()
{
  struct A my_struct = {0};
  __CPROVER_assert(my_struct.a == 0, "Must be true");
  return 0;
}
