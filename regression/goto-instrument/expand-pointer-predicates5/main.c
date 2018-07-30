struct bar
{
  int w;
  int x;
  int y;
  int z;
};

int main()
{
  struct bar s;
  s.z = 5;
  int *x_pointer = &(s.x);
  __CPROVER_assert(__CPROVER_points_to_valid_memory(x_pointer, 3 * sizeof(int)),
                   "Variable length assert");
  assert(x_pointer[2] == 5);
  return 0;
}
