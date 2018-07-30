int main()
{
  int x;
  int *y = &x;
  __CPROVER_assert(__CPROVER_points_to_valid_memory(y),
                   "Assert works on &");
  return 0;
}
