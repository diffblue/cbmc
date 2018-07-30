int main()
{
  int *x;
  __CPROVER_assume(__CPROVER_points_to_valid_memory(x, sizeof(int)));
  __CPROVER_assert(__CPROVER_points_to_valid_memory(x, sizeof(int)),
                   "Assert matches assume");
  return 0;
}
