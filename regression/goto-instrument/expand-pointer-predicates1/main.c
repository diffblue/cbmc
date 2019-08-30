int main()
{
  int *x;
  __CPROVER_assume(__CPROVER_points_to_valid_memory(x));
  *x = 1;
  return 0;
}
