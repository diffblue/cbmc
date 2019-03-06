int main()
{
  int *r;
  __CPROVER_points_to_valid_memory(r, "huh?");
}
