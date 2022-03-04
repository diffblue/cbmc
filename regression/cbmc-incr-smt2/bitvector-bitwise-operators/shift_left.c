int main()
{
  int starting_val = 1;
  int shifting_places;
  __CPROVER_assume(shifting_places > 0);
  __CPROVER_assume(shifting_places < 32);
  int result = starting_val << shifting_places;

  __CPROVER_assert(result > 1, "Shifted result should be greater than one");
}
