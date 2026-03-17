int main()
{
  int arr[] = {1, 2, 3};
  auto p = auto(arr); // decays to int*
  __CPROVER_assert(*p == 1, "decay copy");
}
