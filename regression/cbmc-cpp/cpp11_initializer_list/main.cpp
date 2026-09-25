// C++11 auto with braced-init-list
int main()
{
  auto il = {1, 2, 3};
  int sum = 0;
  for(auto x : il)
    sum += x;
  __CPROVER_assert(sum == 6, "initializer_list sum");
  return 0;
}
