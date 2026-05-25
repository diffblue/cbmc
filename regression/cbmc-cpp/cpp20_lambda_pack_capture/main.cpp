// C++20 lambda init-capture with pack expansion
template <typename... Args>
auto make_sum_lambda(Args... args)
{
  return [... captured = args]() { return (captured + ...); };
}
int main()
{
  auto f = make_sum_lambda(1, 2, 3);
  __CPROVER_assert(f() == 6, "init capture pack");
  return 0;
}
