// C++11 nullptr
void f(int *p)
{
  __CPROVER_assert(p == nullptr, "is null");
}
int main()
{
  f(nullptr);
  return 0;
}
