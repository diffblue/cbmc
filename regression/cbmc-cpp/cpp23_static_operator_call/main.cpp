// C++23 static operator()
struct Add
{
  static int operator()(int a, int b)
  {
    return a + b;
  }
};
int main()
{
  Add add;
  int r = add(1, 2);
  __CPROVER_assert(r == 3, "static operator()");
  return 0;
}
