// C++20 abbreviated function template
int add(auto a, auto b)
{
  return a + b;
}

int main()
{
  int r = add(1, 2);
  __CPROVER_assert(r == 3, "abbreviated fn tmpl");
  return 0;
}
