int add(int a, int b) pre(a > 0) pre(b > 0) post(r : r > 0)
{
  return a + b;
}

int main()
{
  int x = add(1, 2);
  __CPROVER_assert(x == 3, "add");
}
