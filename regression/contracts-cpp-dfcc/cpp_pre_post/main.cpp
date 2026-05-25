extern "C" int add(int a, int b) pre(a >= 0 && b >= 0) post(r : r == a + b)
{
  return a + b;
}

int main()
{
  int x = add(1, 2);
}
