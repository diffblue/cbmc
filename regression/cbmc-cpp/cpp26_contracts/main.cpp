// C++26 language features require GCC 12+
#if !defined(__GNUC__) || __GNUC__ >= 12
int add(int a, int b) pre(a > 0) pre(b > 0) post(r : r > 0)
{
  return a + b;
}

int main()
{
  int x = add(1, 2);
  __CPROVER_assert(x == 3, "add");
}

#else
int main()
{
}
#endif
