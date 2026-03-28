// C++23 language features require GCC 11+
#if !defined(__GNUC__) || __GNUC__ >= 11
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

#else
int main()
{
}
#endif
