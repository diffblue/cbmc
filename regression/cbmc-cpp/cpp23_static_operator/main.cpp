// C++23 static operator()
struct Adder
{
  static int operator()(int a, int b)
  {
    return a + b;
  }
};

int main()
{
  Adder add;
  __CPROVER_assert(add(1, 2) == 3, "static operator()");
}
