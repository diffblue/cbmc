// C++11 cast expressions as postfix-expressions
struct Base
{
  virtual ~Base()
  {
  }
};
struct Derived : Base
{
  int val;
};

int main()
{
  int x = 42;
  double d = static_cast<double>(x);
  const int *cp = &x;
  int *p = const_cast<int *>(cp);
  long l = reinterpret_cast<long>(p);
  Derived der;
  Base *bp = static_cast<Base *>(&der);
  return 0;
}
