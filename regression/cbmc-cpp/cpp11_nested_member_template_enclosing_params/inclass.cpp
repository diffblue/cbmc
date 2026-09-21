extern "C" void __CPROVER_assert(bool, const char *);
template <class T, int N>
struct Outer
{
  struct Plain
  {
    static int f(int k)
    {
      return k + N;
    }
  };
  template <class U>
  struct Inner
  {
    static int g(int k)
    {
      return k + N;
    }
    static T h(U u)
    {
      return T(u) + 1;
    }
  };
  template <class U>
  static int direct(U u)
  {
    return u + N;
  }
};
int main()
{
  __CPROVER_assert(
    Outer<int, 10>::Plain::f(1) == 11, "nested plain struct sees N");
  __CPROVER_assert(
    Outer<int, 10>::direct(1) == 11, "member function template sees N");
  __CPROVER_assert(
    Outer<int, 10>::Inner<int>::h(1) == 2, "nested template sees T");
  __CPROVER_assert(
    Outer<int, 10>::Inner<int>::g(1) == 11, "nested template sees N");
  return 0;
}
