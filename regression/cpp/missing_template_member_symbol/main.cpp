// Test that uninstantiated template member function references
// don't cause crashes.
template <typename T>
struct S
{
  template <typename U>
  void f(U);
};

int main()
{
  S<int> s;
  return 0;
}
