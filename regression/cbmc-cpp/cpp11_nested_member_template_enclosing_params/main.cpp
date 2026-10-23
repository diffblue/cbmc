extern "C" void __CPROVER_assert(bool, const char *);
template <class T, int N>
struct Outer
{
  template <class U>
  struct Inner
  {
    Inner(U init);
    T add(U a, U b) const;
    static int twice(int k);
    T v;
  };
};
template <class T, int N>
template <class U>
Outer<T, N>::Inner<U>::Inner(U init) : v(init + N)
{
}
template <class T, int N>
template <class U>
T Outer<T, N>::Inner<U>::add(U x, U y) const
{
  return v + x + y;
}
template <class T, int N>
template <class U>
int Outer<T, N>::Inner<U>::twice(int k)
{
  return 2 * k + N;
}
int main()
{
  Outer<int, 10>::Inner<int> in(1);
  __CPROVER_assert(in.v == 11, "ctor defined out of line");
  __CPROVER_assert(in.add(2, 3) == 16, "const member with renamed parameters");
  __CPROVER_assert(Outer<int, 10>::Inner<int>::twice(4) == 18, "static member");
  return 0;
}
