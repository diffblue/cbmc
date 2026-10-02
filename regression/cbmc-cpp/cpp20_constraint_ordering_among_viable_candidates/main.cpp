extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
concept C1 = sizeof(T) > 0;
template <class T>
concept CC = C1<T> && sizeof(T) == sizeof(int);
// [over.match.best]/2.5, [temp.func.order]/8.4: the more constrained of two
// viable candidates with equivalent parameter lists is better ...
template <C1 T>
int f(T)
{
  return 1;
}
template <CC T>
int f(T)
{
  return 2;
}
// ... but constraints never remove a candidate that is viable when the more
// constrained one is not, or whose parameter list differs (libstdc++'s
// ranges::copy: the iterator overload next to the range overload)
template <C1 I>
int g(I, I)
{
  return 3;
}
template <CC R>
int g();
int main()
{
  __CPROVER_assert(f(1) == 2, "more constrained viable");
  __CPROVER_assert(f(1.0) == 1, "more constrained not viable");
  __CPROVER_assert(g(1, 2) == 3, "different parameter list");
  __CPROVER_assert(f(1) != 2, "WRONG (must FAIL)");
}
