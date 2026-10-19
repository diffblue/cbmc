extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [class.mfct]/1, [temp.mem]/1: an out-of-class definition defines
// a member of the class it names; the definition of another class's
// same-named member, however many template parameters it has, is not a
// candidate
template <class A, class B, class C, class D, class E>
struct other
{
  int v = 0;
  void operator=(int);
};
template <class A, class B, class C, class D, class E>
void other<A, B, C, D, E>::operator=(int)
{
  v = 99;
}
template <class>
struct fn;
template <class R, class... A>
struct fn<R(A...)>
{
  int which = 0;
  template <class F, class = int>
  void operator=(F &&);
};
template <class R, class... A>
template <class F, class>
void fn<R(A...)>::operator=(F &&)
{
  which = 4;
}
int main()
{
  fn<int(const int &)> g;
  g = [](const int &x) { return x; };
  __CPROVER_assert(g.which == 4, "assignment operator template defined");
  __CPROVER_assert(g.which == 0, "WRONG (must FAIL)");
  return 0;
}
