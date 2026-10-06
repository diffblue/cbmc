// N5008 [temp.param]/17, [temp.local]/7: the default template arguments of
// all declarations of a template are merged; a default argument naming an
// earlier parameter of a declaration (`class = C') refers to that parameter
// in a definition whose parameters are unnamed or named differently
extern "C" void __CPROVER_assert(bool, const char *);
template <class C, class = C>
struct S;
template <class, class>
struct S
{
  int k;
};
template <class T>
struct traits
{
  typedef T type;
};
template <class A, class B = typename traits<A>::type>
struct P;
template <class B, class A>
struct P
{
  B b;
  A a;
};
template <class C, class D = C *>
struct Q;
template <class X, class Y>
struct Q
{
  Y y;
};
int main()
{
  S<char> s;
  s.k = 1;
  __CPROVER_assert(s.k == 1, "unnamed parameters in the definition");
  P<char> p;
  __CPROVER_assert(sizeof(p.a) == 1, "swapped parameter names");
  int i = 3;
  Q<int> q;
  q.y = &i;
  __CPROVER_assert(*q.y == 3, "renamed parameter in a compound type");
  __CPROVER_assert(s.k == 0, "WRONG (must FAIL)");
}
