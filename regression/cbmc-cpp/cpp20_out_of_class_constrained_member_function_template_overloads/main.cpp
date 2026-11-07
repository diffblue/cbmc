// N5008 [temp.over.link]/6, [temp.mem]/1: the two member function
// templates f differ only in their requires-clauses; each out-of-class
// definition defines the declaration with the equivalent template-head.
// The second definition renames the template parameters ([temp.over.link]/6:
// equivalent up to renaming).  The definitions were attached by name,
// parameter count and cv-qualification alone, so s.f(1.0) ran the first
// definition.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
concept small = sizeof(T) <= 4;
template <class T>
concept big = sizeof(T) > 4;
template <class T>
  requires small<T>
struct S
{
  template <class U>
    requires small<U>
  int f(U);
  template <class U>
    requires big<U>
  int f(U);
};
template <class T>
  requires small<T>
template <class U>
  requires small<U>
int S<T>::f(U)
{
  return 1;
}
template <class Q>
  requires small<Q>
template <class V>
  requires big<V>
int S<Q>::f(V)
{
  return 2;
}
int main()
{
  S<int> s;
  __CPROVER_assert(s.f('a') == 1, "small");
  __CPROVER_assert(s.f(1.0) == 2, "big");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
