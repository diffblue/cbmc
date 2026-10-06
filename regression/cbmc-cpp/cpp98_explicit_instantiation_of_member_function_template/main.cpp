// N5008 [temp.explicit]/1, /10, /12: an explicit instantiation definition
// of a member function template specialization instantiates its
// definition; an explicit instantiation declaration (C++11 `extern
// template') only suppresses implicit instantiation in favour of it
extern "C" void __CPROVER_assert(bool, const char *);
template <class C>
struct box
{
  C v;
  template <class T>
  int put(T t);
};
template <class C>
template <class T>
int box<C>::put(T t)
{
  v = C(t);
  return 1;
}
template int box<char>::put(long);
#if __cplusplus >= 201103L
extern template int box<int>::put(short);
#endif
int main()
{
  box<char> b;
  b.v = 0;
  __CPROVER_assert(b.put(5L) == 1 && b.v == 5, "explicitly instantiated");
#if __cplusplus >= 201103L
  box<int> i;
  __CPROVER_assert(i.put(short(6)) == 1 && i.v == 6, "extern template");
#endif
  __CPROVER_assert(b.v == 0, "WRONG (must FAIL)");
}
#if __cplusplus >= 201103L
template int box<int>::put(short);
#endif
