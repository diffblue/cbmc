// N5008 [temp.explicit]/1, /10: an explicit instantiation definition of a
// member function template specialization instantiates its definition
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
int main()
{
  box<char> b;
  b.v = 0;
  __CPROVER_assert(b.put(5L) == 1 && b.v == 5, "explicitly instantiated");
  __CPROVER_assert(b.v == 0, "WRONG (must FAIL)");
}
