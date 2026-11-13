// N5008 [temp.variadic]/5, [temp.mem]/1: the out-of-class definition
// `template <class T> template <class... R> int table<T>::construct(R &&...)'
// defines the member for every pack length.  With an empty pack the
// instance has no parameter, the definition one (the pack), and the parameter
// count check rejected the definition: construct<>() had no body (libc++'s
// __hash_table::__construct_node_hash, behind unordered_set::insert).
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct table
{
  template <class... R>
  int construct(R &&...r);
};
template <class T>
template <class... R>
int table<T>::construct(R &&...r)
{
  return sizeof...(R);
}
struct plain
{
  template <class... R>
  int construct(R &&...r);
};
template <class... R>
int plain::construct(R &&...r)
{
  return sizeof...(R);
}
int main()
{
  table<int> t;
  plain p;
  __CPROVER_assert(t.construct() == 0, "class template, empty");
  __CPROVER_assert(t.construct(1) == 1, "class template, one");
  __CPROVER_assert(t.construct(1, 2) == 2, "class template, two");
  __CPROVER_assert(p.construct() == 0, "class, empty");
  __CPROVER_assert(p.construct(1, 2) == 2, "class, two");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
