extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct iter
{
  T *ptr;
};
template <class T>
struct vec
{
  T *first;
  int size;
};
// N5008 [expr.add]/1, [expr.sub]/1, [temp.inst]/2: `v.first[b]' needs the
// complete type iter<K>, so iter<K> is instantiated although it was named
// only as a template argument so far (the MSVC STL's
// std::unordered_map::_Find_last)
template <class K>
struct table
{
  using iterator = iter<K>;
  vec<iterator> v;
  int count() const
  {
    int n = 0;
    for(int b = 0; b < v.size; ++b)
      n += v.first[b].ptr != nullptr;
    return n;
  }
};
int main()
{
  table<int> t;
  t.v.first = nullptr;
  t.v.size = 0;
  __CPROVER_assert(t.count() == 0, "empty table");
  __CPROVER_assert(t.count() != 0, "WRONG (must FAIL)");
  return 0;
}
