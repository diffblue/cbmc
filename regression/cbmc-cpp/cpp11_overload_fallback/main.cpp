// Test that overload resolution falls back to non-template candidates
// when template instantiation produces candidates that don't match.
#include <cassert>

template <typename T>
struct Container
{
  typedef unsigned long size_type;

  T &insert(size_type pos, const T &val)
  {
    data[pos] = val;
    return data[pos];
  }
  T &insert(size_type pos, size_type count, const T &val)
  {
    data[pos] = val;
    return data[pos];
  }

  template <typename Iter>
  void insert(T *p, Iter beg, Iter end)
  {
  }

  T data[10];
};

int main()
{
  Container<int> c;
  c.data[0] = 0;
  c.insert(0, 42);
  assert(c.data[0] == 42);
  return 0;
}
