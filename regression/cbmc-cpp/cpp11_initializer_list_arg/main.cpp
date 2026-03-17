// C++11 initializer_list as function argument
namespace std
{
template <class T>
class initializer_list
{
  const T *_begin;
  unsigned long _size;

public:
  initializer_list() : _begin(0), _size(0)
  {
  }
  const T *begin() const
  {
    return _begin;
  }
  const T *end() const
  {
    return _begin + _size;
  }
  unsigned long size() const
  {
    return _size;
  }
};
} // namespace std

int sum(std::initializer_list<int> il)
{
  int s = 0;
  for(const int *p = il.begin(); p != il.end(); ++p)
    s += *p;
  return s;
}

int main()
{
  int r = sum({1, 2, 3});
  __CPROVER_assert(r == 6, "init list sum");
  return 0;
}
