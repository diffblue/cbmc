// C++11 range-for over initializer_list
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
};
} // namespace std
int main()
{
  int s = 0;
  for(int x : {1, 2, 3})
    s += x;
  __CPROVER_assert(s == 6, "range-for init list");
  return 0;
}
