// Template constructors should not crash overload resolution
// when they appear alongside non-template constructors.

namespace std
{
typedef unsigned long size_t;
template <typename T>
struct allocator
{
};
template <typename T>
struct char_traits
{
};

template <
  typename _CharT,
  typename _Traits = char_traits<_CharT>,
  typename _Alloc = allocator<_CharT>>
class basic_string
{
public:
  basic_string(size_t __n, _CharT __c)
  {
  }

  template <typename _InputIterator>
  basic_string(_InputIterator __beg, _InputIterator __end)
  {
  }
};

typedef basic_string<char> string;
} // namespace std

int main()
{
  std::string s(3, '-');
  return 0;
}
