extern "C" void __CPROVER_assert(bool, const char *);
// The MSVC STL's layout: N5008 [support.initlist]/1 leaves it to the
// implementation; clang accepts a begin and an end pointer
namespace std
{
typedef decltype(sizeof(0)) size_t;
template <class E>
class initializer_list
{
  const E *first_;
  const E *last_;

public:
  constexpr initializer_list() noexcept : first_(nullptr), last_(nullptr)
  {
  }
  constexpr const E *begin() const noexcept
  {
    return first_;
  }
  constexpr const E *end() const noexcept
  {
    return last_;
  }
  constexpr size_t size() const noexcept
  {
    return static_cast<size_t>(last_ - first_);
  }
};
} // namespace std
int sum(std::initializer_list<int> l)
{
  int s = 0;
  for(const int *p = l.begin(); p != l.end(); ++p)
    s += *p;
  return s;
}
int main()
{
  // N5008 [dcl.init.list]/5: the object refers to a backing array of three
  // elements
  std::initializer_list<int> l = {1, 2, 3};
  __CPROVER_assert(l.size() == 3 && sum(l) == 6, "begin/end layout");
  __CPROVER_assert(sum({4, 5}) == 9, "argument");
  __CPROVER_assert(l.size() == 2, "WRONG (must FAIL)");
  return 0;
}
