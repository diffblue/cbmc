// Test class template declared with a qualified name (namespace::class)
// as used by GCC's libstdc++ for inline namespace __cxx11.
namespace outer
{
inline namespace inner
{
}
template <typename T>
class inner::Foo
{
public:
  typedef T value_type;
  T val;
};
} // namespace outer

int main()
{
  outer::Foo<int> f;
  f.val = 42;
  outer::inner::Foo<char> g;
  g.val = 'x';
  return 0;
}
