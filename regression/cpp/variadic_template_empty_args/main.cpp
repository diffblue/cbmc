// Test that variadic template aliases can be instantiated with zero arguments.
// This pattern is used by std::__void_t in GCC's standard library headers.

template <typename...>
using __void_t = void;

template <typename T, typename = __void_t<>>
struct test
{
  typedef int type;
};

int main()
{
  test<int>::type x = 0;
  return x;
}
