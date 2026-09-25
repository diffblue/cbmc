// Template constructor with SFINAE constraint (anonymous type parameter)
namespace std
{
template <bool B, typename T = void>
struct enable_if
{
};
template <typename T>
struct enable_if<true, T>
{
  typedef T type;
};
} // namespace std

struct unevaluable_trait
{
};

struct duration
{
  duration()
  {
  }
  duration(const duration &)
  {
  }
  // Anonymous type parameter with default that cannot be evaluated
  template <typename Rep2, typename = typename std::enable_if<true>::type>
  explicit duration(const Rep2 &r)
  {
  }
};

typedef duration seconds;

void test()
{
  long long t = 42;
  seconds s(t);
}

int main()
{
  test();
}
