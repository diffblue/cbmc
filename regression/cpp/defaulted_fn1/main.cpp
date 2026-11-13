// C++11 defaulted special member functions
struct S
{
  S() = default;
  S(const S &) = default;
  S &operator=(const S &) = default;
};

struct T
{
  explicit T() = default;
};

int main()
{
  S s;
  T t;
  return 0;
}
