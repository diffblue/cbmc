// Braced-init-list should call the default constructor for non-POD types
struct S
{
  S() = default;
};
constexpr S s1{};

struct T
{
  explicit T() = default;
};
constexpr T t1{};

// Braced-init-list with arguments
struct U
{
  int x;
  U(int v) : x(v)
  {
  }
};
U u1{42};

int main()
{
  return 0;
}
