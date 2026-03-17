// C++20 floating-point non-type template parameter
template <double V>
struct Const
{
  static constexpr double value = V;
};

int main()
{
  __CPROVER_assert(Const<3.14>::value > 3.0, "float nttp");
  return 0;
}
