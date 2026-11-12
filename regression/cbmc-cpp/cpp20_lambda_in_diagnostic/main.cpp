// A C++ lambda-expression has the id of the mathematical lambda_exprt;
// printing the constraint below in a diagnostic failed an invariant of
// expr2c ("lambda must have two operands").  kind<int> is ill-formed: its
// lambda's static_assert fails (g++ 13 and clang++ 18 reject the program).
template <class T>
constexpr auto kind = []
{
  static_assert(sizeof(T) == 0, "primary template of kind");
  return 1;
}();
template <class T, class = void>
struct fmt
{
  static constexpr int v = 0;
};
template <class T>
  requires(kind<T> != 2)
struct fmt<T, int>
{
  static constexpr int v = 1;
};
int main()
{
  return fmt<int, int>::v;
}
