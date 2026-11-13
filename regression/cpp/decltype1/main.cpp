// C++11 decltype and noexcept expressions
struct S
{
  static int value;
};
int S::value = 42;

int main()
{
  decltype(S::value) x = 5;
  bool b = noexcept(x + 1);
  return 0;
}
