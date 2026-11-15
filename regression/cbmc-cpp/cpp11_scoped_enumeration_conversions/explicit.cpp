extern "C" void __CPROVER_assert(bool, const char *);
enum class E : unsigned char
{
  a = 0,
  b = 200
};
int main()
{
  E e = E::b;
  int i = static_cast<int>(e);
  bool t = static_cast<bool>(e);
  double d = static_cast<double>(e);
  int c = (int)e;
  int f = int(e);
  __CPROVER_assert(
    i == 200 && t && d == 200.0 && c == 200 && f == 200,
    "explicit conversions");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
