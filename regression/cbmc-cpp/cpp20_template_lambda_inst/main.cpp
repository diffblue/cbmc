// C++20 template lambda instantiation
int main()
{
  auto f = []<typename T>(T x) { return x + 1; };
  int r = f(41);
  __CPROVER_assert(r == 42, "template lambda inst");
  return 0;
}
