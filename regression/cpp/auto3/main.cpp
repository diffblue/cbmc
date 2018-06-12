int main()
{
#ifndef _MSC_VER
  // should yield a parse error unless in C++11 (or later) mode
  auto x = 42;
  const auto y = 42;
  const auto &z = y;
#else
  intentionally invalid
#endif
}
