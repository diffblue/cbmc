extern "C" void __CPROVER_assert(bool, const char *);
struct wide
{
  unsigned long long w;
  // N5008 [over.match.copy]/1.2, [over.match.conv]/1: an explicit conversion
  // function template is a candidate in a direct-initialization only (the
  // MSVC STL's _Base128::operator _Ty)
  template <class T>
  constexpr explicit operator T() const noexcept
  {
    return static_cast<T>(w);
  }
};
int pick(int)
{
  return 1;
}
int pick(...)
{
  return 2;
}
int main()
{
  wide b{7};
  __CPROVER_assert(
    !__is_convertible(wide, int) && __is_constructible(int, wide) &&
      static_cast<int>(b) == 7 && pick(b) == 2,
    "explicit only when direct");
  __CPROVER_assert(pick(b) == 1, "WRONG (must FAIL)");
  return 0;
}
