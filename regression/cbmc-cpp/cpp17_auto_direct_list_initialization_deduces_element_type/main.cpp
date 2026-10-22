extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [dcl.type.auto.deduct]/2.2.2, /4: `auto t{l}' is not
// copy-list-initialization, so T is deduced from the single element l as
// for `auto t = l' (the MSVC STL's _Unsigned128::operator<< in
// <__msvc_int128.hpp>)
struct U
{
  unsigned long w[2];
  constexpr void shl(unsigned char)
  {
    w[0] = w[0] << 1;
  }
  friend constexpr U operator<<(const U &l, int)
  {
    auto t{l};
    t.shl(1);
    return t;
  }
};
int main()
{
  U a{{1, 0}};
  U b = a << 1;
  auto c{a};
  int i = 4;
  auto j{i};
  j = j + 1;
  __CPROVER_assert(b.w[0] == 2 && c.w[0] == 1, "auto brace");
  __CPROVER_assert(j == 5 && sizeof(j) == sizeof(int), "scalar");
  __CPROVER_assert(b.w[0] == 1, "WRONG (must FAIL)");
}
