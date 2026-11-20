// N5008 [intro.object]/10: an empty [[no_unique_address]] member and a
// later member of the same type have distinct addresses.  GCC and Clang
// (Itanium C++ ABI 2.4 II) allocate in declaration order: e takes offset
// 0, and x, which would conflict there, moves to offset 1.
extern "C" void __CPROVER_assert(bool, const char *);
struct E
{
};
struct L
{
  [[no_unique_address]] E e;
  E x;
  int i;
};
int main()
{
  L l;
  __CPROVER_assert((char *)&l.e != (char *)&l.x, "distinct addresses");
  __CPROVER_assert((char *)&l.e == (char *)&l, "e at offset 0");
  __CPROVER_assert((char *)&l.x == (char *)&l + 1, "x at offset 1");
  __CPROVER_assert(sizeof(L) == 8, "size");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
