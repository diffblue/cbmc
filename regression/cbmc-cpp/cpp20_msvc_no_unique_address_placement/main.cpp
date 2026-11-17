// Visual Studio gives an empty member declared [[msvc::no_unique_address]]
// zero size (N5008 [intro.object]/8: implementation-defined).  The
// expected offsets are those of clang++ 18 for x86_64-pc-windows-msvc,
// which follows the Microsoft C++ ABI (-fdump-record-layouts): it tries
// offset 0 and then the following offsets, instead of the Itanium data
// size.
extern "C" void __CPROVER_assert(bool, const char *);
struct E
{
};
struct alignas(8) A8
{
};
struct R1
{
  E x;
  int i;
  [[msvc::no_unique_address]] E e;
};
struct R2
{
  E x;
  [[msvc::no_unique_address]] E e;
  int i;
};
struct Q
{
  char c;
  [[msvc::no_unique_address]] A8 a;
  char d;
};
int main()
{
  R1 r1;
  R2 r2;
  __CPROVER_assert(
    sizeof(R1) == 8 && (char *)&r1.e - (char *)&r1 == 1, "R1: e at 1");
  __CPROVER_assert(
    sizeof(R2) == 8 && (char *)&r2.e - (char *)&r2 == 1, "R2: e at 1");
  __CPROVER_assert(
    sizeof(Q) == 8 && __builtin_offsetof(Q, d) == 1, "Q: d at 1");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
