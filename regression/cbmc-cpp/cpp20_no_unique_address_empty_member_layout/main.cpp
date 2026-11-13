// N5008 [dcl.attr.nouniqueaddr]/1, [intro.object]/8, /10: an empty member
// declared [[no_unique_address]] may have zero size and share an address
// with other subobjects, but not with one of the same type.  The offsets
// are those of the Itanium C++ ABI (GCC, Clang).  Xcode 26's basic_string
// has such a member in __short.
#include <cstddef>
extern "C" void __CPROVER_assert(bool, const char *);
struct E
{
};
struct F
{
};
struct S1
{
  char d[3];
  [[no_unique_address]] E e;
  char c;
};
struct S2
{
  [[no_unique_address]] E e;
  int i;
};
struct S3
{
  [[no_unique_address]] E a;
  [[no_unique_address]] E b;
  int i;
};
struct S4
{
  [[no_unique_address]] E a;
  [[no_unique_address]] F b;
  int i;
};
struct S5
{
  [[no_unique_address]] E e;
};
struct S6
{
  E x;
  [[no_unique_address]] E e;
  int i;
};
struct S9 : E
{
  [[no_unique_address]] E e;
  int i;
};
struct S10
{
  char c;
  [[no_unique_address]] E a, b, x;
};
// Itanium C++ ABI 2.4 II.3: offset 0, else the data size of the members
// before it, then multiples of the alignment
struct R1
{
  E x;
  int i;
  [[no_unique_address]] E e;
};
struct R2
{
  E x;
  [[no_unique_address]] E e;
  int i;
};
struct BigArr
{
  E arr[100];
  [[no_unique_address]] E e;
};
#define OFF(s, m) ((char *)&s.m - (char *)&s)
int main()
{
  S1 s1;
  S2 s2;
  S3 s3;
  S4 s4;
  S6 s6;
  S9 s9;
  S10 s10;
  s1.c = 'c';
  s1.e = E{};
  E copy = s1.e;
  __CPROVER_assert(
    sizeof(S1) == 4 && OFF(s1, e) == 0 && offsetof(S1, c) == 3, "S1");
  __CPROVER_assert(s1.c == 'c', "storing the member writes nothing");
  __CPROVER_assert(sizeof(S2) == 4 && OFF(s2, e) == 0, "S2");
  __CPROVER_assert(sizeof(S3) == 4 && OFF(s3, a) == 0 && OFF(s3, b) == 1, "S3");
  __CPROVER_assert(sizeof(S4) == 4 && OFF(s4, a) == 0 && OFF(s4, b) == 0, "S4");
  __CPROVER_assert(sizeof(S5) == 1, "S5");
  __CPROVER_assert(sizeof(S6) == 8 && OFF(s6, e) == 1, "S6");
  __CPROVER_assert(sizeof(S9) == 4 && OFF(s9, e) == 1, "S9");
  __CPROVER_assert(sizeof(S10) == 3 && OFF(s10, x) == 2, "S10");
  __CPROVER_assert(sizeof(s1.e) == 1, "sizeof the member");
  R1 r1;
  R2 r2;
  BigArr b;
  __CPROVER_assert(sizeof(R1) == 12 && OFF(r1, e) == 8, "R1");
  __CPROVER_assert(sizeof(R2) == 8 && OFF(r2, e) == 1, "R2");
  __CPROVER_assert(sizeof(BigArr) == 101 && OFF(b, e) == 100, "BigArr");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
