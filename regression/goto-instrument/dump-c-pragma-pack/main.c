#pragma pack(push, 1)
struct A
{
  char c;
  int i;
};
#pragma pack(pop)

#pragma pack(push, 2)
struct B
{
  char c;
  long long ll;
};
#pragma pack(pop)

struct C
{
  char c;
  int i;
};

struct A a;
struct B b;
struct C c;

int main()
{
  // pointer differences (unlike sizeof) are not constant expressions, so that
  // the layout of the output of dump-c is checked when that output is compiled
  // again
  __CPROVER_assert((char *)&a.i - (char *)&a == 1, "A is packed");
  __CPROVER_assert((char *)&b.ll - (char *)&b == 2, "B has 2-byte alignment");
  __CPROVER_assert((char *)&c.i - (char *)&c == 4, "C is not packed");
  return 0;
}
