// Visual Studio ignores [[no_unique_address]] and gives an empty member
// declared [[msvc::no_unique_address]] zero size (N5008 [intro.object]/8:
// implementation-defined).
extern "C" void __CPROVER_assert(bool, const char *);
struct E
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
  char d[3];
  [[msvc::no_unique_address]] E e;
  char c;
};
struct S3
{
  [[msvc::no_unique_address]] E a;
  [[msvc::no_unique_address]] E b;
  int i;
};
int main()
{
  __CPROVER_assert(sizeof(S1) == 5, "ignored by Visual Studio");
  __CPROVER_assert(sizeof(S2) == 4, "msvc::no_unique_address");
  __CPROVER_assert(sizeof(S3) == 4, "two members");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
