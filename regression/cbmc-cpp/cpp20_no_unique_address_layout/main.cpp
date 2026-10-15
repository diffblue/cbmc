// N5008 [dcl.attr.nouniqueaddr]/2, [intro.object]/9: a non-static data
// member with [[no_unique_address]] of an empty class type need not have
// a distinct address; g++ and clang++ (Itanium C++ ABI) give it none, so
// sizeof(S) == sizeof(int).  The front end ignores the attribute and lays
// out the empty member as a byte, so sizeof(S) is 8.
extern "C" void __CPROVER_assert(bool, const char *);
struct E
{
};
struct S
{
  [[no_unique_address]] E e;
  int x;
};
int main()
{
  __CPROVER_assert(sizeof(S) == sizeof(int), "no_unique_address");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
