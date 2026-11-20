extern "C" void __CPROVER_assert(bool, const char *);

struct pair
{
  int first;
  struct
  {
    int second;
  } inner;
};

// defined in other.c ([dcl.link]/10: linkage to C is implementation-defined;
// GCC, Clang and MSVC pass a struct by value with the same layout in C)
extern "C" int sum(pair p);

int main()
{
  pair p;
  p.first = 1;
  p.inner.second = 2;
  __CPROVER_assert(sum(p) == 3, "sum");
  __CPROVER_assert(sum(p) == 4, "WRONG (must FAIL)");
  return 0;
}
