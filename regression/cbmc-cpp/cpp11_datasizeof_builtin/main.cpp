extern "C" void __CPROVER_assert(bool, const char *);
// Clang's __datasizeof(T): the Itanium C++ ABI's dsize(T), the size of an
// object without its tail padding (libc++ 18's __libcpp_datasizeof).  Every
// static_assert below holds with clang++-18.
struct E
{
};
struct A
{
  int i;
  char c;
};
// non-POD: a user-provided constructor
struct NP
{
  int i;
  char c;
  NP()
  {
  }
};
// non-POD: a non-public data member
struct NP2
{
  int i;
  char c;

private:
  int j;
};
struct NE
{
  NE()
  {
  }
};
struct C
{
  long l;
  char c;
  short s;
};
struct NC
{
  long l;
  char c;
  short s;
  NC()
  {
  }
};
struct Ref
{
  int &r;
};
// ABI 2.4-II.1: a POD for the purpose of layout has dsize == sizeof
static_assert(__datasizeof(E) == 1, "empty POD");
static_assert(__datasizeof(A) == 8, "POD: sizeof");
static_assert(
  __datasizeof(C) == 2 * sizeof(long),
  "POD with interior and tail padding");
static_assert(__datasizeof(Ref) == sizeof(void *), "");
// otherwise dsize is the end of the last non-static data member
static_assert(__datasizeof(NP) == 5, "non-POD: without the tail padding");
static_assert(__datasizeof(NP2) == 12, "non-POD without tail padding");
static_assert(__datasizeof(NE) == 0, "non-POD empty class");
static_assert(__datasizeof(NC) == sizeof(long) + 4, "");
// non-class types: sizeof
static_assert(__datasizeof(int) == 4, "");
static_assert(__datasizeof(char[7]) == 7, "");
static_assert(__datasizeof(NP[2]) == 16, "array of non-POD: sizeof");
int main()
{
  __CPROVER_assert(__datasizeof(NP) == 5, "dsize of a non-POD class");
  __CPROVER_assert(__datasizeof(A) == 8, "dsize of a POD class");
  __CPROVER_assert(__datasizeof(NP) == 8, "WRONG (must FAIL)");
}
