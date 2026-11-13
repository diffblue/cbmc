extern "C" void __CPROVER_assert(bool, const char *);

// N5008 [dcl.enum]/7: without an enum-base, the underlying type of an
// unscoped enumeration is an implementation-defined integral type that can
// represent all enumerator values; g++ and clang++ use unsigned int when no
// enumerator is negative.  [conv.prom]/3: such an enumeration promotes to
// the first of int, unsigned int, long, ... that represents all enumerator
// values.
enum F
{
  X,
  Y
};
enum G
{
  Z = -1
};
enum Big
{
  BIG = 0x80000000u
};
enum Huge
{
  H = 0x100000000LL
};
enum Ref
{
  R0 = 3,
  R1 = R0 + 1
};
#ifndef __clang__
// GCC's mode attribute (clang ignores it on enumerations)
enum M
{
  P,
  Q
} __attribute__((__mode__(__byte__)));
#endif

static_assert(sizeof(F) == 4, "int-sized");
static_assert(sizeof(Huge) == 8, "long-sized");
static_assert(!((F)-1 > 0), "promotes to int");
static_assert((G)-1 < 0, "signed");
#ifndef __clang__
static_assert(sizeof(M) == 1, "mode(byte)");
static_assert((M)255 == 255, "mode(byte) is unsigned");

// an array whose size is a value of the enumeration
int a[(M)255];
#endif

int g(int)
{
  return 1;
}
int g(unsigned)
{
  return 2;
}
int g(long)
{
  return 3;
}

struct T
{
  F b : 1;
};

int main()
{
  __CPROVER_assert(g(X) == 1, "promotes to int");
  __CPROVER_assert(g(BIG) == 2, "promotes to unsigned int");
  __CPROVER_assert(g(H) == 3, "promotes to long");
  __CPROVER_assert(R1 == 4, "enumerator referring to an enumerator");
#ifndef __clang__
  __CPROVER_assert(sizeof(a) == 255 * sizeof(int), "array size");
#else
  __CPROVER_assert(true, "array size");
#endif
  T t;
  t.b = Y;
  __CPROVER_assert(t.b == Y, "unsigned one-bit bit-field");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
