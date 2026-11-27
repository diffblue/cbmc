extern "C" void __CPROVER_assert(bool, const char *);

// GNU extension (as in C11 6.7.2.1/13): a designator names a member of an
// anonymous struct or union
struct bits
{
  unsigned char op;
  struct
  {
    unsigned char lo : 4;
    unsigned char hi : 4;
  };
  unsigned char z;
};

struct variant
{
  int kind;
  union
  {
    int i;
    float f;
  };
};

int main()
{
  bits b;
  b = {.op = 1, .lo = 2, .z = 3};
  __CPROVER_assert(
    b.op == 1 && b.lo == 2 && b.hi == 0 && b.z == 3, "anonymous struct");

  variant v = {.kind = 1, .f = 2.5f};
  __CPROVER_assert(v.kind == 1 && v.f == 2.5f, "anonymous union");

  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
