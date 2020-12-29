#include <assert.h>

struct S
{
  union U {
    int x;
    int y;
  } u;
  int z;
} s = {1, 2};

union B {
  unsigned char b : 1;
  unsigned char c;
};

union C {
  char c;
  int i;
};

union A {
  struct
  {
    char c;
    char p[3];
  };
  int i;
} x = {1};

int main()
{
  // Make sure elements of initializer lists are assigned to the right members
  // (in particular, `2` is not to be assigned to the second component of the
  // union, but has to be assigned to the second member of the struct).
  assert(s.u.x == 1);
  assert(s.z == 2);
  assert(x.p[0] == 0);

  // The C standard (6.2.6.1 (7)) states: "When a value is stored in a member of
  // an object of union type, the bytes of the object representation that do not
  // correspond to that member but do correspond to other members take
  // unspecified values." Appendix J.1 Unspecified behavior refers back to this:
  // "When a value is stored in a member of an object of union type, the bytes
  // of the object representation that do not correspond to that member but do
  // correspond to other members take unspecified values."
  //
  // GCC, Clang, Visual Studio (and possibly others) choose to maintain the
  // values of any bits not being assigned to. This includes bit fields, as the
  // following examples demonstrate.
  union B ub = {.c = 0xFF};
  ub.b = 0;
  assert(ub.c == 0xFE);

  union C uc = {.i = 0xFFFFFFFF};
  uc.c = 0;
  assert(uc.i == 0xFFFFFF00);

  union A ua = {.i = 0xFFFFFFFF};
  ua.c = 0;
  assert(ua.i == 0xFFFFFF00);
}
