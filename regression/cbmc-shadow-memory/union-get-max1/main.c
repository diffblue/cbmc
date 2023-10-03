#include <assert.h>
#include <stdlib.h>

union UNIONNAME
{
  int x1;
  struct
  {
    char y1;
    // char padding;
    short y2;
    short y3;
  } x2;
  char x3[3];
};

// [Shadow] Memory layout (PP is padding)
// u    = [ byte1  byte2  byte3  byte4  byte5  byte6 ]
// u.x1 = [    X1     X1     X1     X1     PP     PP ]
// u.x2 = [    Y1     PP     Y2     Y2     Y3     Y3 ]
// u.x3 = [ X3[0]  X3[1]  X3[2]     PP     PP     PP ]

int main()
{
  __CPROVER_field_decl_local("field2", (__CPROVER_bitvector[6])0);

  union UNIONNAME u;
  // u = [0x00 0x00 0x00 0x00 0x00 0x00]

  assert(__CPROVER_get_field(&u, "field2") == 0);
  assert(__CPROVER_get_field(&(u.x1), "field2") == 0);
  assert(__CPROVER_get_field(&(u.x2), "field2") == 0);
  assert(__CPROVER_get_field(&(u.x2.y1), "field2") == 0);
  assert(__CPROVER_get_field(&(u.x2.y2), "field2") == 0);
  assert(__CPROVER_get_field(&(u.x2.y3), "field2") == 0);
  // Not allowed: assert(__CPROVER_get_field(u.x3, "field2") == 0);
  assert(__CPROVER_get_field(&(u.x3[0]), "field2") == 0);
  assert(__CPROVER_get_field(&(u.x3[1]), "field2") == 0);
  assert(__CPROVER_get_field(&(u.x3[2]), "field2") == 0);

  __CPROVER_set_field(&(u.x1), "field2", 1);
  // u = [0x02 0x01 0x01 0x01 0x00 0x00]
  assert(__CPROVER_get_field(&u, "field2") == 1);
  assert(__CPROVER_get_field(&(u.x1), "field2") == 1);
  assert(__CPROVER_get_field(&(u.x2), "field2") == 1);
  assert(__CPROVER_get_field(&(u.x2.y1), "field2") == 1);
  assert(__CPROVER_get_field(&(u.x2.y2), "field2") == 1);
  assert(__CPROVER_get_field(&(u.x2.y3), "field2") == 0);
  // Not allowed: assert(__CPROVER_get_field(u.x3, "field2") == 1);
  assert(__CPROVER_get_field(&(u.x3[0]), "field2") == 1);
  assert(__CPROVER_get_field(&(u.x3[1]), "field2") == 1);
  assert(__CPROVER_get_field(&(u.x3[2]), "field2") == 1);

  __CPROVER_set_field(&(u.x2.y1), "field2", 2);
  // u = [0x02 0x01 0x01 0x01 0x00 0x00]
  assert(__CPROVER_get_field(&u, "field2") == 2);
  assert(__CPROVER_get_field(&(u.x1), "field2") == 2);
  assert(__CPROVER_get_field(&(u.x2), "field2") == 2);
  assert(__CPROVER_get_field(&(u.x2.y1), "field2") == 2);
  assert(__CPROVER_get_field(&(u.x2.y2), "field2") == 1);
  assert(__CPROVER_get_field(&(u.x2.y3), "field2") == 0);
  // Not allowed: assert(__CPROVER_get_field(u.x3, "field2") == 2);
  assert(__CPROVER_get_field(&(u.x3[0]), "field2") == 2);
  assert(__CPROVER_get_field(&(u.x3[1]), "field2") == 1);
  assert(__CPROVER_get_field(&(u.x3[2]), "field2") == 1);

  __CPROVER_set_field(&(u.x2.y2), "field2", 3);
  // u = [0x02 0x01 0x03 0x03 0x00 0x00]
  assert(__CPROVER_get_field(&u, "field2") == 3);
  assert(__CPROVER_get_field(&(u.x1), "field2") == 3);
  assert(__CPROVER_get_field(&(u.x2), "field2") == 3);
  assert(__CPROVER_get_field(&(u.x2.y1), "field2") == 2);
  assert(__CPROVER_get_field(&(u.x2.y2), "field2") == 3);
  assert(__CPROVER_get_field(&(u.x2.y3), "field2") == 0);
  // Not allowed: assert(__CPROVER_get_field(u.x3, "field2") == 3);
  assert(__CPROVER_get_field(&(u.x3[0]), "field2") == 2);
  assert(__CPROVER_get_field(&(u.x3[1]), "field2") == 1);
  assert(__CPROVER_get_field(&(u.x3[2]), "field2") == 3);

  __CPROVER_set_field(&(u.x2.y3), "field2", 4);
  // u = [0x02 0x01 0x03 0x03 0x04 0x04]
  assert(__CPROVER_get_field(&u, "field2") == 4);
  assert(__CPROVER_get_field(&(u.x1), "field2") == 3);
  assert(__CPROVER_get_field(&(u.x2), "field2") == 4);
  assert(__CPROVER_get_field(&(u.x2.y1), "field2") == 2);
  assert(__CPROVER_get_field(&(u.x2.y2), "field2") == 3);
  assert(__CPROVER_get_field(&(u.x2.y3), "field2") == 4);
  // Not allowed: assert(__CPROVER_get_field(u.x3, "field2") == 3);
  assert(__CPROVER_get_field(&(u.x3[0]), "field2") == 2);
  assert(__CPROVER_get_field(&(u.x3[1]), "field2") == 1);
  assert(__CPROVER_get_field(&(u.x3[2]), "field2") == 3);

  __CPROVER_set_field(&(u.x3[1]), "field2", 5);
  // u = [0x02 0x05 0x03 0x03 0x04 0x04]
  assert(__CPROVER_get_field(&u, "field2") == 5);
  assert(__CPROVER_get_field(&(u.x1), "field2") == 5);
  assert(__CPROVER_get_field(&(u.x2), "field2") == 5);
  assert(__CPROVER_get_field(&(u.x2.y1), "field2") == 2);
  assert(__CPROVER_get_field(&(u.x2.y2), "field2") == 3);
  assert(__CPROVER_get_field(&(u.x2.y3), "field2") == 4);
  // Not allowed: assert(__CPROVER_get_field(u.x3, "field2") == 5);
  assert(__CPROVER_get_field(&(u.x3[0]), "field2") == 2);
  assert(__CPROVER_get_field(&(u.x3[1]), "field2") == 5);
  assert(__CPROVER_get_field(&(u.x3[2]), "field2") == 3);

  // Failing assertion added to get trace and to test what the inner
  // representation is.
  assert(__CPROVER_get_field(&u, "field2") == 42);
}
