#include <string.h>

union payload
{
  struct
  {
    char flags;
    long items[2];
  } list;
  short code;
};

struct message
{
  int id;
  union payload body;
};

union nested
{
  union
  {
    int word;
    char bytes[4];
  } inner;
  short half;
};

int main()
{
  // uninitialised objects containing unions
  union payload p;
  struct message original;
  union nested n;

  // the bytes of a union agree with each of its members
  unsigned char *bytes = (unsigned char *)&p;
  __CPROVER_assert(bytes[0] == (unsigned char)p.code, "first byte");
  __CPROVER_assert((char)bytes[0] == p.list.flags, "first byte of struct");
  __CPROVER_assert(
    bytes[8] == (unsigned char)p.list.items[0], "byte of array element");

  // and so do the members among themselves
  __CPROVER_assert((char)p.code == p.list.flags, "overlapping members");
  __CPROVER_assert((short)n.inner.word == n.half, "nested union, outer");
  __CPROVER_assert(n.inner.bytes[1] == (char)(n.half >> 8), "nested union");

  // a copy of the bytes of an object containing a union has the same members
  struct message copy;
  memcpy(&copy, &original, sizeof(struct message));
  __CPROVER_assert(copy.id == original.id, "id copied");
  __CPROVER_assert(
    copy.body.list.items[1] == original.body.list.items[1], "items copied");
  __CPROVER_assert(copy.body.code == original.body.code, "code copied");

  // the values remain nondeterministic
  __CPROVER_assert(original.body.list.items[1] == 0, "nondeterministic");

  return 0;
}
