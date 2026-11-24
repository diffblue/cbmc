#include <assert.h>
#include <string.h>

union bytes_or_half
{
  unsigned char b[8];
  unsigned short h;
};

// the short member is as wide as the union
union rep
{
  struct
  {
    char *data;
    unsigned long size;
  } l;
  struct
  {
    char data[15];
    unsigned char size;
  } s;
};

// the short member is narrower than the union
union wide_rep
{
  struct
  {
    char *data;
    unsigned long size;
    unsigned long cap;
  } l;
  struct
  {
    char data[15];
    unsigned char size;
  } s;
};

int main()
{
  // a member keeps the bytes written to it when other bytes are written
  union rep r;
  r.s.size = 4;
  memmove(r.s.data, "abc", 3);
  unsigned n = r.s.size;
  unsigned k = 0;
  for(; n != 0; --n)
    ++k;
  assert(k == 4);
  assert(r.s.data[1] == 'b');

  union wide_rep w;
  w.s.size = 3;
  memmove(w.s.data, "xy", 2);
  n = w.s.size;
  for(; n != 0; --n)
    ++k;
  assert(k == 7);
  assert(w.s.data[1] == 'y');

  // a write of some bytes whose value reads other bytes of the union
  union bytes_or_half u;
  u.h = 0x0102;
  u.b[4] = 7;
  u.b[5] = 9;
  *(unsigned short *)&u.b[1] = *(unsigned short *)&u.b[4];
  assert(u.h == 0x0702);
  assert(u.b[2] == 9);

  assert(0);
  return 0;
}
