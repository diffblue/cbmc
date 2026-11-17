#include <assert.h>
#include <string.h>
// libc++'s alternate std::string layout: the short size is a 7-bit bit field
// in the last byte of a union whose other member holds pointers and sizes
struct short_rep
{
  char data[23];
  unsigned char size : 7;
  unsigned char is_long : 1;
};
struct long_rep
{
  char *data;
  unsigned long size;
  unsigned long cap;
};
union rep
{
  struct long_rep l;
  struct short_rep s;
};
int main()
{
  union rep r;
  r.s.size = 4;
  r.s.is_long = 0;
  memmove(r.s.data, "loop", 4);
  r.s.data[4] = 0;
  // writes of other bytes leave the bit field as written
  unsigned n = r.s.size;
  unsigned k = 0;
  for(; n != 0; --n)
    ++k;
  assert(k == 4);
  assert(r.s.is_long == 0);
  return 0;
}
