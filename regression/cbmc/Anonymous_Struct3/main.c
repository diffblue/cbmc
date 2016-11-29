#include <assert.h>

// The member without name is a Visual Studio feature
// https://msdn.microsoft.com/en-us/library/z2cx9y4f.aspx
typedef union my_U {
  struct my_S {
    unsigned      : 1;
    unsigned f1   : 1;
  };
  char raw;
} fields_t;

fields_t x;

int main()
{
  unsigned word=1;

  x.f1 = 1;

  if(*(char *)&word==1)
    assert(x.raw==2); // little endian
  else
    assert(x.raw==64); // big endian
}
