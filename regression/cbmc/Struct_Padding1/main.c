#include <assert.h>

#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1]

struct my_struct1
{
  int i;
  char ch;
  
  struct
  {
    // this gets padded
    int j;
  };
  
  // Bit-fields do not get padded in between,
  // but fill up an integer!
  unsigned bf1:1;
  unsigned bf2:28;
} xx1 =
{
  1, 2, { .j=3 }
};

struct my_struct2
{
  int i;
  char ch[4];
  
  // no padding needed
  int j;

  char ch2;
  // there may be end-padding!
} xx2;

STATIC_ASSERT(sizeof(xx1)==4+1+3+4+4);
STATIC_ASSERT(sizeof(xx2)==4+4+4+4);

int main()
{
  assert(xx1.i==1);
  assert(xx1.ch==2);
  assert(xx1.j==3);
  
  // let's probe the padding
  char *p=&xx1.ch;
  assert(p[0]==2);
  assert(p[1]==0);
  assert(p[2]==0);
  assert(p[3]==0);
}
