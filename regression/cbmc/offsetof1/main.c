#include <assert.h>

struct S
{
  int i;
  char ch;
  int j; // this gets aligned
  
  struct Ssub
  {
    int x, y;
  } sub, array[100];
};

struct S s;

int main(void)
{
  // this is a GCC extension
  #ifdef __GNUC__
  assert(__builtin_offsetof(struct S, i)==0);
  assert(__builtin_offsetof(struct S, ch)==4);
  assert(__builtin_offsetof(struct S, j)==8); // padding!
  assert(__builtin_offsetof(struct S, sub.x)==12);
  assert(__builtin_offsetof(struct S, sub.y)==16);
  assert(__builtin_offsetof(struct S, array)==16+4);
  assert(__builtin_offsetof(struct S, array[1])==16+12);
  assert(__builtin_offsetof(struct S, array[1].y)==16+12+4);
  #endif

  // The following is the 'official' Microsoft way
  // of getting struct offsets. No dereferencing
  // happens here, just address arithmetic.
  assert((long int)&((struct S *)0)->i==0);
  assert((long int)&((struct S *)0)->ch==4);
  assert((long int)&((struct S *)0)->j==8); // padding!
  assert((long int)&((struct S *)0)->sub.x==12);
  assert((long int)&((struct S *)0)->sub.y==16);
  assert((long int)&((struct S *)0)->array==16+4);
  assert((long int)&((struct S *)0)->array[1]==16+12);
  assert((long int)&((struct S *)0)->array[1].y==16+12+4);
  
  // these are _constants_!

  #ifdef __GNUC__  
  enum { E1 = __builtin_offsetof(struct S, ch) };
  #endif

  enum { E2 = (long int)&((struct S *)0)->ch };
  enum { E3 = (long int)&((struct S *)0)->array[1].y };

}
