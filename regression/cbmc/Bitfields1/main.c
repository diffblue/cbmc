#include <assert.h>

typedef int INT;

typedef enum _INTEL_CACHE_TYPE {
    IntelCacheNull,
    IntelCacheTrace=10
} INTEL_CACHE_TYPE;

struct bft {
  unsigned long int a : 3;
  unsigned int b:1;
  signed int c:2;
  _Bool d : 1;

  // an anonymous bitfield
  signed int :2;

  // with typedef
  INT x:1;

  // made of sizeof
  unsigned int abc : sizeof(int) * 8;

  // enums are integers!
  INTEL_CACHE_TYPE Type : 5;

  // and good as field sizes
  INTEL_CACHE_TYPE Field2 : IntelCacheTrace;
};

int main() {
  struct bft bf;

  assert(bf.a<=7);
  assert(bf.b<=1);
  assert(bf.c<=1);

  bf.a&=0;
  assert(bf.a==0);

  bf.a+=9;
  assert(bf.a==1);

  bf.a<<=1;
  assert(bf.a==2);

  bf.a>>=1;
  assert(bf.a==1);

  bf.d=2;
  assert(bf.d==1);

  // assignments have the underlying type
  assert(sizeof(bf.d=1)==sizeof(_Bool));
  assert(sizeof(bf.a += 1) == sizeof(unsigned long));

  bf.Type=IntelCacheTrace;

  // promotion rules apply, and thus, bf.a is signed,
  // but bf.abc is unsigned
  bf.a = 0;
  assert(bf.a - 1 < 0);
  bf.abc = 0;
  assert(bf.abc - 1 >= 0);
}
