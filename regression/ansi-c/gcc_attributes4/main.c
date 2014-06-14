#define STATIC_ASSERT(condition) \
  int some_array[(condition) ? 1 : -1];  

typedef unsigned char uchar;

uchar int8 __attribute__ ((__mode__ (__QI__))),
      int16 __attribute__ ((__mode__ (__HI__))),
      int32 __attribute__ ((__mode__ (__SI__))),
      int64 __attribute__ ((__mode__ (__DI__)));

STATIC_ASSERT(sizeof(int8)==1);
STATIC_ASSERT(sizeof(int16)==2);
STATIC_ASSERT(sizeof(int32)==4);
STATIC_ASSERT(sizeof(int64)==8);

int main()
{
}
