#define STATIC_ASSERT(condition) \
  int some_array[(condition) ? 1 : -1];  

#ifdef __GNUC__

typedef unsigned char uchar;

uchar int8 __attribute__ ((__mode__ (__QI__))),
      int16 __attribute__ ((__mode__ (__HI__))),
      int32 __attribute__ ((__mode__ (__SI__))),
      int64 __attribute__ ((__mode__ (__DI__)));

STATIC_ASSERT(sizeof(int8)==1);
STATIC_ASSERT(sizeof(int16)==2);
STATIC_ASSERT(sizeof(int32)==4);
STATIC_ASSERT(sizeof(int64)==8);

uchar v1 __attribute__ ((vector_size (1))),
      v2 __attribute__ ((vector_size (2))),
      v4 __attribute__ ((vector_size (4)));

STATIC_ASSERT(sizeof(v1)==1);
STATIC_ASSERT(sizeof(v2)==2);
STATIC_ASSERT(sizeof(v4)==4);

#endif

int main()
{
}
