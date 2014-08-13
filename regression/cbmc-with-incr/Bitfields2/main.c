
#if defined(_WIN32) && !defined(__CYGWIN__)
typedef signed __int64 int64_t;
typedef unsigned __int64 uint64_t;
typedef signed int int32_t;
typedef unsigned int uint32_t;
typedef signed short int int16_t;
#else
#include <inttypes.h>
#endif

#include <assert.h>

union U {
  signed : 0;
};

#pragma pack(push)
#pragma pack(1)
struct S0 {
   uint64_t  f0;
   int32_t  f1;
   int64_t  f2;
   uint32_t  f3;
   // skipped over during initialization
   signed : 0; 
   volatile int16_t  f4;
   volatile uint32_t  f5;
   int32_t  f6;
   int32_t  f7;
   uint32_t  f8;
};
#pragma pack(pop)

unsigned foo(union U u, struct S0 s)
{
  return s.f8;
}

int main()
{
  struct S0 main_s = { 0, 1, 2, 3, 4, 5, 6, 7, 8 };
  union U main_u;

  assert(8==foo(main_u, main_s));

  return 0;
}

