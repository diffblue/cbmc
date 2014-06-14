#include <inttypes.h>
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
  struct S0 s = { 0, 1, 2, 3, 4, 5, 6, 7, 8 };
  union U u;

  assert(8==foo(u, s));

  return 0;
}

