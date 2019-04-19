#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

#ifdef _WIN32
typedef unsigned __int64 uint64_t;
typedef unsigned int uint32_t;
typedef unsigned short uint16_t;
typedef unsigned char uint8_t;
#define __extension__
#else
#include <inttypes.h>
#endif

#pragma pack(1)
typedef union RTFLOAT80U
{
    __extension__ struct
    {
        uint64_t u64Mantissa;
        __extension__ uint16_t uExponent : 15;
        __extension__ uint16_t fSign : 1;
    } s;

    uint64_t au64[1];
    uint32_t au32[2];
    uint16_t au16[5];
    uint8_t au8[10];
} RTFLOAT80U;
#pragma pack()

STATIC_ASSERT(sizeof(RTFLOAT80U)==10);

struct S
{
  char c;
  int i;
};

STATIC_ASSERT(sizeof(struct S)==2*sizeof(int));

#include <stdio.h>

int main()
{
  printf("RTFLOAT80U: %lu\n", sizeof(RTFLOAT80U));
  printf("struct S: %lu\n", sizeof(struct S));
  return 0;
}
